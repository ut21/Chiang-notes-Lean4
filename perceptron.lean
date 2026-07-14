import Mathlib

-- Defintion 2.1
def perceptron {d} (x : Fin d → ℝ) (w : Fin d → ℝ) (b : ℝ) := (∑ i, w i * x i) + b
def true_perceptron {d} (x : Fin d → ℝ) (w : Fin d → ℝ) (b : ℝ) := perceptron x w b > 0
def false_perceptron {d} (x : Fin d → ℝ) (w : Fin d → ℝ) (b : ℝ) := perceptron x w b ≤ 0

-- Example 2.2
def two_way_and_perceptron (x : Fin 2 → ℝ) := perceptron x (1 : Fin 2 → ℝ) (-1)
def two_way_or_perceptron (x : Fin 2 → ℝ) := perceptron x (1 : Fin 2 → ℝ) (1)
def one_way_not_perceptron (x : Fin 1 → ℝ) := perceptron x (-1 : Fin 1 → ℝ) (0)

-- Example 2.3
def d_way_and_perceptron {d} (x : Fin d → ℝ):= perceptron x (1 : Fin d → ℝ) (-d+1)
def d_way_or_perceptron {d} (x : Fin d → ℝ):= perceptron x (1 : Fin d → ℝ) (d+1)

-- Theorem 2.4 / Example 2.5
theorem no_perceptron_for_2_way_xor :
  ¬ ∃ (w : Fin 2 → ℝ) (b : ℝ),
  false_perceptron (![0,0]) w b ∧
  true_perceptron (![0,1]) w b ∧
  true_perceptron (![1,0]) w b ∧
  false_perceptron (![1,1]) w b := by
  intro h
  obtain ⟨w, b, h00, h01, h10, h11⟩ := h
  simp only [false_perceptron, true_perceptron, perceptron] at h00 h01 h10 h11
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01 h10 h11
  linarith

-- Definition 2.6
structure Sample (d : ℕ) where
  x : Fin d → ℝ
  y : ℝ
  hy : y = 1 ∨ y = -1
abbrev Dataset (d n : ℕ) := Fin n → Sample D

def dot {d} (x1 : Fin d → ℝ) (x2 : Fin d → ℝ) : ℝ := dotProduct x1 x2

def linearly_separable {d n} (D : Dataset d n) (γ : ℝ) :=
  γ > 0 ∧ ∃ (w : Fin d → ℝ), dot w w = 1 ∧ ∀ (i : Fin n), (dot ((D i).x) (w)) * (D i).y ≥ γ

def is_mistake {d} (s : Sample d) (w : Fin d → ℝ) : Prop :=
  s.y * dot s.x w ≤ 0

def update {d} (w_tmin1 : Fin d → ℝ) (s_t : Sample d) :=
  w_tmin1 + (s_t.y • s_t.x)

def weights_after_k_updates {d} (k : ℕ) (mistakes : Fin k → Sample d) : Fin d → ℝ :=
  match k with
  | 0 => (0 : Fin d → ℝ)
  | k+1 => update (weights_after_k_updates k (fun i => mistakes i.castSucc)) (mistakes (Fin.last k))

lemma cauchy_schwarz {d} (v w : Fin d → ℝ) : (dot v w)^2 ≤ dot v v * dot w w := by
  simpa [dot, dotProduct, sq, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) v w

lemma y_sq_eq_one {d} (s : Sample d) : s.y ^ 2 = 1 := by
  rcases s.hy with h | h <;> (rw [h]; norm_num)

lemma novikoff_lower {d n} {γ : ℝ}
    (D : Dataset d n)
    (w_star : Fin d → ℝ)
    (hw_star_sep : ∀ (i : Fin n), dot (D i).x w_star * (D i).y ≥ γ)
    (k : ℕ) :
    ∀ (mistakes : Fin k → Sample d)
      (_hFromD : ∀ t : Fin k, ∃ i : Fin n, mistakes t = D i),
      dot w_star (weights_after_k_updates k mistakes) ≥ (k : ℝ) * γ := by
  induction k with
  | zero =>
    intros mistakes _
    change dotProduct w_star (0 : Fin d → ℝ) ≥ _
    simp
  | succ k ih =>
    intros mistakes hFromD
    let mistakes' : Fin k → Sample d := fun i => mistakes i.castSucc
    have hFromD' : ∀ t : Fin k, ∃ i : Fin n, mistakes' t = D i :=
      fun t => hFromD t.castSucc
    have lb := ih mistakes' hFromD'
    set W_k := weights_after_k_updates k (fun i => mistakes i.castSucc)
    set x_last := (mistakes (Fin.last k)).x
    set y_last := (mistakes (Fin.last k)).y
    change dot w_star (W_k + y_last • x_last) ≥ _
    have h_sep_last : y_last * dot w_star x_last ≥ γ := by
      obtain ⟨i, hi⟩ := hFromD (Fin.last k)
      have h := hw_star_sep i
      have hswap : dot (D i).x w_star * (D i).y = (D i).y * dot w_star (D i).x := by
        rw [show dot (D i).x w_star = dot w_star (D i).x from dotProduct_comm _ _]
        ring
      rw [hswap] at h
      change (mistakes (Fin.last k)).y * dot w_star (mistakes (Fin.last k)).x ≥ γ
      rw [hi]
      exact h
    rw [show dot w_star (W_k + y_last • x_last)
            = dot w_star W_k + y_last * dot w_star x_last from by
          simp only [dot, dotProduct_add, dotProduct_smul, smul_eq_mul]]
    have hkg : (((k + 1 : ℕ) : ℝ)) * γ = (k : ℝ) * γ + γ := by push_cast; ring
    rw [hkg]
    linarith [lb, h_sep_last]

lemma novikoff_upper {d n} {R : ℝ}
    (D : Dataset d n)
    (hR : ∀ i : Fin n, dot (D i).x (D i).x ≤ R^2)
    (k : ℕ) :
    ∀ (mistakes : Fin k → Sample d)
      (_hFromD : ∀ t : Fin k, ∃ i : Fin n, mistakes t = D i)
      (_hmistakes : ∀ t : Fin k, is_mistake (mistakes t)
          (weights_after_k_updates t.val
            (fun i => mistakes (Fin.castLE (Nat.le_of_lt t.isLt) i)))),
      dot (weights_after_k_updates k mistakes)
        (weights_after_k_updates k mistakes) ≤ (k : ℝ) * R^2 := by
  induction k with
  | zero =>
    intros mistakes _ _
    change dotProduct (0 : Fin d → ℝ) 0 ≤ _
    simp
  | succ k ih =>
    intros mistakes hFromD hmistakes
    let mistakes' : Fin k → Sample d := fun i => mistakes i.castSucc
    have hFromD' : ∀ t : Fin k, ∃ i : Fin n, mistakes' t = D i :=
      fun t => hFromD t.castSucc
    have hmistakes' : ∀ t : Fin k, is_mistake (mistakes' t)
        (weights_after_k_updates t.val
          (fun i => mistakes' (Fin.castLE (Nat.le_of_lt t.isLt) i))) := by
      intro t
      have h1 := hmistakes t.castSucc
      have hfun : (fun i : Fin t.val => mistakes' (Fin.castLE (Nat.le_of_lt t.isLt) i)) =
                  (fun i : Fin t.castSucc.val =>
                    mistakes (Fin.castLE (Nat.le_of_lt t.castSucc.isLt) i)) := by
        funext i
        change mistakes _ = mistakes _
        congr 1
      change is_mistake (mistakes t.castSucc) _
      rw [hfun]
      exact h1
    have ub := ih mistakes' hFromD' hmistakes'
    set W_k := weights_after_k_updates k (fun i => mistakes i.castSucc)
    set x_last := (mistakes (Fin.last k)).x
    set y_last := (mistakes (Fin.last k)).y
    change dot (W_k + y_last • x_last) (W_k + y_last • x_last) ≤ _
    have h_mistake_last : y_last * dot x_last W_k ≤ 0 := by
      have h1 := hmistakes (Fin.last k)
      rw [is_mistake] at h1
      have hfun : (fun i : Fin (Fin.last k).val =>
                     mistakes (Fin.castLE (Nat.le_of_lt (Fin.last k).isLt) i))
                = (fun i : Fin k => mistakes i.castSucc) := by
        funext i
        congr 1
      rw [hfun] at h1
      change (mistakes (Fin.last k)).y * dot (mistakes (Fin.last k)).x W_k ≤ 0
      exact h1
    have h_x_R : dot x_last x_last ≤ R^2 := by
      obtain ⟨i, hi⟩ := hFromD (Fin.last k)
      change dot (mistakes (Fin.last k)).x (mistakes (Fin.last k)).x ≤ R^2
      rw [hi]
      exact hR i
    have hy_sq : y_last ^ 2 = 1 := y_sq_eq_one (mistakes (Fin.last k))
    rw [show dot (W_k + y_last • x_last) (W_k + y_last • x_last)
           = dot W_k W_k + 2 * (y_last * dot W_k x_last)
             + y_last ^ 2 * dot x_last x_last from by
          simp only [dot, add_dotProduct, dotProduct_add,
            smul_dotProduct, dotProduct_smul, smul_eq_mul,
            dotProduct_comm x_last W_k]
          ring]
    rw [hy_sq, one_mul]
    have h_dot_swap : y_last * dot W_k x_last = y_last * dot x_last W_k := by
      rw [show dot W_k x_last = dot x_last W_k from dotProduct_comm _ _]
    have h_kr : (((k + 1 : ℕ) : ℝ)) * R^2 = (k : ℝ) * R^2 + R^2 := by push_cast; ring
    rw [h_kr]
    linarith [ub, h_x_R, h_mistake_last, h_dot_swap]

theorem novikoff_62 {d n} {γ : ℝ}
    (D : Dataset d n)
    (hD : linearly_separable D γ)
    (R : ℝ)
    (hR : ∀ i : Fin n, dot (D i).x (D i).x ≤ R^2)
    (k : ℕ)
    (mistakes : Fin k → Sample d)
    (hFromD : ∀ t : Fin k, ∃ i : Fin n, mistakes t = D i)
    (hmistakes : ∀ t : Fin k, is_mistake (mistakes t)
        (weights_after_k_updates t.val
          (fun i => mistakes (Fin.castLE (Nat.le_of_lt t.isLt) i)))) :
    (k : ℝ) ≤ R^2 / γ^2 := by
  obtain ⟨hγ, w_star, hw_star_normsq, hw_star_sep⟩ := hD
  have lb := novikoff_lower D w_star hw_star_sep k mistakes hFromD
  have ub := novikoff_upper D hR k mistakes hFromD hmistakes
  have hγ_sq_pos : (0 : ℝ) < γ^2 := pow_pos hγ 2
  by_cases hk : k = 0
  · rw [hk]
    push_cast
    exact div_nonneg (sq_nonneg R) (le_of_lt hγ_sq_pos)
  · have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have h_kγ_nn : (0 : ℝ) ≤ (k : ℝ) * γ := mul_nonneg (le_of_lt hk_pos) (le_of_lt hγ)
    have h_lb_pow : ((k : ℝ) * γ)^2 ≤ (dot w_star (weights_after_k_updates k mistakes))^2 :=
      pow_le_pow_left₀ h_kγ_nn lb 2
    have h_cs := cauchy_schwarz w_star (weights_after_k_updates k mistakes)
    rw [hw_star_normsq, one_mul] at h_cs
    have h_combined : ((k : ℝ) * γ)^2 ≤ (k : ℝ) * R^2 :=
      le_trans h_lb_pow (le_trans h_cs ub)
    have h_expand : ((k : ℝ) * γ)^2 = (k : ℝ) * ((k : ℝ) * γ^2) := by ring
    rw [h_expand] at h_combined
    have h_kγsq_le : (k : ℝ) * γ^2 ≤ R^2 :=
      (mul_le_mul_iff_of_pos_left hk_pos).mp h_combined
    rw [le_div_iff₀ hγ_sq_pos]
    linarith
