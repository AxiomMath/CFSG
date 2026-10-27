module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityFamily

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFourier

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {B : Finset ι} {p : ι} {d : ι → ℤ} {J : Finset κ} {c : κ → ι → ℤ}
variable {σ : ℤ} {χ : κ → ι} {V : ι → ℤ}

namespace ParityFamily

omit [DecidableEq κ] in
theorem sq_sign (hf : ParityFamily B p d J c σ χ V) : σ ^ 2 = 1 := by
  rcases hf.sign with h | h <;> rw [h] <;> norm_num

theorem V_principal (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V) {j : κ}
    (hj : j ∈ J) : V p = -1 := by
  have h := hf.eq j hj p hc.mem
  rw [hc.principal j hj, unitVector_of_ne (Ne.symm (hf.ne j hj)), mul_zero, add_zero] at h
  exact h.symm

theorem sq_sum (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V) {j : κ}
    (hj : j ∈ J) : ∑ ψ ∈ B, V ψ ^ 2 + 4 * σ * V (χ j) = 4 := by
  have h8 := hc.gram j hj j hj
  rw [ite_eq_left rfl] at h8
  have hcongr : ∑ ψ ∈ B, c j ψ * c j ψ = ∑ ψ ∈ B, (V ψ ^ 2 +
      4 * σ * (V ψ * unitVector (χ j) ψ) +
      4 * σ ^ 2 * (unitVector (χ j) ψ * unitVector (χ j) ψ)) :=
    Finset.sum_congr rfl fun ψ hψ => by rw [hf.eq j hj ψ hψ]; ring
  rw [hcongr, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_mul_unitVector (hf.mem j hj), sum_mul_unitVector (hf.mem j hj), unitVector_self,
    hf.sq_sign] at h8
  linarith

theorem lower (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V) {j₀ : κ}
    (hj₀ : j₀ ∈ J) : 1 + ∑ j ∈ J, V (χ j) ^ 2 ≤ ∑ ψ ∈ B, V ψ ^ 2 := by
  have hp : p ∉ J.image χ := by
    rw [Finset.mem_image]
    rintro ⟨j, hj, h⟩
    exact hf.ne j hj h
  have hsub : insert p (J.image χ) ⊆ B := by
    intro ψ hψ
    rw [Finset.mem_insert, Finset.mem_image] at hψ
    rcases hψ with rfl | ⟨j, hj, rfl⟩
    · exact hc.mem
    · exact hf.mem j hj
  calc 1 + ∑ j ∈ J, V (χ j) ^ 2 = ∑ ψ ∈ insert p (J.image χ), V ψ ^ 2 := by
        rw [Finset.sum_insert hp, Finset.sum_image hf.injOn, hf.V_principal hc hj₀]
        norm_num
    _ ≤ ∑ ψ ∈ B, V ψ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

theorem swap (hf : ParityFamily B p d J c σ χ V) {j₀ j₁ : κ} (hne : j₀ ≠ j₁)
    (hJ : J = {j₀, j₁}) :
    ParityFamily B p d J c (-σ) (fun j => if j = j₀ then χ j₁ else χ j₀)
      (fun ψ => V ψ + 2 * σ * unitVector (χ j₀) ψ + 2 * σ * unitVector (χ j₁) ψ) := by
  have h₀ : j₀ ∈ J := by rw [hJ]; simp
  have h₁ : j₁ ∈ J := by rw [hJ]; simp
  have hcases : ∀ j ∈ J, j ≠ j₀ → j = j₁ := by
    intro j hj hj0
    rw [hJ] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    exact hj.resolve_left hj0
  have hχne : χ j₀ ≠ χ j₁ := fun h => hne (hf.injOn h₀ h₁ h)
  refine ⟨by rcases hf.sign with h | h <;> rw [h] <;> norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj t ht h
    by_cases hj0 : j = j₀ <;> by_cases ht0 : t = j₀
    · exact hj0.trans ht0.symm
    · simp only [hj0, ht0, ↓reduceIte] at h
      exact absurd h.symm hχne
    · simp only [hj0, ht0, ↓reduceIte] at h
      exact absurd h hχne
    · exact (hcases j hj hj0).trans (hcases t ht ht0).symm
  · intro j hj
    by_cases hj0 : j = j₀
    · simpa only [hj0, ↓reduceIte] using hf.mem j₁ h₁
    · simpa only [hj0, ↓reduceIte] using hf.mem j₀ h₀
  · intro j hj
    by_cases hj0 : j = j₀
    · simpa only [hj0, ↓reduceIte] using hf.ne j₁ h₁
    · simpa only [hj0, ↓reduceIte] using hf.ne j₀ h₀
  · have hd : ∀ j ∈ J, d (if j = j₀ then χ j₁ else χ j₀) = d (χ j₀) := by
      intro j hj
      by_cases hj0 : j = j₀
      · simpa only [hj0, ↓reduceIte] using hf.deg j₁ h₁ j₀ h₀
      · simp only [hj0, ↓reduceIte]
    intro j hj t ht
    rw [hd j hj, hd t ht]
  · intro j hj ψ hψ
    by_cases hj0 : j = j₀
    · simp only [hj0, ↓reduceIte]
      rw [hf.eq j₀ h₀ ψ hψ]
      ring
    · simp only [hj0, ↓reduceIte]
      rw [hcases j hj hj0, hf.eq j₁ h₁ ψ hψ]
      ring

theorem normalize (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V)
    (hJ : 2 ≤ J.card) :
    ∃ σ' χ' V', ParityFamily B p d J c σ' χ' V' ∧
      ((∀ j ∈ J, V' (χ' j) = 0) ∨ (∀ j ∈ J, V' (χ' j) = -σ')) := by
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, ht⟩ : ∃ t, t = σ * V (χ j₀) := ⟨_, rfl⟩
  have hσ2 := hf.sq_sign
  have hval : ∀ j ∈ J, V (χ j) = σ * t := by
    intro j hj
    have h1 := hf.sq_sum hc hj
    have h2 := hf.sq_sum hc hj₀
    have h3 : σ * V (χ j) = σ * V (χ j₀) := by linarith
    have h4 : V (χ j) = V (χ j₀) := by
      rcases hf.sign with h | h <;> rw [h] at h3 <;> linarith
    rw [h4, ht, ← mul_assoc, ← sq, hσ2, one_mul]
  have hsum : ∑ j ∈ J, V (χ j) ^ 2 = J.card * t ^ 2 := by
    have hcongr : ∑ j ∈ J, V (χ j) ^ 2 = ∑ j ∈ J, t ^ 2 :=
      Finset.sum_congr rfl fun j hj => by rw [hval j hj, mul_pow, hσ2, one_mul]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have hQ : ∑ ψ ∈ B, V ψ ^ 2 = 4 - 4 * t := by
    have h := hf.sq_sum hc hj₀
    rw [ht]
    linarith
  have hbound : 1 + (J.card : ℤ) * t ^ 2 ≤ 4 - 4 * t := by
    have h := hf.lower hc hj₀
    rwa [hsum, hQ] at h
  have hk : (2 : ℤ) ≤ J.card := by exact_mod_cast hJ
  have hkt : 2 * t ^ 2 ≤ J.card * t ^ 2 := mul_le_mul_of_nonneg_right hk (sq_nonneg t)
  have ht0 : t ≤ 0 := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  have ht2 : -2 ≤ t := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  rcases (by omega : t = 0 ∨ t = -1 ∨ t = -2) with h0 | h1 | h2
  · exact ⟨σ, χ, V, hf, Or.inl fun j hj => by rw [hval j hj, h0, mul_zero]⟩
  · exact ⟨σ, χ, V, hf, Or.inr fun j hj => by rw [hval j hj, h1, mul_neg_one]⟩
  ·
    have hk2 : J.card = 2 := by
      rw [h2] at hbound
      have : (J.card : ℤ) ≤ 2 := by nlinarith
      omega
    obtain ⟨x, y, hxy, hJxy⟩ := Finset.card_eq_two.mp hk2
    refine ⟨-σ, _, _, hf.swap hxy hJxy, Or.inl fun j hj => ?_⟩
    have hx : x ∈ J := by rw [hJxy]; simp
    have hy : y ∈ J := by rw [hJxy]; simp
    have hχne : χ x ≠ χ y := fun h => hxy (hf.injOn hx hy h)
    have hVx : V (χ x) = -2 * σ := by rw [hval x hx, h2]; ring
    have hVy : V (χ y) = -2 * σ := by rw [hval y hy, h2]; ring
    by_cases hjx : j = x
    · simp only [hjx, ↓reduceIte]
      rw [hVy, unitVector_of_ne (Ne.symm hχne), unitVector_self]
      ring
    · simp only [hjx, ↓reduceIte]
      rw [hVx, unitVector_self, unitVector_of_ne hχne]
      ring

theorem descI (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V) {j₀ : κ}
    (hj₀ : j₀ ∈ J) (h0 : ∀ j ∈ J, V (χ j) = 0) :
    ∃ (α : Fin 3 → ι) (η : Fin 3 → ℤ), Function.Injective α ∧
      (∀ i, α i ∈ B ∧ α i ≠ p ∧ ∀ j ∈ J, α i ≠ χ j) ∧ (∀ i, η i = 1 ∨ η i = -1) ∧
      ∀ ψ ∈ B, V ψ = -unitVector p ψ + ∑ i, η i * unitVector (α i) ψ := by
  have hVp := hf.V_principal hc hj₀
  have hQ : ∑ ψ ∈ B, V ψ ^ 2 = 4 := by
    have h := hf.sq_sum hc hj₀
    rwa [h0 j₀ hj₀, mul_zero, add_zero] at h
  have h3 : ∑ ψ ∈ B.erase p, V ψ ^ 2 = ((3 : ℕ) : ℤ) := by
    have h := Finset.add_sum_erase B (fun ψ => V ψ ^ 2) hc.mem
    rw [hQ, hVp] at h
    push_cast
    linarith
  rcases hasCoefficientShape_of_sq_sum (by norm_num) h3 with ⟨hval, hones, htwos⟩ | ⟨h4, -⟩
  swap
  · norm_num at h4
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ := Finset.card_eq_three.mp hones
  have hmemT : ∀ ψ, ψ ∈ (B.erase p).filter (fun χ => |V χ| = 1) ↔
      ψ ∈ B ∧ ψ ≠ p ∧ |V ψ| = 1 := by
    intro ψ
    rw [Finset.mem_filter, Finset.mem_erase]
    tauto
  have hx := (hmemT x).mp (by rw [hT]; simp)
  have hy := (hmemT y).mp (by rw [hT]; simp)
  have hz := (hmemT z).mp (by rw [hT]; simp)
  have hzero : ∀ ψ ∈ B, ψ ≠ p → ψ ≠ x → ψ ≠ y → ψ ≠ z → V ψ = 0 := by
    intro ψ hψ hψp hψx hψy hψz
    have hnot : ψ ∉ (B.erase p).filter (fun χ => |V χ| = 1) := by
      rw [hT]
      simp [hψx, hψy, hψz]
    have hnot2 : ¬ |V ψ| = 2 := by
      intro h2
      have hmem : ψ ∈ (B.erase p).filter (fun χ => |V χ| = 2) := by
        rw [Finset.mem_filter, Finset.mem_erase]
        exact ⟨⟨hψp, hψ⟩, h2⟩
      rw [Finset.card_eq_zero.mp htwos] at hmem
      simp at hmem
    rcases hval ψ (Finset.mem_erase.mpr ⟨hψp, hψ⟩) with h | h | h
    · exact h
    · exact absurd ((hmemT ψ).mpr ⟨hψ, hψp, h⟩) hnot
    · exact absurd h hnot2
  have hsign : ∀ ψ, |V ψ| = 1 → V ψ = 1 ∨ V ψ = -1 := fun ψ h => (abs_eq (by norm_num)).mp h
  have hne0 : ∀ ψ, |V ψ| = 1 → ∀ j ∈ J, ψ ≠ χ j := by
    intro ψ h j hj hψ
    rw [hψ, h0 j hj] at h
    norm_num at h
  refine ⟨![x, y, z], fun i => V (![x, y, z] i), ?_, ?_, ?_, ?_⟩
  · intro i i' h
    fin_cases i <;> fin_cases i' <;> simp_all
  · intro i
    fin_cases i
    · exact ⟨hx.1, hx.2.1, hne0 x hx.2.2⟩
    · exact ⟨hy.1, hy.2.1, hne0 y hy.2.2⟩
    · exact ⟨hz.1, hz.2.1, hne0 z hz.2.2⟩
  · intro i
    fin_cases i
    · exact hsign x hx.2.2
    · exact hsign y hy.2.2
    · exact hsign z hz.2.2
  · intro ψ hψ
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    by_cases hψp : ψ = p
    · rw [hψp, hVp, unitVector_self, unitVector_of_ne (Ne.symm hx.2.1),
        unitVector_of_ne (Ne.symm hy.2.1), unitVector_of_ne (Ne.symm hz.2.1)]
      ring
    by_cases hψx : ψ = x
    · rw [hψx, unitVector_of_ne hx.2.1, unitVector_self, unitVector_of_ne hxy,
        unitVector_of_ne hxz]
      ring
    by_cases hψy : ψ = y
    · rw [hψy, unitVector_of_ne hy.2.1, unitVector_of_ne (Ne.symm hxy), unitVector_self,
        unitVector_of_ne hyz]
      ring
    by_cases hψz : ψ = z
    · rw [hψz, unitVector_of_ne hz.2.1, unitVector_of_ne (Ne.symm hxz),
        unitVector_of_ne (Ne.symm hyz), unitVector_self]
      ring
    rw [hzero ψ hψ hψp hψx hψy hψz, unitVector_of_ne hψp, unitVector_of_ne hψx,
      unitVector_of_ne hψy, unitVector_of_ne hψz]
    ring

theorem sum_mul_residual (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V)
    (f : ι → ℤ) :
    ∑ ψ ∈ B, f ψ * (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ) =
      f p + σ * ∑ j ∈ J, f (χ j) := by
  have h : ∀ ψ, f ψ * (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ) =
      f ψ * unitVector p ψ + σ * ∑ j ∈ J, f ψ * unitVector (χ j) ψ := by
    intro ψ
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun ψ _ => h ψ, Finset.sum_add_distrib, sum_mul_unitVector hc.mem f,
    ← Finset.mul_sum, Finset.sum_comm]
  congr 2
  exact Finset.sum_congr rfl fun j hj => sum_mul_unitVector (hf.mem j hj) f

omit [DecidableEq κ] in
theorem residual_principal (hf : ParityFamily B p d J c σ χ V) :
    unitVector p p + σ * ∑ j ∈ J, unitVector (χ j) p = 1 := by
  rw [unitVector_self, Finset.sum_eq_zero fun j hj => unitVector_of_ne (Ne.symm (hf.ne j hj)),
    mul_zero, add_zero]

omit [DecidableEq κ] in
theorem residual_family (hf : ParityFamily B p d J c σ χ V) {t : κ} (ht : t ∈ J) :
    unitVector p (χ t) + σ * ∑ j ∈ J, unitVector (χ j) (χ t) = σ := by
  rw [unitVector_of_ne (hf.ne t ht), Finset.sum_eq_single t, unitVector_self, mul_one, zero_add]
  · intro j hj hjt
    exact unitVector_of_ne fun h => hjt (hf.injOn ht hj h).symm
  · intro h
    exact absurd ht h

theorem degree_V (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V) {j : κ}
    (hj : j ∈ J) : ∑ ψ ∈ B, d ψ * V ψ = -2 * σ * d (χ j) := by
  have h := hc.degree j hj
  have hcongr : ∑ ψ ∈ B, d ψ * c j ψ =
      ∑ ψ ∈ B, (d ψ * V ψ + 2 * σ * (d ψ * unitVector (χ j) ψ)) :=
    Finset.sum_congr rfl fun ψ hψ => by rw [hf.eq j hj ψ hψ]; ring
  rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, sum_mul_unitVector (hf.mem j hj)] at h
  linarith

theorem descII (hc : ParityColumns B p d J c) (hf : ParityFamily B p d J c σ χ V)
    (hJ : 2 ≤ J.card) (h1 : ∀ j ∈ J, V (χ j) = -σ) :
    J.card ≤ 6 ∧ ∃ w : ι → ℤ, w p = 0 ∧ (∀ j ∈ J, w (χ j) = 0) ∧
      (∀ j ∈ J, ∀ ψ ∈ B, c j ψ = -unitVector p ψ + w ψ + σ * unitVector (χ j) ψ -
        σ * ∑ t ∈ J.erase j, unitVector (χ t) ψ) ∧
      ∑ ψ ∈ B, w ψ ^ 2 = 7 - J.card ∧
      (∀ j ∈ J, ∑ ψ ∈ B, d ψ * w ψ = 1 + σ * (J.card - 2) * d (χ j)) ∧
      (HasCoefficientShape B w (7 - J.card) 0 ∨
        ((J.card = 2 ∨ J.card = 3) ∧ HasCoefficientShape B w (3 - J.card) 1)) := by
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  have hσ2 := hf.sq_sign
  have hQ : ∑ ψ ∈ B, V ψ ^ 2 = 8 := by
    have h := hf.sq_sum hc hj₀
    rw [h1 j₀ hj₀] at h
    linear_combination h + 4 * hσ2
  have hsumV : ∑ j ∈ J, V (χ j) = J.card * -σ := by
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  have hsumu : ∑ j ∈ J, (unitVector p (χ j) + σ * ∑ t ∈ J, unitVector (χ t) (χ j)) =
      J.card * σ := by
    rw [Finset.sum_congr rfl fun j hj => hf.residual_family hj, Finset.sum_const, nsmul_eq_mul]
  have hVu := hf.sum_mul_residual hc V
  have huu := hf.sum_mul_residual hc (fun ψ => unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ)
  rw [hf.V_principal hc hj₀, hsumV] at hVu
  rw [hf.residual_principal, hsumu] at huu
  have hW2 : ∑ ψ ∈ B, (V ψ + (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ)) ^ 2 =
      7 - J.card := by
    have hexp : ∑ ψ ∈ B, (V ψ + (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ)) ^ 2 =
        ∑ ψ ∈ B, V ψ ^ 2 +
          2 * ∑ ψ ∈ B, V ψ * (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ) +
          ∑ ψ ∈ B, (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ) *
            (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ψ _ => by ring
    rw [hexp, hQ, hVu, huu]
    linear_combination (-(J.card : ℤ)) * hσ2
  have hdeg : ∀ j ∈ J, ∑ ψ ∈ B, d ψ * (V ψ + (unitVector p ψ +
      σ * ∑ t ∈ J, unitVector (χ t) ψ)) = 1 + σ * (J.card - 2) * d (χ j) := by
    intro j hj
    have hsplit : ∑ ψ ∈ B, d ψ * (V ψ + (unitVector p ψ + σ * ∑ t ∈ J, unitVector (χ t) ψ)) =
        ∑ ψ ∈ B, d ψ * V ψ +
          ∑ ψ ∈ B, d ψ * (unitVector p ψ + σ * ∑ t ∈ J, unitVector (χ t) ψ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ψ _ => by ring
    have hdsum : ∑ t ∈ J, d (χ t) = J.card * d (χ j) := by
      rw [Finset.sum_congr rfl fun t ht => hf.deg t ht j hj, Finset.sum_const, nsmul_eq_mul]
    rw [hsplit, hf.degree_V hc hj, hf.sum_mul_residual hc d, hc.one, hdsum]
    ring
  have hk7 : J.card ≤ 7 := by
    have hnn : 0 ≤ ∑ ψ ∈ B, (V ψ + (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ)) ^ 2 :=
      Finset.sum_nonneg fun ψ _ => sq_nonneg _
    rw [hW2] at hnn
    omega
  have hk6 : J.card ≤ 6 := by
    by_contra h6
    have hk : J.card = 7 := by omega
    have h0 : ∑ ψ ∈ B, (V ψ + (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ)) ^ 2 = 0 := by
      rw [hW2, hk]
      norm_num
    have hzero : ∀ ψ ∈ B, V ψ + (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ) = 0 :=
      fun ψ hψ => (pow_eq_zero_iff two_ne_zero).mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun ψ _ => sq_nonneg _).mp h0 ψ hψ)
    have hd0 := hdeg j₀ hj₀
    rw [Finset.sum_eq_zero fun ψ hψ => by rw [hzero ψ hψ, mul_zero], hk] at hd0
    have hpos := hc.pos (χ j₀) (hf.mem j₀ hj₀)
    rcases hf.sign with h | h <;> rw [h] at hd0 <;> norm_num at hd0 <;> omega
  have hW2' : ∑ ψ ∈ B, (V ψ + (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ)) ^ 2 =
      ((7 - J.card : ℕ) : ℤ) := by
    rw [hW2, Nat.cast_sub hk7]
    norm_num
  refine ⟨hk6, fun ψ => V ψ + (unitVector p ψ + σ * ∑ j ∈ J, unitVector (χ j) ψ), ?_, ?_, ?_,
    hW2, hdeg, ?_⟩
  · beta_reduce
    rw [hf.residual_principal, hf.V_principal hc hj₀]
    norm_num
  · intro t ht
    beta_reduce
    rw [hf.residual_family ht, h1 t ht]
    ring
  · intro j hj ψ hψ
    beta_reduce
    rw [hf.eq j hj ψ hψ, ← Finset.add_sum_erase J (fun t => unitVector (χ t) ψ) hj]
    ring
  · rcases hasCoefficientShape_of_sq_sum (by omega) hW2' with h0 | ⟨h4, hsh⟩
    · exact Or.inl h0
    · refine Or.inr ⟨by omega, ?_⟩
      have h3 : 7 - J.card - 4 = 3 - J.card := by omega
      rwa [h3] at hsh

end ParityFamily

end CFSG.Wreathed.ConditionalFourier
