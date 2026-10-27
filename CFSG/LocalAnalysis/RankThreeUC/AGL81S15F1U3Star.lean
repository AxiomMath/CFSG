module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3Mon

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F]

section Elements

variable {N : ℕ}

@[expose] def z0 : GL (Fin 3) F := dGL (-1) (-1) 1

@[expose] def tau0 : GL (Fin 3) F := sGL 1 1 (-1)

theorem z0_mem (hN : Even N) : (z0 : GL (Fin 3) F) ∈ stdMon (F := F) N := by
  have hneg : ((-1 : Fˣ)) ^ N = 1 := by rw [hN.neg_pow, one_pow]
  refine ⟨-1, -1, hneg, hneg, Or.inl ?_⟩
  simp [z0]

theorem tau0_mem : (tau0 : GL (Fin 3) F) ∈ stdMon (F := F) N := by
  refine ⟨1, 1, one_pow _, one_pow _, Or.inr ?_⟩
  simp [tau0]

theorem b0_mem {ι : Fˣ} (hι : ι ^ N = 1) : (dGL ι ι⁻¹ 1 : GL (Fin 3) F) ∈ stdMon (F := F) N := by
  refine ⟨ι, ι⁻¹, hι, by rw [inv_pow, hι, inv_one], Or.inl ?_⟩
  simp

theorem b1_mem {ι : Fˣ} (hι : ι ^ N = 1) : (dGL ι 1 ι⁻¹ : GL (Fin 3) F) ∈ stdMon (F := F) N := by
  refine ⟨ι, 1, hι, one_pow _, Or.inl ?_⟩
  simp

theorem z0_comm {x : GL (Fin 3) F} (hx : x ∈ stdMon (F := F) N) : x * z0 = z0 * x := by
  obtain ⟨α, β, -, -, rfl | rfl⟩ := hx
  · simp only [z0, dGL_mul_dGL]
    congr 1 <;> exact mul_comm _ _
  · simp only [z0, dGL_mul_sGL, sGL_mul_dGL]
    congr 1 <;> exact mul_comm _ _

theorem central_involution_eq {ι : Fˣ} (hι : ι ^ N = 1) (hι2 : ι ^ 2 ≠ 1)
    {y : GL (Fin 3) F} (hy : y ∈ stdMon (F := F) N)
    (hc : ∀ x ∈ stdMon (F := F) N, y * x = x * y) (hy2 : y * y = 1) : y = 1 ∨ y = z0 := by
  obtain ⟨α, β, hα, hβ, rfl | rfl⟩ := hy
  ·
    have h1 := hc _ (tau0_mem (N := N))
    simp only [tau0, dGL_mul_sGL, sGL_mul_dGL] at h1
    obtain ⟨h2, -⟩ := sGL_inj h1
    simp only [one_mul, mul_one] at h2
    subst h2
    rw [dGL_mul_dGL] at hy2
    have h3 : α * α = 1 := by
      exact (dGL_inj (hy2.trans dGL_one.symm)).1
    have h4 : (α : F) = 1 ∨ (α : F) = -1 := by
      have : (α : F) * α = 1 := by simpa using congrArg Units.val h3
      exact mul_self_eq_one_iff.1 this
    rcases h4 with h | h
    · left
      have : α = 1 := Units.ext h
      subst this
      simp [dGL_one]
    · right
      have : α = -1 := Units.ext (by simpa using h)
      subst this
      simp [z0]
  ·
    exfalso
    have h1 := hc _ (b0_mem (N := N) hι)
    simp only [sGL_mul_dGL, dGL_mul_sGL] at h1
    obtain ⟨h2, -⟩ := sGL_inj h1
    have h3 : ι⁻¹ = ι := mul_left_cancel (a := α) (h2.trans (mul_comm ι α))
    apply hι2
    rw [sq]
    calc ι * ι = ι * ι⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel ι

theorem z0_mul_self : (z0 : GL (Fin 3) F) * z0 = 1 := by
  simp [z0, dGL_mul_dGL, dGL_one]

theorem z0_ne_one (h2 : (2 : F) ≠ 0) : (z0 : GL (Fin 3) F) ≠ 1 := by
  intro h
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [z0, coe_dGL, dMat] at h'
  apply h2
  linear_combination -h'

theorem conj_z0_eq (h2 : (2 : F) ≠ 0) {ι : Fˣ} (hN : Even N) (hι : ι ^ N = 1) (hι2 : ι ^ 2 ≠ 1)
    {n : GL (Fin 3) F} (hn : ∀ g, g ∈ stdMon (F := F) N ↔ n * g * n⁻¹ ∈ stdMon (F := F) N) :
    n * z0 * n⁻¹ = z0 := by
  have hy : n * z0 * n⁻¹ ∈ stdMon (F := F) N := (hn z0).1 (z0_mem hN)
  have hc : ∀ x ∈ stdMon (F := F) N, (n * z0 * n⁻¹) * x = x * (n * z0 * n⁻¹) := by
    intro x hx
    have hx' : n⁻¹ * x * n ∈ stdMon (F := F) N := by
      refine (hn _).2 ?_
      have : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
      rw [this]; exact hx
    have hcomm := z0_comm hx'
    calc n * z0 * n⁻¹ * x = n * (z0 * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * x * n) * z0) * n⁻¹ := by rw [hcomm]
      _ = x * (n * z0 * n⁻¹) := by group
  have hy2 : (n * z0 * n⁻¹) * (n * z0 * n⁻¹) = 1 := by
    calc (n * z0 * n⁻¹) * (n * z0 * n⁻¹) = n * (z0 * z0) * n⁻¹ := by group
      _ = 1 := by rw [z0_mul_self]; group
  rcases central_involution_eq hι hι2 hy hc hy2 with h | h
  · exfalso
    apply z0_ne_one h2
    have : n * z0 = n := by
      have h' : n * z0 * n⁻¹ = 1 := h
      rwa [mul_inv_eq_one] at h'
    exact mul_eq_left.1 this
  · exact h

theorem blockShape_of_commute_z0 (h2 : (2 : F) ≠ 0) {n : GL (Fin 3) F} (h : n * z0 = z0 * n) :
    (n : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (n : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (n : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Units.val_mul, z0, coe_dGL, dMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
  have e02 := congrFun (congrFun h' 0) 2
  have e12 := congrFun (congrFun h' 1) 2
  have e20 := congrFun (congrFun h' 2) 0
  have e21 := congrFun (congrFun h' 2) 1
  simp at e02 e12 e20 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : F) * (n : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by linear_combination e02
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : F) * (n : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by linear_combination e12
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : F) * (n : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by linear_combination -e20
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : F) * (n : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by linear_combination -e21
    exact (mul_eq_zero.1 this).resolve_left h2

theorem exists_ne_zero_col (n : GL (Fin 3) F) (j : Fin 3) :
    ∃ i, (n : Matrix (Fin 3) (Fin 3) F) i j ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : ((n⁻¹ * n : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j j = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply] at h1
  simp [h] at h1

theorem diag_or_swap_of_normalizer (h2 : (2 : F) ≠ 0) {ι : Fˣ} (hι : ι ^ N = 1) (hι2 : ι ^ 2 ≠ 1)
    {n : GL (Fin 3) F} (hn : ∀ g, g ∈ stdMon (F := F) N ↔ n * g * n⁻¹ ∈ stdMon (F := F) N)
    (hsh : (n : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (n : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (n : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ((n : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (n : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) ∨
      ((n : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 ∧ (n : Matrix (Fin 3) (Fin 3) F) 1 1 = 0) := by
  obtain ⟨h02, h12, h20, h21⟩ := hsh
  have hι1 : ι ≠ 1 := fun h => hι2 (by rw [h]; simp)
  have hι1' : (ι : F) ≠ 1 := fun h => hι1 (Units.ext h)
  have hy := (hn _).1 (b1_mem (N := N) hι)
  have hmat : ∀ y : GL (Fin 3) F, y = n * dGL ι 1 ι⁻¹ * n⁻¹ →
      (n : Matrix (Fin 3) (Fin 3) F) * dMat (ι : F) 1 ((ι⁻¹ : Fˣ) : F) =
        (y : Matrix (Fin 3) (Fin 3) F) * n := by
    intro y hy'
    have : y * n = n * dGL ι 1 ι⁻¹ := by rw [hy']; group
    have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) this
    simp only [Units.val_mul, coe_dGL] at h'
    simpa using h'.symm
  obtain ⟨i0, hi0⟩ := exists_ne_zero_col n 0
  obtain ⟨i1, hi1⟩ := exists_ne_zero_col n 1
  have hc0 : (n : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 ∨ (n : Matrix (Fin 3) (Fin 3) F) 1 0 ≠ 0 := by
    fin_cases i0
    · exact Or.inl hi0
    · exact Or.inr hi0
    · exact absurd h20 hi0
  have hc1 : (n : Matrix (Fin 3) (Fin 3) F) 0 1 ≠ 0 ∨ (n : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := by
    fin_cases i1
    · exact Or.inl hi1
    · exact Or.inr hi1
    · exact absurd h21 hi1
  obtain ⟨α, β, hα, hβ, hyα | hyβ⟩ := hy
  ·
    have hm := hmat _ hyα.symm
    simp only [coe_dGL, dMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at hm
    have e00 := congrFun (congrFun hm 0) 0
    have e01 := congrFun (congrFun hm 0) 1
    have e10 := congrFun (congrFun hm 1) 0
    have e11 := congrFun (congrFun hm 1) 1
    simp at e00 e01 e10 e11
    have c00 : (n : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 → (α : F) = ι := fun h =>
      mul_right_cancel₀ h (by linear_combination (-1 : F) * e00)
    have c10 : (n : Matrix (Fin 3) (Fin 3) F) 1 0 ≠ 0 → (β : F) = ι := fun h =>
      mul_right_cancel₀ h (by linear_combination (-1 : F) * e10)
    have c01 : (n : Matrix (Fin 3) (Fin 3) F) 0 1 ≠ 0 → (α : F) = 1 := fun h =>
      mul_right_cancel₀ h (by linear_combination (-1 : F) * e01)
    have c11 : (n : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 → (β : F) = 1 := fun h =>
      mul_right_cancel₀ h (by linear_combination (-1 : F) * e11)
    by_cases hαι : (α : F) = ι
    · left
      have h01 : (n : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
        by_contra h
        exact hι1' (hαι.symm.trans (c01 h))
      refine ⟨h01, ?_⟩
      by_contra h10
      have hβι := c10 h10
      have hn11 : (n : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := by
        rcases hc1 with h | h
        · exact absurd h01 h
        · exact h
      exact hι1' (hβι.symm.trans (c11 hn11))
    · right
      have h00 : (n : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by
        by_contra h
        exact hαι (c00 h)
      refine ⟨h00, ?_⟩
      have h10 : (n : Matrix (Fin 3) (Fin 3) F) 1 0 ≠ 0 := by
        rcases hc0 with h | h
        · exact absurd h00 h
        · exact h
      have hβι := c10 h10
      by_contra h11
      exact hι1' (hβι.symm.trans (c11 h11))
  ·
    exfalso
    have hm := hmat _ hyβ.symm
    simp only [coe_sGL, sMat', dMat, Matrix.mul_diagonal] at hm
    have e00 := congrFun (congrFun hm 0) 0
    have e10 := congrFun (congrFun hm 1) 0
    have e01 := congrFun (congrFun hm 0) 1
    have e11 := congrFun (congrFun hm 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e10 e01 e11
    have hA0 : (ι : F) ^ 2 = α * β := by
      have f0 : ((ι : F) ^ 2 - α * β) * (n : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by
        linear_combination (ι : F) * e00 + (α : F) * e10
      have f1 : ((ι : F) ^ 2 - α * β) * (n : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
        linear_combination (ι : F) * e10 + (β : F) * e00
      rcases hc0 with h | h
      · exact sub_eq_zero.1 ((mul_eq_zero.1 f0).resolve_right h)
      · exact sub_eq_zero.1 ((mul_eq_zero.1 f1).resolve_right h)
    have hB0 : (1 : F) = α * β := by
      have f0 : (1 - (α : F) * β) * (n : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
        linear_combination e01 + (α : F) * e11
      have f1 : (1 - (α : F) * β) * (n : Matrix (Fin 3) (Fin 3) F) 1 1 = 0 := by
        linear_combination e11 + (β : F) * e01
      rcases hc1 with h | h
      · exact sub_eq_zero.1 ((mul_eq_zero.1 f0).resolve_right h)
      · exact sub_eq_zero.1 ((mul_eq_zero.1 f1).resolve_right h)
    apply hι2
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [hA0, ← hB0]

theorem exists_dGL_of_coe (n : GL (Fin 3) F) {a b c : F}
    (h : (n : Matrix (Fin 3) (Fin 3) F) = dMat a b c) : ∃ a' b' c' : Fˣ, n = dGL a' b' c' := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero n
  rw [h, det_dMat] at hdet
  have ha : a ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have hb : b ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have hc : c ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  exact ⟨Units.mk0 a ha, Units.mk0 b hb, Units.mk0 c hc, Units.ext (by simp [coe_dGL, h])⟩

theorem exists_sGL_of_coe (n : GL (Fin 3) F) {a b c : F}
    (h : (n : Matrix (Fin 3) (Fin 3) F) = sMat' a b c) : ∃ a' b' c' : Fˣ, n = sGL a' b' c' := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero n
  rw [h, det_sMat'] at hdet
  have ha : a ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have hb : b ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have hc : c ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  exact ⟨Units.mk0 a ha, Units.mk0 b hb, Units.mk0 c hc, Units.ext (by simp [coe_sGL, h])⟩

theorem conj_tau0_dGL (a b c : Fˣ) :
    (dGL a b c : GL (Fin 3) F) * tau0 * (dGL a b c)⁻¹ = sGL (a * 1 * b⁻¹) (b * 1 * a⁻¹) (c * -1 * c⁻¹) := by
  rw [tau0, dGL_mul_sGL, dGL_inv, sGL_mul_dGL]

theorem conj_tau0_sGL (a b c : Fˣ) :
    (sGL a b c : GL (Fin 3) F) * tau0 * (sGL a b c)⁻¹ = sGL (a * 1 * b⁻¹) (b * 1 * a⁻¹) (c * -1 * c⁻¹) := by
  rw [tau0, sGL_mul_sGL, sGL_inv, dGL_mul_sGL]

end Elements

section Main

variable {N : ℕ} {p f : ℕ} [Fact p.Prime] [CharP F p] [Finite F]

theorem exists_mul_central_of_mem_normalizer (h2 : (2 : F) ≠ 0) {ι : Fˣ} (hN : Even N)
    (hι : ι ^ N = 1) (hι2 : ι ^ 2 ≠ 1) {n : GL (Fin 3) F}
    (hnU : n ∈ SUid (unitaryInvolution F p f) 3)
    (hn : ∀ g, g ∈ stdMon (F := F) N ↔ n * g * n⁻¹ ∈ stdMon (F := F) N) :
    ∃ s ∈ stdMon (F := F) N, ∃ l : Fˣ, unitaryInvolution F p f (l : F) * l = 1 ∧
      n = s * dGL l l (l * l)⁻¹ := by
  have hz := conj_z0_eq h2 hN hι hι2 hn
  have hcomm : n * z0 = z0 * n := by
    have : n * z0 * n⁻¹ * n = z0 * n := by rw [hz]
    simpa using this
  have hsh := blockShape_of_commute_z0 h2 hcomm
  obtain ⟨h02, h12, h20, h21⟩ := hsh
  have hτ : n * tau0 * n⁻¹ ∈ stdMon (F := F) N := (hn _).1 tau0_mem
  rcases diag_or_swap_of_normalizer h2 hι hι2 hn ⟨h02, h12, h20, h21⟩ with ⟨h01, h10⟩ | ⟨h00, h11⟩
  ·
    have hd : (n : Matrix (Fin 3) (Fin 3) F) = dMat ((n : Matrix (Fin 3) (Fin 3) F) 0 0)
        ((n : Matrix (Fin 3) (Fin 3) F) 1 1) ((n : Matrix (Fin 3) (Fin 3) F) 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dMat, h01, h10, h02, h12, h20, h21]
    obtain ⟨a, b, c, rfl⟩ := exists_dGL_of_coe n hd
    obtain ⟨⟨hσa, hσb, hσc⟩, hdet⟩ := (dGL_mem_SUid _).1 hnU
    have habc : a * b * c = 1 := Units.ext (by simpa using hdet)
    rw [conj_tau0_dGL] at hτ
    obtain ⟨α, β, hα, hβ, hs | hs⟩ := hτ
    · exact (dGL_ne_sGL _ _ _ _ _ _ hs.symm).elim
    · obtain ⟨hab, -⟩ := sGL_inj hs
      have hab' : (a * b⁻¹) ^ N = 1 := by
        have : a * 1 * b⁻¹ = α := hab
        rw [mul_one] at this
        rw [this]; exact hα
      refine ⟨dGL (a * b⁻¹) 1 (c * (b * b)), ⟨a * b⁻¹, 1, hab', one_pow _, Or.inl ?_⟩, b, hσb, ?_⟩
      · congr 1
        have hc : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habc
        rw [hc]
        apply Units.ext
        have h1 := a.ne_zero
        have h2' := b.ne_zero
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
        field_simp
      · rw [dGL_mul_dGL]
        congr 1 <;> group
  ·
    have hd : (n : Matrix (Fin 3) (Fin 3) F) = sMat' ((n : Matrix (Fin 3) (Fin 3) F) 0 1)
        ((n : Matrix (Fin 3) (Fin 3) F) 1 0) ((n : Matrix (Fin 3) (Fin 3) F) 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sMat', h00, h11, h02, h12, h20, h21]
    obtain ⟨a, b, c, rfl⟩ := exists_sGL_of_coe n hd
    obtain ⟨⟨hσa, hσb, hσc⟩, hdet⟩ := (sGL_mem_SUid _).1 hnU
    have habc : a * b * c = -1 := Units.ext (by simpa using hdet)
    rw [conj_tau0_sGL] at hτ
    obtain ⟨α, β, hα, hβ, hs | hs⟩ := hτ
    · exact (dGL_ne_sGL _ _ _ _ _ _ hs.symm).elim
    · obtain ⟨hab, -⟩ := sGL_inj hs
      have hab' : (a * b⁻¹) ^ N = 1 := by
        have : a * 1 * b⁻¹ = α := hab
        rw [mul_one] at this
        rw [this]; exact hα
      refine ⟨sGL (a * b⁻¹) 1 (c * (b * b)), ⟨a * b⁻¹, 1, hab', one_pow _, Or.inr ?_⟩, b, hσb, ?_⟩
      · congr 1
        have hc : c = -(a * b)⁻¹ := by
          calc c = (a * b)⁻¹ * (a * b * c) := by group
            _ = (a * b)⁻¹ * -1 := by rw [habc]
            _ = -(a * b)⁻¹ := by rw [mul_neg, mul_one]
        rw [hc]
        apply Units.ext
        have h1 := a.ne_zero
        have h2' := b.ne_zero
        simp only [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, Units.val_one]
        field_simp
      · rw [sGL_mul_dGL]
        congr 1 <;> group

end Main

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
