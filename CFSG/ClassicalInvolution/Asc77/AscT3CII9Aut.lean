module

public import CFSG.ClassicalInvolution.Asc77.AscT3CII9Eps
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Matrices

variable {F : Type*} [Field F]

theorem exists_sq_add_sq_neg_one_fixed [Finite F] (hF : Odd (Nat.card F)) (σ : F ≃+* F) :
    ∃ a b : F, a ^ 2 + b ^ 2 = -1 ∧ σ a = a ∧ σ b = b := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  have hp2 : ringChar F ≠ 2 := by
    intro h
    apply h2
    have : (2 : F) = ((ringChar F : ℕ) : F) := by rw [h]; norm_num
    rw [this]
    exact ringChar.Nat.cast_ringChar
  have hodd : Odd (Nat.card (ZMod (ringChar F))) := by
    rw [Nat.card_zmod]
    exact hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨a₀, b₀, hab⟩ :=
    CFSG.Semidihedral.OddFieldSL2.sum_two_squares (ZMod (ringChar F)) hodd (-1)
  obtain ⟨φ, hσφ⟩ : ∃ φ : ZMod (ringChar F) →+* F, σ.toRingHom.comp φ = φ :=
    ⟨ZMod.castHom (dvd_refl _) F, RingHom.ext_zmod _ _⟩
  refine ⟨φ a₀, φ b₀, ?_, ?_, ?_⟩
  · have h := congrArg φ hab
    rw [map_add, map_pow, map_pow] at h
    exact h.trans ((map_neg φ (1 : ZMod (ringChar F))).trans (by rw [map_one]))
  · exact congrArg (fun g => g a₀) hσφ
  · exact congrArg (fun g => g b₀) hσφ

@[expose] noncomputable def wA (F : Type*) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

@[expose] noncomputable def wB {F : Type*} [Field F] (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    SL(2, F) :=
  ⟨!![a, b; b, -a], by rw [Matrix.det_fin_two_of]; linear_combination (-1 : F) * h⟩

theorem neg_one_coe_matrix : ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    Matrix.scalar (Fin 2) (-1) := CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix F

theorem wA_coe : ((wA F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem wB_coe (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    ((wB a b h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a] := rfl

theorem wA_mul_wA : wA F * wA F = -1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [neg_one_coe_matrix, Matrix.SpecialLinearGroup.coe_mul, wA_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wB_mul_wB (a b : F) (h : a ^ 2 + b ^ 2 = -1) : wB a b h * wB a b h = -1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [neg_one_coe_matrix, Matrix.SpecialLinearGroup.coe_mul, wB_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

theorem wA_mul_wB (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    wA F * wB a b h = (-1) * (wB a b h * wA F) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, neg_one_coe_matrix, wA_coe, wB_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wA_ne_one_ne_neg_one : wA F ≠ 1 ∧ wA F ≠ -1 := by
  constructor
  · intro h
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [wA_coe] at this
  · intro h
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [wA_coe] at this

theorem wB_ne_one_ne_neg_one (h2 : (2 : F) ≠ 0) (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    wB a b h ≠ 1 ∧ wB a b h ≠ -1 := by
  constructor
  · intro hc
    have h1 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hc
    have h2' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hc
    simp [wB_coe] at h1 h2'
    subst h1
    subst h2'
    apply h2
    linear_combination h
  · intro hc
    have h1 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hc
    have h2' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hc
    simp [wB_coe] at h1 h2'
    subst h1
    subst h2'
    apply h2
    linear_combination h

theorem wA_mul_wB_ne_one_ne_neg_one (h2 : (2 : F) ≠ 0) (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    wA F * wB a b h ≠ 1 ∧ wA F * wB a b h ≠ -1 := by
  constructor
  · intro hc
    have h1 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hc
    have h2' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 1 1) hc
    simp [Matrix.SpecialLinearGroup.coe_mul, wA_coe, wB_coe, Matrix.mul_apply,
      Fin.sum_univ_two] at h1 h2'
    apply h2
    linear_combination -h1 - h2'
  · intro hc
    have h1 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hc
    have h2' := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 1 1) hc
    simp [Matrix.SpecialLinearGroup.coe_mul, wA_coe, wB_coe, Matrix.mul_apply,
      Fin.sum_univ_two] at h1 h2'
    apply h2
    linear_combination h1 - h2'

end Matrices

section Auts

variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
theorem conj_eq_one_iff (x : SL(2, F)) : MulAut.conj x = 1 ↔ x ∈ Subgroup.center SL(2, F) := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := DFunLike.congr_fun h g
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    apply MulEquiv.ext
    intro g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h g).symm

omit [Finite F] in
theorem conj_neg_one : MulAut.conj (-1 : SL(2, F)) = 1 :=
  (conj_eq_one_iff _).mpr ((CFSG.ClassicalInvolution.mem_center_sl2_iff _).mpr (Or.inr rfl))

omit [Finite F] in
theorem conj_neg_one_mul (x : SL(2, F)) : MulAut.conj ((-1) * x) = MulAut.conj x := by
  rw [map_mul, conj_neg_one, one_mul]

omit [Finite F] in
theorem conj_ne_one {x : SL(2, F)} (h1 : x ≠ 1) (h2 : x ≠ -1) : MulAut.conj x ≠ 1 := by
  intro h
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff x).mp ((conj_eq_one_iff x).mp h) with h | h
  · exact h1 h
  · exact h2 h

omit [Finite F] in
theorem slFieldAut_one : slFieldAut F 1 = 1 := by
  ext x : 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

omit [Finite F] in
theorem slFieldAut_mul (σ τ : F ≃+* F) :
    slFieldAut F (σ * τ) = slFieldAut F σ * slFieldAut F τ := by
  ext x : 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

omit [Finite F] in
theorem slFieldAut_comm_conj (σ : F ≃+* F) (x : SL(2, F)) (hx : slFieldAut F σ x = x) :
    slFieldAut F σ * MulAut.conj x = MulAut.conj x * slFieldAut F σ := by
  have h := mul_mulAutConj_mul_inv (slFieldAut F σ) x
  rw [hx] at h
  calc slFieldAut F σ * MulAut.conj x
      = (slFieldAut F σ * MulAut.conj x * (slFieldAut F σ)⁻¹) * slFieldAut F σ := by group
    _ = MulAut.conj x * slFieldAut F σ := by rw [h]

omit [Finite F] in
theorem slFieldAut_wA (σ : F ≃+* F) : slFieldAut F σ (wA F) = wA F := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [slFieldAut_entry]
  fin_cases i <;> fin_cases j <;> simp [wA_coe]

omit [Finite F] in
theorem slFieldAut_wB (σ : F ≃+* F) (a b : F) (h : a ^ 2 + b ^ 2 = -1) (ha : σ a = a)
    (hb : σ b = b) : slFieldAut F σ (wB a b h) = wB a b h := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [slFieldAut_entry]
  fin_cases i <;> fin_cases j <;> simp [wB_coe, ha, hb]

end Auts


section Generic

variable {H : Type*} [Group H]

theorem eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {y z : C}
    (hy : y * y = 1) (hz : z * z = 1) (hy1 : y ≠ 1) (hz1 : z ≠ 1) : y = z := by
  classical
  by_contra hyz
  have : Fintype C := Fintype.ofFinite C
  have h := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, y, z} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · rwa [pow_two]
    · rwa [pow_two]
  have hcard : ({1, y, z} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hyz]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hy1 h.symm, fun h => hz1 h.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem eq_of_mem_zpowers_of_sq_eq_one [Finite H] {β y z : H} (hy : y ∈ Subgroup.zpowers β)
    (hz : z ∈ Subgroup.zpowers β) (hy2 : y * y = 1) (hz2 : z * z = 1) (hy1 : y ≠ 1)
    (hz1 : z ≠ 1) : y = z := by
  have := eq_of_sq_eq_one_of_isCyclic (C := ↥(Subgroup.zpowers β)) (y := ⟨y, hy⟩) (z := ⟨z, hz⟩)
    (Subtype.ext hy2) (Subtype.ext hz2) (fun h => hy1 (congrArg Subtype.val h))
    (fun h => hz1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem false_of_two_involutions [Finite H] {P : Subgroup H} {β : H}
    (hPB : P ≤ Subgroup.zpowers β) {x₁ x₂ : H} (hx₁ : x₁ ∈ P) (hx₂ : x₂ ∈ P)
    (s₁ : x₁ * x₁ = 1) (s₂ : x₂ * x₂ = 1) (n₁ : x₁ ≠ 1) (n₂ : x₂ ≠ 1) (d : x₁ ≠ x₂) : False :=
  d (eq_of_mem_zpowers_of_sq_eq_one (hPB hx₁) (hPB hx₂) s₁ s₂ n₁ n₂)

theorem false_of_three_involutions [Finite H] {P : Subgroup H} {β : H}
    (hind : (Subgroup.zpowers β).relIndex P ≤ 2)
    {x₁ x₂ x₃ : H} (hx₁ : x₁ ∈ P) (hx₂ : x₂ ∈ P) (hx₃ : x₃ ∈ P)
    (c₁₂ : x₁ * x₂ = x₂ * x₁) (c₁₃ : x₁ * x₃ = x₃ * x₁) (c₂₃ : x₂ * x₃ = x₃ * x₂)
    (s₁ : x₁ * x₁ = 1) (s₂ : x₂ * x₂ = 1) (s₃ : x₃ * x₃ = 1)
    (n₁ : x₁ ≠ 1) (n₂ : x₂ ≠ 1) (n₃ : x₃ ≠ 1) (d₁₂ : x₁ ≠ x₂) (d₁₃ : x₁ ≠ x₃) (d₂₃ : x₂ ≠ x₃)
    (hprod : x₁ * x₂ * x₃ ≠ 1) : False := by
  set B := Subgroup.zpowers β with hB
  have hU : ∀ {y z : H}, y ∈ B → z ∈ B → y * y = 1 → z * z = 1 → y ≠ 1 → z ≠ 1 → y = z :=
    fun hy hz hy2 hz2 hy1 hz1 => eq_of_mem_zpowers_of_sq_eq_one hy hz hy2 hz2 hy1 hz1
  have hpos : (B.relIndex P) ≠ 0 := by
    show (B.subgroupOf P).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hcases : B.relIndex P = 1 ∨ B.relIndex P = 2 := by omega
  rcases hcases with h1 | h2
  · have hPB : P ≤ B := Subgroup.relIndex_eq_one.mp h1
    exact false_of_two_involutions hPB hx₁ hx₂ s₁ s₂ n₁ n₂ d₁₂
  · obtain ⟨a, haP, haB, hall⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and').mp h2
    have hpair : ∀ {y z : H}, y ∈ P → z ∈ P → y ∉ B → z ∉ B → y * y = 1 → y * z ∈ B := by
      intro y z hy hz hyB hzB hy2
      have h1 : a * y ∈ B := (hall y hy).resolve_right hyB
      have h2 : a * z ∈ B := (hall z hz).resolve_right hzB
      have h3 : (a * y)⁻¹ * (a * z) ∈ B := B.mul_mem (B.inv_mem h1) h2
      have h4 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have : (a * y)⁻¹ * (a * z) = y * z := by
        rw [mul_inv_rev, h4]; group
      rwa [this] at h3
    by_cases m₁ : x₁ ∈ B <;> by_cases m₂ : x₂ ∈ B <;> by_cases m₃ : x₃ ∈ B
    · exact d₁₂ (hU m₁ m₂ s₁ s₂ n₁ n₂)
    · exact d₁₂ (hU m₁ m₂ s₁ s₂ n₁ n₂)
    · exact d₁₃ (hU m₁ m₃ s₁ s₃ n₁ n₃)
    ·
      have h23 := hpair hx₂ hx₃ m₂ m₃ s₂
      have hsq : (x₂ * x₃) * (x₂ * x₃) = 1 := by
        calc (x₂ * x₃) * (x₂ * x₃) = x₂ * (x₃ * x₂) * x₃ := by group
          _ = x₂ * (x₂ * x₃) * x₃ := by rw [c₂₃]
          _ = (x₂ * x₂) * (x₃ * x₃) := by group
          _ = 1 := by rw [s₂, s₃, one_mul]
      have hne : x₂ * x₃ ≠ 1 := fun h => d₂₃ (mul_right_cancel (h.trans (s₃.symm)))
      have := hU m₁ h23 s₁ hsq n₁ hne
      apply hprod
      rw [this]
      calc x₂ * x₃ * x₂ * x₃ = (x₂ * x₃) * (x₂ * x₃) := by group
        _ = 1 := hsq
    · exact d₂₃ (hU m₂ m₃ s₂ s₃ n₂ n₃)
    ·
      have h13 := hpair hx₁ hx₃ m₁ m₃ s₁
      have hsq : (x₁ * x₃) * (x₁ * x₃) = 1 := by
        calc (x₁ * x₃) * (x₁ * x₃) = x₁ * (x₃ * x₁) * x₃ := by group
          _ = x₁ * (x₁ * x₃) * x₃ := by rw [c₁₃]
          _ = (x₁ * x₁) * (x₃ * x₃) := by group
          _ = 1 := by rw [s₁, s₃, one_mul]
      have hne : x₁ * x₃ ≠ 1 := fun h => d₁₃ (mul_right_cancel (h.trans (s₃.symm)))
      have := hU m₂ h13 s₂ hsq n₂ hne
      apply hprod
      calc x₁ * x₂ * x₃ = x₁ * (x₂ * x₃) := by group
        _ = x₁ * (x₃ * x₂) := by rw [c₂₃]
        _ = (x₁ * x₃) * x₂ := by group
        _ = (x₁ * x₃) * (x₁ * x₃) := by rw [← this]
        _ = 1 := hsq
    ·
      have h12 := hpair hx₁ hx₂ m₁ m₂ s₁
      have hsq : (x₁ * x₂) * (x₁ * x₂) = 1 := by
        calc (x₁ * x₂) * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
          _ = x₁ * (x₁ * x₂) * x₂ := by rw [c₁₂]
          _ = (x₁ * x₁) * (x₂ * x₂) := by group
          _ = 1 := by rw [s₁, s₂, one_mul]
      have hne : x₁ * x₂ ≠ 1 := fun h => d₁₂ (mul_right_cancel (h.trans (s₂.symm)))
      have := hU m₃ h12 s₃ hsq n₃ hne
      apply hprod
      rw [← this]
      exact s₃
    ·
      have h12 := hpair hx₁ hx₂ m₁ m₂ s₁
      have h13 := hpair hx₁ hx₃ m₁ m₃ s₁
      have hsq12 : (x₁ * x₂) * (x₁ * x₂) = 1 := by
        calc (x₁ * x₂) * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
          _ = x₁ * (x₁ * x₂) * x₂ := by rw [c₁₂]
          _ = (x₁ * x₁) * (x₂ * x₂) := by group
          _ = 1 := by rw [s₁, s₂, one_mul]
      have hsq13 : (x₁ * x₃) * (x₁ * x₃) = 1 := by
        calc (x₁ * x₃) * (x₁ * x₃) = x₁ * (x₃ * x₁) * x₃ := by group
          _ = x₁ * (x₁ * x₃) * x₃ := by rw [c₁₃]
          _ = (x₁ * x₁) * (x₃ * x₃) := by group
          _ = 1 := by rw [s₁, s₃, one_mul]
      have hne12 : x₁ * x₂ ≠ 1 := fun h => d₁₂ (mul_right_cancel (h.trans (s₂.symm)))
      have hne13 : x₁ * x₃ ≠ 1 := fun h => d₁₃ (mul_right_cancel (h.trans (s₃.symm)))
      have := hU h12 h13 hsq12 hsq13 hne12 hne13
      exact d₂₃ (mul_left_cancel this)

theorem conj_eq_one_iff' {g x : H} : g * x * g⁻¹ = 1 ↔ x = 1 := by
  constructor
  · intro h
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  · rintro rfl
    group

theorem conj_inj' {g x y : H} : g * x * g⁻¹ = g * y * g⁻¹ ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · rintro rfl
    rfl

theorem conj_mul_conj (g x y : H) : (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by
  group

end Generic

section ElementsAut

variable {F : Type*} [Field F]

theorem cA_sq : MulAut.conj (wA F) * MulAut.conj (wA F) = 1 := by
  rw [← map_mul, wA_mul_wA, conj_neg_one]

theorem cB_sq (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    MulAut.conj (wB a b h) * MulAut.conj (wB a b h) = 1 := by
  rw [← map_mul, wB_mul_wB, conj_neg_one]

theorem cA_cB_comm (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    MulAut.conj (wA F) * MulAut.conj (wB a b h) = MulAut.conj (wB a b h) * MulAut.conj (wA F) := by
  rw [← map_mul, ← map_mul, wA_mul_wB, conj_neg_one_mul]

theorem cA_ne_one : MulAut.conj (wA F) ≠ 1 :=
  conj_ne_one (wA_ne_one_ne_neg_one).1 (wA_ne_one_ne_neg_one).2

theorem cB_ne_one (h2 : (2 : F) ≠ 0) (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    MulAut.conj (wB a b h) ≠ 1 :=
  conj_ne_one (wB_ne_one_ne_neg_one h2 a b h).1 (wB_ne_one_ne_neg_one h2 a b h).2

theorem cA_cB_ne_one (h2 : (2 : F) ≠ 0) (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    MulAut.conj (wA F) * MulAut.conj (wB a b h) ≠ 1 := by
  rw [← map_mul]
  exact conj_ne_one (wA_mul_wB_ne_one_ne_neg_one h2 a b h).1
    (wA_mul_wB_ne_one_ne_neg_one h2 a b h).2

end ElementsAut

section Closure

variable {H : Type*} [Group H]

theorem isPGroup_two_closure_of_comm_sq {S : Set H} (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hs : ∀ x ∈ S, x * x = 1) : IsPGroup 2 (Subgroup.closure S) := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => hc h hh x hx
  have hcomm : ∀ y ∈ Subgroup.closure S, ∀ y' ∈ Subgroup.closure S, y' * y = y * y' := by
    intro y hy y' hy'
    have h1 : y ∈ Subgroup.centralizer (Subgroup.closure S : Set H) := by
      rw [Subgroup.centralizer_closure]
      exact hle hy
    exact Subgroup.mem_centralizer_iff.mp h1 y' hy'
  have hsq : ∀ y ∈ Subgroup.closure S, y * y = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hs x hx
    | one => simp
    | mul x y hx hy hx2 hy2 =>
      have hc' := hcomm x hx y hy
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hc']
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    | inv x hx hx2 =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [hx2, inv_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using hsq g g.2

end Closure

section Card

variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
theorem finite_ringAut (F : Type*) [Field F] [Finite F] : Finite (F ≃+* F) :=
  Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))

theorem two_mul_natCard_le_of_le_inn (hF : Odd (Nat.card F)) (Q : Sylow 2 SL(2, F))
    {U : Subgroup (MulAut SL(2, F))}
    (hU : U ≤ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range) (hU2 : IsPGroup 2 U) :
    2 * Nat.card U ≤ Nat.card Q := by
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  have hdvd : Nat.card U ∣ Nat.card (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range :=
    Subgroup.card_dvd_of_le hU
  have hInn := CFSG.ClassicalInvolution.natCard_conj_range_of_equiv_sl2 hF
    (MulEquiv.refl SL(2, F))
  have hQ : Nat.card Q = 2 ^ (Nat.card SL(2, F)).factorization 2 := Sylow.card_eq_multiplicity Q
  have hpos : Nat.card (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range ≠ 0 := Nat.card_pos.ne'
  have hk' : k ≤ (Nat.card (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range).factorization 2 := by
    rw [hk] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp hdvd
  have hfac : (Nat.card SL(2, F)).factorization 2 =
      (Nat.card (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range).factorization 2 + 1 := by
    rw [← hInn, Nat.factorization_mul hpos (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  rw [hk, hQ, hfac, pow_succ]
  have : 2 ^ k ≤ 2 ^ (Nat.card (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) hk'
  omega

theorem two_mul_natCard_le_of_le_gamma (hF : Odd (Nat.card F)) (hK : IsOddPrimePower (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (Q : Sylow 2 SL(2, F)) {Γ P : Subgroup (MulAut SL(2, F))}
    (hΓ : Γ ≤ (slEps F hK).ker) (hPΓ : P ≤ Γ) (hP2 : IsPGroup 2 P) :
    2 * Nat.card P ≤ Nat.card (Γ.map (slRho F)) * Nat.card Q := by
  set φ : ↥P →* (F ≃+* F) := (slRho F).comp P.subtype with hφ
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card P := Subgroup.card_ker_mul_card_range φ
  set Kr : Subgroup (MulAut SL(2, F)) := φ.ker.map P.subtype with hKr
  have hKrle : Kr ≤ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : slRho F (x : MulAut SL(2, F)) = 1 := hx
    have hε : slEps F hK (x : MulAut SL(2, F)) = 1 := hΓ (hPΓ x.2)
    exact (slEps_slRho_eq_one_iff F hK h4 _).mp ⟨hε, hx1⟩
  have hKr2 : IsPGroup 2 Kr := hP2.to_le (Subgroup.map_subtype_le _)
  have h2 := two_mul_natCard_le_of_le_inn hF Q hKrle hKr2
  have hcard : Nat.card Kr = Nat.card φ.ker := Subgroup.card_map_of_injective P.subtype_injective
  have h3 : Nat.card φ.range ≤ Nat.card (Γ.map (slRho F)) := by
    have := finite_ringAut F
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    exact ⟨x, hPΓ x.2, rfl⟩
  calc 2 * Nat.card P = 2 * (Nat.card φ.ker * Nat.card φ.range) := by rw [h1]
    _ = (2 * Nat.card Kr) * Nat.card φ.range := by rw [hcard]; ring
    _ ≤ Nat.card Q * Nat.card (Γ.map (slRho F)) := Nat.mul_le_mul h2 h3
    _ = Nat.card (Γ.map (slRho F)) * Nat.card Q := mul_comm _ _

end Card

section A2

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem finite_mulAut_sl2 (F : Type) [Field F] [Finite F] : Finite (MulAut SL(2, F)) :=
  Finite.of_injective (fun e : MulAut SL(2, F) => (e : SL(2, F) → SL(2, F)))
    (fun _ _ h => MulEquiv.ext (congrFun h))

theorem slEps_ne_one_of_orderOf (hF : Odd (Nat.card F)) (hK : IsOddPrimePower (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (Q : Sylow 2 SL(2, F)) {β : MulAut SL(2, F)}
    (hβ2 : IsInnerAut (β * β)) (hord : 2 * orderOf β = Nat.card Q) : slEps F hK β ≠ 1 := by
  intro hε
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF
  have := finite_ringAut F
  have := finite_mulAut_sl2 F
  obtain ⟨-, hρ2⟩ := (slEps_slRho_eq_one_iff F hK h4 (β * β)).mpr hβ2
  set σ : F ≃+* F := slRho F β with hσ
  have hσ2 : σ * σ = 1 := by rwa [map_mul] at hρ2
  set Γ : Subgroup (MulAut SL(2, F)) :=
    (slEps F hK).ker ⊓ (Subgroup.zpowers σ).comap (slRho F) with hΓ
  have hΓle : Γ ≤ (slEps F hK).ker := inf_le_left
  have hmemΓ : ∀ x, slEps F hK x = 1 → slRho F x ∈ Subgroup.zpowers σ → x ∈ Γ :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hβΓ : β ∈ Γ := hmemΓ β hε (Subgroup.mem_zpowers σ)
  have hrange : Γ.map (slRho F) ≤ Subgroup.zpowers σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hr : Nat.card (Γ.map (slRho F)) ≤ orderOf σ := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_le_of_le hrange
  have hQ : Nat.card Q = 2 ^ (Nat.card SL(2, F)).factorization 2 := Sylow.card_eq_multiplicity Q
  have hordpos : 0 < orderOf β := orderOf_pos β
  have hB2 : IsPGroup 2 (Subgroup.zpowers β) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf β ∣ 2 ^ (Nat.card SL(2, F)).factorization 2 from
        ⟨2, by rw [← hQ, ← hord]; ring⟩)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hBΓ : Subgroup.zpowers β ≤ Γ := Subgroup.zpowers_le.mpr hβΓ
  obtain ⟨P, hP, hBP⟩ := IsSylow2In.exists_ge hB2 hBΓ
  have hcardP := two_mul_natCard_le_of_le_gamma hF hK h4 Q hΓle hP.1 hP.2.1
  have hrel : (Subgroup.zpowers β).relIndex P * orderOf β = Nat.card P := by
    have := Subgroup.relIndex_mul_card (Subgroup.zpowers β) P
    rwa [inf_eq_left.mpr hBP, Nat.card_zpowers] at this
  have hrelle : (Subgroup.zpowers β).relIndex P ≤ orderOf σ := by
    by_contra hlt
    have hlt' : orderOf σ < (Subgroup.zpowers β).relIndex P := not_le.mp hlt
    have h1 : orderOf σ * orderOf β < Nat.card P := by
      rw [← hrel]
      exact Nat.mul_lt_mul_of_pos_right hlt' hordpos
    have h3 : Nat.card (Γ.map (slRho F)) * Nat.card Q ≤ orderOf σ * (2 * orderOf β) := by
      rw [← hord]
      exact Nat.mul_le_mul_right _ hr
    have hmul : orderOf σ * (2 * orderOf β) = 2 * (orderOf σ * orderOf β) := by ring
    omega
  obtain ⟨a, b, hab, ha, hb⟩ := exists_sq_add_sq_neg_one_fixed hF σ
  set x₁ : MulAut SL(2, F) := MulAut.conj (wA F) with hx₁
  set x₂ : MulAut SL(2, F) := MulAut.conj (wB a b hab) with hx₂
  have hx₁sq : x₁ * x₁ = 1 := cA_sq
  have hx₂sq : x₂ * x₂ = 1 := cB_sq a b hab
  have hx₁₂ : x₁ * x₂ = x₂ * x₁ := cA_cB_comm a b hab
  have hn₁ : x₁ ≠ 1 := cA_ne_one
  have hn₂ : x₂ ≠ 1 := cB_ne_one h2 a b hab
  have hn₁₂ : x₁ * x₂ ≠ 1 := cA_cB_ne_one h2 a b hab
  have hd₁₂ : x₁ ≠ x₂ := fun h => hn₁₂ (by rw [← h]; exact hx₁sq)
  have hρ₁ : slRho F x₁ = 1 := slRho_conj F _
  have hρ₂ : slRho F x₂ = 1 := slRho_conj F _
  have hx₁Γ : x₁ ∈ Γ := hmemΓ x₁ (slEps_conj F hK _) (by rw [hρ₁]; exact Subgroup.one_mem _)
  have hx₂Γ : x₂ ∈ Γ := hmemΓ x₂ (slEps_conj F hK _) (by rw [hρ₂]; exact Subgroup.one_mem _)
  by_cases hσ1 : σ = 1
  · have hrel1 : (Subgroup.zpowers β).relIndex P = 1 := by
      have h1 : orderOf σ = 1 := by rw [hσ1]; exact orderOf_one
      have hpos : (Subgroup.zpowers β).relIndex P ≠ 0 := by
        show ((Subgroup.zpowers β).subgroupOf P).index ≠ 0
        exact Subgroup.index_ne_zero_of_finite
      omega
    have hPB : P ≤ Subgroup.zpowers β := Subgroup.relIndex_eq_one.mp hrel1
    have hE₀2 : IsPGroup 2 (Subgroup.closure ({x₁, x₂} : Set (MulAut SL(2, F)))) := by
      apply isPGroup_two_closure_of_comm_sq
      · intro x hx y hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          first | rfl | assumption | exact hx₁₂.symm
      · intro x hx
        rcases hx with rfl | rfl <;> assumption
    have hE₀Γ : Subgroup.closure ({x₁, x₂} : Set (MulAut SL(2, F))) ≤ Γ := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl <;> assumption
    obtain ⟨P', hP', hE₀P'⟩ := IsSylow2In.exists_ge hE₀2 hE₀Γ
    obtain ⟨g, -, hgP⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP' hP
    have hy : ∀ x ∈ Subgroup.closure ({x₁, x₂} : Set (MulAut SL(2, F))), g * x * g⁻¹ ∈ P :=
      fun x hx => hgP ▸ conj_mem_conjSub (hE₀P' hx)
    have hy₁ := hy x₁ (Subgroup.subset_closure (by simp))
    have hy₂ := hy x₂ (Subgroup.subset_closure (by simp))
    refine false_of_two_involutions hPB hy₁ hy₂ ?_ ?_ ?_ ?_ ?_
    · rw [conj_mul_conj, hx₁sq]; group
    · rw [conj_mul_conj, hx₂sq]; group
    · exact fun h => hn₁ (conj_eq_one_iff'.mp h)
    · exact fun h => hn₂ (conj_eq_one_iff'.mp h)
    · exact fun h => hd₁₂ (conj_inj'.mp h)
  · have hσord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
    set f : MulAut SL(2, F) := slFieldAut F σ with hf
    have hρf : slRho F f = σ := slRho_slFieldAut F σ
    have hfΓ : f ∈ Γ :=
      hmemΓ f (slEps_slFieldAut F hK σ) (by rw [hρf]; exact Subgroup.mem_zpowers σ)
    have hfsq : f * f = 1 := by rw [hf, ← slFieldAut_mul, hσ2, slFieldAut_one]
    have hf₁ : f * x₁ = x₁ * f := slFieldAut_comm_conj σ (wA F) (slFieldAut_wA σ)
    have hf₂ : f * x₂ = x₂ * f := slFieldAut_comm_conj σ _ (slFieldAut_wB σ a b hab ha hb)
    have hnf : f ≠ 1 := fun h => hσ1 (by rw [h, map_one] at hρf; exact hρf.symm)
    have hd₁f : x₁ ≠ f := fun h => hσ1 (by rw [← hρf, ← h, hρ₁])
    have hd₂f : x₂ ≠ f := fun h => hσ1 (by rw [← hρf, ← h, hρ₂])
    have hprod : x₁ * x₂ * f ≠ 1 := fun h => hσ1 (by
      have := congrArg (slRho F) h
      rwa [map_mul, map_mul, hρ₁, hρ₂, hρf, one_mul, one_mul, map_one] at this)
    have hE₁2 : IsPGroup 2 (Subgroup.closure ({x₁, x₂, f} : Set (MulAut SL(2, F)))) := by
      apply isPGroup_two_closure_of_comm_sq
      · intro x hx y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first | rfl | assumption | exact hx₁₂.symm | exact hf₁.symm | exact hf₂.symm
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    have hE₁Γ : Subgroup.closure ({x₁, x₂, f} : Set (MulAut SL(2, F))) ≤ Γ := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    obtain ⟨P', hP', hE₁P'⟩ := IsSylow2In.exists_ge hE₁2 hE₁Γ
    obtain ⟨g, -, hgP⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP' hP
    have hy : ∀ x ∈ Subgroup.closure ({x₁, x₂, f} : Set (MulAut SL(2, F))), g * x * g⁻¹ ∈ P :=
      fun x hx => hgP ▸ conj_mem_conjSub (hE₁P' hx)
    have hy₁ := hy x₁ (Subgroup.subset_closure (by simp))
    have hy₂ := hy x₂ (Subgroup.subset_closure (by simp))
    have hy₃ := hy f (Subgroup.subset_closure (by simp))
    refine false_of_three_involutions (β := β) (hrelle.trans hσord.le) hy₁ hy₂ hy₃ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [conj_mul_conj, conj_mul_conj, hx₁₂]
    · rw [conj_mul_conj, conj_mul_conj, hf₁.symm]
    · rw [conj_mul_conj, conj_mul_conj, hf₂.symm]
    · rw [conj_mul_conj, hx₁sq]; group
    · rw [conj_mul_conj, hx₂sq]; group
    · rw [conj_mul_conj, hfsq]; group
    · exact fun h => hn₁ (conj_eq_one_iff'.mp h)
    · exact fun h => hn₂ (conj_eq_one_iff'.mp h)
    · exact fun h => hnf (conj_eq_one_iff'.mp h)
    · exact fun h => hd₁₂ (conj_inj'.mp h)
    · exact fun h => hd₁f (conj_inj'.mp h)
    · exact fun h => hd₂f (conj_inj'.mp h)
    · rw [conj_mul_conj, conj_mul_conj]
      exact fun h => hprod (conj_eq_one_iff'.mp h)

end A2

section LemmaB

variable {F : Type} [Field F] [Finite F]

theorem two_mul_natCard_map_conj (hF : Odd (Nat.card F)) (Q : Sylow 2 SL(2, F))
    {Rs : Subgroup SL(2, F)} (hRs2 : IsPGroup 2 Rs) (hRs : Nat.card Rs = Nat.card Q) :
    2 * Nat.card (Rs.map (MulAut.conj : SL(2, F) →* MulAut SL(2, F))) = Nat.card Q := by
  have hle := two_mul_natCard_le_of_le_inn hF Q
    (U := Rs.map (MulAut.conj : SL(2, F) →* MulAut SL(2, F)))
    (fun x ⟨y, _, hy⟩ => ⟨y, hy⟩) (hRs2.map _)
  set φ : ↥Rs →* MulAut SL(2, F) :=
    (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).comp Rs.subtype with hφ
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card Rs := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range = Rs.map (MulAut.conj : SL(2, F) →* MulAut SL(2, F)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : Nat.card φ.ker ≤ 2 := by
    have hsub : φ.ker.map Rs.subtype ≤ Subgroup.center SL(2, F) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : MulAut.conj (x : SL(2, F)) = 1 := hx
      exact (conj_eq_one_iff _).mp hx1
    have hc := CFSG.ClassicalInvolution.sl2_natCard_center hF
    have h2 := Subgroup.card_le_of_le hsub
    rw [Subgroup.card_map_of_injective Rs.subtype_injective, hc] at h2
    exact h2
  rw [hrange] at h1
  have h3 := Nat.mul_le_mul_right (Nat.card (Rs.map (MulAut.conj : SL(2, F) →* MulAut SL(2, F))))
    hker
  omega

end LemmaB

end CFSG.ClassicalInvolution.Asc77.T3CII
