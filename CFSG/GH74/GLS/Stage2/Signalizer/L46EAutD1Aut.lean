module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F] [Finite F]

theorem ringAut_sq_of_card_four (hF4 : Nat.card F = 4) (σ : F ≃+* F) : σ * σ = 1 := by
  have h := (card_ringAut_and_isCyclic Nat.prime_two F (by rw [hF4]; norm_num : Nat.card F = 2 ^ 2)).1
  have : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have h2 : σ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut F) (x := σ)
    rwa [h] at this
  rwa [pow_two] at h2

theorem sq_mem_linearAutGroup (hσ : ∀ σ : F ≃+* F, σ * σ = 1) (β : MulAut (projectiveSL 3 F)) :
    β * β ∈ linearAutGroup 3 F := by
  classical
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβ'⟩ := hform β
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hδδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hβ'
    rw [hβ', conjAut_mul_fieldAut_mul, hσ σ, map_one, mul_one]
    exact conjAut_mem_linearAutGroup _
  · rw [pow_one] at hβ'
    set δ := dualAut 3 F with hδ
    have key : δ * conjAut 3 F A * δ * (δ * fieldAut 3 F σ * δ) =
        δ * conjAut 3 F A * fieldAut 3 F σ * δ := by
      calc δ * conjAut 3 F A * δ * (δ * fieldAut 3 F σ * δ)
          = δ * conjAut 3 F A * (δ * δ) * fieldAut 3 F σ * δ := by group
        _ = δ * conjAut 3 F A * fieldAut 3 F σ * δ := by rw [hδδ]; group
    have hA' : δ * conjAut 3 F A * δ = conjAut 3 F (GeneralLinearGroup.inverseTranspose A) :=
      htrans.2.2.2.2.1 A
    have hf' : δ * fieldAut 3 F σ * δ = fieldAut 3 F σ := htrans.2.2.2.2.2.1 σ
    have h1 : β * β = (conjAut 3 F A * fieldAut 3 F σ) *
        (conjAut 3 F (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 F σ) := by
      rw [hβ']
      calc conjAut 3 F A * fieldAut 3 F σ * δ * (conjAut 3 F A * fieldAut 3 F σ * δ)
          = conjAut 3 F A * fieldAut 3 F σ * (δ * conjAut 3 F A * fieldAut 3 F σ * δ) := by group
        _ = conjAut 3 F A * fieldAut 3 F σ *
            (δ * conjAut 3 F A * δ * (δ * fieldAut 3 F σ * δ)) := by rw [key]
        _ = _ := by rw [hA', hf']
    rw [h1, conjAut_mul_fieldAut_mul, hσ σ, map_one, mul_one]
    exact conjAut_mem_linearAutGroup _

theorem mem_linearAutGroup_of_odd_pow (hσ : ∀ σ : F ≃+* F, σ * σ = 1) {β : MulAut (projectiveSL 3 F)}
    {m : ℕ} (hm : Odd m) (hβ : β ^ m = 1) : β ∈ linearAutGroup 3 F := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : β ^ (2 * k + 1) = β * (β * β) ^ k := by
    rw [pow_succ', pow_mul, pow_two]
  rw [h2] at hβ
  have : β = ((β * β) ^ k)⁻¹ := eq_inv_iff_mul_eq_one.2 hβ
  rw [this]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (sq_mem_linearAutGroup hσ β) k)


open Matrix.ProjGenLinGroup in
@[expose] noncomputable def pglToAut (F : Type) [Field F] :
    Matrix.ProjGenLinGroup (Fin 3) F →* MulAut (projectiveSL 3 F) :=
  lift (conjAut 3 F) (MonoidHom.ext fun u => conjAut_scalar u)

omit [Finite F] in
open Matrix.ProjGenLinGroup in
theorem pglToAut_mk (A : GL (Fin 3) F) : pglToAut F (mk A) = conjAut 3 F A :=
  lift_mk _ A

open Matrix.ProjGenLinGroup in
theorem pglToAut_injective : Function.Injective (pglToAut F) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨A, rfl⟩ := mk_surjective x
  rw [pglToAut_mk] at hx
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) A 1
    (by rw [map_one, mul_one, hx])
  rw [← hc, mk_scalar]

omit [Finite F] in
open Matrix.ProjGenLinGroup in
theorem range_pglToAut : (pglToAut F).range = linearAutGroup 3 F := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨A, rfl⟩ := mk_surjective x
    rw [pglToAut_mk]
    exact conjAut_mem_linearAutGroup A
  · rw [linearAutGroup, Subgroup.closure_le]
    rintro _ ⟨A, rfl⟩
    exact ⟨mk A, pglToAut_mk A⟩


omit [Finite F] in
theorem isSimpleGroup_P3 : IsSimpleGroup (projectiveSL 3 F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega) (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup

omit [Finite F] in
theorem isPerfect_P3 : Group.IsPerfect (projectiveSL 3 F) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (scalars 3 F))

omit [Finite F] in
theorem center_P3_eq_bot : center (projectiveSL 3 F) = ⊥ := by
  have := isSimpleGroup_P3 (F := F)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (projectiveSL 3 F)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : projectiveSL 3 F, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a
    have h1 : commutator (projectiveSL 3 F) = ⊥ := by
      rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm a b
    have h2 := (isPerfect_P3 (F := F)).commutator_eq_top
    rw [h1] at h2
    exact bot_ne_top h2

@[expose] def Iaut (F : Type) [Field F] : Subgroup (MulAut (projectiveSL 3 F)) :=
  (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range

omit [Finite F] in
theorem mulAut_mul_conj_mul_inv (θ : MulAut (projectiveSL 3 F)) (x : projectiveSL 3 F) :
    θ * MulAut.conj x * θ⁻¹ = MulAut.conj (θ x) := by
  ext y
  simp [MulAut.conj_apply]

omit [Finite F] in
theorem eq_one_of_commute_conj {θ : MulAut (projectiveSL 3 F)}
    (h : ∀ x, θ * MulAut.conj x = MulAut.conj x * θ) : θ = 1 := by
  ext x
  have h1 : MulAut.conj (θ x) = MulAut.conj x := by
    rw [← mulAut_mul_conj_mul_inv, h x]
    group
  have h2 : (θ x)⁻¹ * x ∈ center (projectiveSL 3 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ g) h1
    simp only [MulAut.conj_apply] at this
    calc g * ((θ x)⁻¹ * x) = (θ x)⁻¹ * (θ x * g * (θ x)⁻¹) * x := by group
      _ = (θ x)⁻¹ * (x * g * x⁻¹) * x := by rw [this]
      _ = ((θ x)⁻¹ * x) * g := by group
  rw [center_P3_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h2
  simp [h2]

omit [Finite F] in
theorem Iaut_perfect : Group.IsPerfect (Iaut F) := by
  have := isPerfect_P3 (F := F)
  exact Group.IsPerfect.ofSurjective
    (f := (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).rangeRestrict)
    (MonoidHom.rangeRestrict_surjective _)

theorem Iaut_le_D : Iaut F ≤ linearAutGroup 3 F :=
  (standard_outer_quotients (K := F) (n := 3)).1

theorem comm_mem_Iaut {a b : MulAut (projectiveSL 3 F)} (ha : a ∈ linearAutGroup 3 F)
    (hb : b ∈ linearAutGroup 3 F) : a * b * a⁻¹ * b⁻¹ ∈ Iaut F :=
  (standard_outer_quotients (K := F) (n := 3)).2.2.2.2.1 a ha b hb

theorem commutator_D_eq_Iaut : ⁅linearAutGroup 3 F, linearAutGroup 3 F⁆ = Iaut F := by
  apply le_antisymm
  · exact Subgroup.commutator_le.mpr fun a ha b hb => comm_mem_Iaut ha hb
  · have h := (Iaut_perfect (F := F)).commutator_eq_top
    calc Iaut F = ⁅Iaut F, Iaut F⁆ := by
          rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ ≤ ⁅linearAutGroup 3 F, linearAutGroup 3 F⁆ :=
          Subgroup.commutator_mono Iaut_le_D Iaut_le_D


theorem mem_Iaut_of_coprime_three (hF4 : Nat.card F = 4) {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∈ linearAutGroup 3 F) {m : ℕ} (hm : Nat.Coprime m 3) (hθm : θ ^ m = 1) :
    θ ∈ Iaut F := by
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hθ
  rw [← map_pow] at hθm
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (A ^ m) 1
    (by rw [map_one, mul_one]; exact hθm)
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF4]
  have hc3 : c ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Fˣ) (x := c)
    rwa [hcard] at this
  have h1 : (GeneralLinearGroup.det A) ^ m = c ^ 3 := by
    rw [← map_pow, ← hc, GeneralLinearGroup.det_scalar]
    simp
  have hdm : (GeneralLinearGroup.det A) ^ m = 1 := by rw [h1, hc3]
  have hd3 : (GeneralLinearGroup.det A) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Fˣ) (x := GeneralLinearGroup.det A)
    rwa [hcard] at this
  have hd : GeneralLinearGroup.det A = 1 := by
    have h2 : orderOf (GeneralLinearGroup.det A) ∣ m := orderOf_dvd_of_pow_eq_one hdm
    have h3 : orderOf (GeneralLinearGroup.det A) ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hm) h3)
  have hA : A ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hd
  obtain ⟨g, rfl⟩ := hA
  exact ⟨proj 3 F g, (conjAut_toGL g).symm⟩


omit [Finite F] in
theorem conj_injective_P3 : Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h : ∀ g : projectiveSL 3 F, g * x = x * g := by
    intro g
    have := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = (x * g * x⁻¹) * x := by rw [this]
      _ = x * g := by group
  have : x ∈ center (projectiveSL 3 F) := Subgroup.mem_center_iff.2 fun g => h g
  rw [center_P3_eq_bot, Subgroup.mem_bot] at this
  exact this

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
