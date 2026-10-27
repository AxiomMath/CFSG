module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeX
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTNormalDescent
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Chevalley.E6GraphLevi (realize unitarySL unitaryTwist antiId)
open CFSG.SeitzReduction.UnitaryPilot (toPSL graphFieldAut graphFieldSL barRingEquiv)

section Kernel

variable {K : Type} [Field K]

theorem ker_realizeA_eq_scalars [CharP K 2] (h2 : (2 : K) = 0) :
    (realizeA h2).ker = LinearFlag.scalars 6 K := by
  ext B
  have hker : B ∈ (realizeA h2).ker ↔ B ∈ (realize h2).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hker, E6GraphLevi.mem_ker_realize, LinearFlag.mem_scalars]
  constructor
  · rintro ⟨l, hl3, hB⟩
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hl3
    refine ⟨Units.mk0 l hl0, ?_, hB⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
      show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hl3, one_pow]
  · rintro ⟨c, hc6, hB⟩
    refine ⟨(c : K), ?_, hB⟩
    have h6 : ((c : K) ^ 3) * ((c : K) ^ 3) = 1 := by
      rw [← pow_add, show 3 + 3 = 6 by norm_num, ← Units.val_pow_eq_pow_val, hc6, Units.val_one]
    exact d4_eq_one_of_mul_self_eq_one h6

@[expose] noncomputable def projectiveSLEquivA5 [CharP K 2] (h2 : (2 : K) = 0) :
    LinearFlag.projectiveSL 6 K ≃* subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA :=
  (QuotientGroup.quotientMulEquivOfEq (ker_realizeA_eq_scalars h2).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (realizeA h2) (realizeA_surjective h2))

theorem projectiveSLEquivA5_proj [CharP K 2] (h2 : (2 : K) = 0) (B : SpecialLinearGroup (Fin 6) K) :
    projectiveSLEquivA5 h2 (LinearFlag.proj 6 K B) = realizeA h2 B :=
  rfl

end Kernel

section Witt

variable {K : Type} [Field K]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem exists_witt_antiId [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ P : GL (Fin 6) K,
      ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * (P : Matrix (Fin 6) (Fin 6) K) = antiId K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := 2) (f := f) hK 6
  refine ⟨P, ?_⟩
  rw [← E6GraphLevi.conjTr_unitaryInvolution hσ]
  exact hP

theorem witt_identities {σ : K →+* K} {P : GL (Fin 6) K}
    (hP : ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * (P : Matrix (Fin 6) (Fin 6) K) = antiId K) :
    antiId K * ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ =
        ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ∧
      (((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K =
        (P : Matrix (Fin 6) (Fin 6) K) := by
  have hPP : (P : Matrix (Fin 6) (Fin 6) K) * ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (P : Matrix (Fin 6) (Fin 6) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJJ : antiId K * antiId K = 1 := E6GraphLevi.antiId_mul_self
  have h1 : ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ =
      antiId K * ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [← hP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  refine ⟨by rw [h1, ← Matrix.mul_assoc, hJJ, Matrix.one_mul], ?_⟩
  have h2 : (((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ *
      ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  rw [h1, ← Matrix.mul_assoc] at h2
  calc (((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K =
        (((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K *
          (((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (P : Matrix (Fin 6) (Fin 6) K)) := by
        rw [hPP', Matrix.mul_one]
    _ = ((((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K *
          ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * (P : Matrix (Fin 6) (Fin 6) K) := by
        simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin 6) (Fin 6) K) := by rw [h2, Matrix.one_mul]

theorem unitaryTwist_slConjugation {f : ℕ} (h : UnitaryFieldData 2 f K) {σ : K →+* K}
    (hbar : ∀ c, h.bar c = σ c) {P : GL (Fin 6) K}
    (hP : ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * (P : Matrix (Fin 6) (Fin 6) K) = antiId K)
    (B : SpecialLinearGroup (Fin 6) K) :
    unitaryTwist σ (slConjugation 6 K P⁻¹ B) = slConjugation 6 K P⁻¹ (graphFieldSL h 6 B) := by
  obtain ⟨hJ1, hJ2⟩ := witt_identities hP
  have hmap : h.bar = σ := RingHom.ext hbar
  apply Subtype.ext
  change antiId K * (((Matrix.SpecialLinearGroup.map σ (slConjugation 6 K P⁻¹ B))⁻¹ :
    SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * antiId K = _
  rw [← map_inv, ← map_inv, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, inv_inv,
    UnitaryPilot.graphFieldSL_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.transpose_mul]
  have hb : (barRingEquiv h).toRingHom = σ := by
    ext c
    exact hbar c
  rw [Matrix.SpecialLinearGroup.coe_transpose, hb, Matrix.transpose_map]
  calc antiId K * (((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ *
        ((((B⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ *
          (((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ)) * antiId K =
        (antiId K * ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ) *
          (((B⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ *
          ((((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ1, hJ2]

end Witt

section Transport

variable {A₁ A₂ M₁ M₂ : Type*} [Group A₁] [Group A₂] [Group M₁] [Group M₂]

theorem autExtensionComm_of_mulEquiv (Ξ : M₁ ≃* M₂) {θ₁ : MulAut M₁} {θ₂ : MulAut M₂}
    (hΞ : MulAut.congr Ξ θ₁ = θ₂) {j₁ : A₁ →* M₁} {j₂ : A₂ →* M₂} (e : A₁ ≃* A₂)
    (hj : ∀ a, Ξ (j₁ a) = j₂ (e a)) (h : AutExtensionComm j₁ θ₁) : AutExtensionComm j₂ θ₂ := by
  intro δ
  obtain ⟨δ₁', hδ₁', hcomm⟩ := h (MulAut.congr e.symm δ)
  refine ⟨MulAut.congr Ξ δ₁', fun b => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective b
    change Ξ (δ₁' (Ξ.symm (j₂ (e a)))) = j₂ (δ (e a))
    rw [← hj, MulEquiv.symm_apply_apply, hδ₁', hj]
    change j₂ (e (e.symm (δ (e.symm.symm a)))) = j₂ (δ (e a))
    rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  · rw [← hΞ, ← map_mul, ← map_mul, hcomm]

theorem involutionDescentComp_of_mulEquiv (Ξ : M₁ ≃* M₂) {θ₁ : MulAut M₁} {θ₂ : MulAut M₂}
    (hΞ : MulAut.congr Ξ θ₁ = θ₂) (eA : A₁ ≃* A₂) (h : InvolutionDescentComp θ₁ A₁) :
    InvolutionDescentComp θ₂ A₂ := by
  intro β hββ ⟨C, hC, ⟨eC⟩⟩
  set β₁ : MulAut M₁ := MulAut.congr Ξ.symm β with hβ₁def
  have hβ₁β₁ : β₁ * β₁ = 1 := by rw [hβ₁def, ← map_mul, hββ, map_one]
  have hfix : fixedSubgroup β₁ = (fixedSubgroup β).map Ξ.symm.toMonoidHom :=
    fixedSubgroup_mulAutCongr Ξ.symm β
  set eFix : fixedSubgroup β ≃* fixedSubgroup β₁ :=
    ((fixedSubgroup β).equivMapOfInjective _ Ξ.symm.injective).trans
      (MulEquiv.subgroupCongr hfix.symm) with heFix
  obtain ⟨ψ₁, hψ₁⟩ := h β₁ hβ₁β₁ ⟨C.map eFix.toMonoidHom,
    CFSG.LocalCores.isComponent_map_mulEquiv eFix hC,
    ⟨((C.equivMapOfInjective _ eFix.injective).symm.trans eC).trans eA.symm⟩⟩
  have hback : MulAut.congr Ξ β₁ = β := MulEquiv.ext fun y => by
    change Ξ (Ξ.symm (β (Ξ.symm.symm (Ξ.symm y)))) = β y
    rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine ⟨MulAut.congr Ξ ψ₁, ?_⟩
  rw [← hback, ← map_mul, ← map_inv, ← map_mul, hψ₁, hΞ]

end Transport

section Model

variable
  {K : Type} [Field K]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

@[expose] noncomputable def modelEquivA5 [CharP K 2] (h2 : (2 : K) = 0) (P : GL (Fin 6) K) :
    LinearFlag.projectiveSL 6 K ≃* subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA :=
  (LinearFlag.conjAut 6 K P⁻¹).trans (projectiveSLEquivA5 h2)

theorem modelEquivA5_proj [CharP K 2] (h2 : (2 : K) = 0) (P : GL (Fin 6) K)
    (B : SpecialLinearGroup (Fin 6) K) :
    modelEquivA5 h2 P (LinearFlag.proj 6 K B) = realizeA h2 (slConjugation 6 K P⁻¹ B) := by
  rw [modelEquivA5, MulEquiv.trans_apply, LinearFlag.conjAut_proj, projectiveSLEquivA5_proj]

theorem congr_modelEquivA5_graphFieldAut {f : ℕ} (h : UnitaryFieldData 2 f K) [CharP K 2]
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (hbar : ∀ c, h.bar c = σ c)
    {P : GL (Fin 6) K}
    (hP : ((P : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * (P : Matrix (Fin 6) (Fin 6) K) = antiId K) :
    MulAut.congr (modelEquivA5 h2 P) (graphFieldAut h 6) = a5LeviTwist hσσ := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨B, rfl⟩ := realizeA_surjective h2 y
  change modelEquivA5 h2 P (graphFieldAut h 6 ((modelEquivA5 h2 P).symm (realizeA h2 B))) =
    a5LeviTwist hσσ (realizeA h2 B)
  have hB : realizeA h2 B = modelEquivA5 h2 P (LinearFlag.proj 6 K (slConjugation 6 K P B)) := by
    rw [modelEquivA5_proj, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      MulAut.one_apply]
  rw [hB, MulEquiv.symm_apply_apply, UnitaryPilot.graphFieldAut_proj, modelEquivA5_proj]
  apply Subtype.ext
  change realize h2 _ = twistHom TwistTag.E6 K σ (realize h2 (slConjugation 6 K P⁻¹
    (slConjugation 6 K P B)))
  rw [E6GraphLevi.twistHom_realize, unitaryTwist_slConjugation h hbar hP]

end Model

section Unitary

variable {f : ℕ} {K : Type} [Field K]

theorem autExtensionComm_toPSL (h : UnitaryFieldData 2 f K) :
    AutExtensionComm (toPSL h 6) (graphFieldAut h 6) := by
  intro δ
  obtain ⟨δ', hδ', hc⟩ := UnitaryPilot.exists_mulAut_toPSL_comm h (m := 6) (by norm_num)
    (fun h' => absurd h'.1 (by norm_num)) δ
  exact ⟨δ', hδ', hc.eq⟩

theorem involutionDescentComp_graphFieldAut (h : UnitaryFieldData 2 f K)
    (hlie : LieModel (unitaryPSU h 6) .PSU 6 2 f) :
    InvolutionDescentComp (graphFieldAut h 6) (unitaryPSU h 6) := by
  intro β hββ ⟨C, hC, ⟨eC⟩⟩
  obtain ⟨H, hH⟩ := UnitaryPilot.eq_conj_graphFieldAut_conj_inv_of_isComponent h (n := 6)
    (by norm_num) hββ hC (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eC.symm hlie)
  exact ⟨(LinearFlag.conjAut 6 K H)⁻¹, by rw [hH]; group⟩

end Unitary

section Consequences

variable
  {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem unitaryFieldData_twistedE6Field (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩

theorem commutator_su6Levi_subgroupOf (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ⁅(su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA),
      (su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)⁆ =
      (su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA) := by
  have hP := isPerfect_su6Levi hf hk hK hσ
  have e := subgroupOfEquivOfLe (su6Levi_le_subsystemGroup σ)
  have : Group.IsPerfect ((su6Levi σ).subgroupOf
      (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.1 this

theorem exists_model_equiv_a5Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ (h : UnitaryFieldData 2 f K)
      (Ξ : LinearFlag.projectiveSL 6 K ≃* subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)
      (eu : unitaryPSU h 6 ≃* (su6Levi σ).subgroupOf
        (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)),
      MulAut.congr Ξ (graphFieldAut h 6) = a5LeviTwist (apply_apply_eq hK hσ) ∧
        ∀ x, Ξ (toPSL h 6 x) = ((su6Levi σ).subgroupOf
          (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)).subtype (eu x) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have h2 : (2 : K) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hf hK
  set h := unitaryFieldData_twistedE6Field (K := K) hf hK with hhdef
  have hbar : ∀ c, h.bar c = σ c := fun c => by rw [UnitaryFieldData.bar_apply, hσ]
  obtain ⟨P, hP⟩ := exists_witt_antiId hK hσ
  set Ξ := modelEquivA5 h2 P with hΞdef
  have hc := congr_modelEquivA5_graphFieldAut h h2 (apply_apply_eq hK hσ) hbar hP
  set A' := (su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)
    with hA'def
  have hfixF : (fixedSubgroup (graphFieldAut h 6)).map Ξ.toMonoidHom = A' := by
    rw [← fixedSubgroup_mulAutCongr, hc, fixedSubgroup_a5LeviTwist hf hK hσ]
  have hperf : ⁅fixedSubgroup (graphFieldAut h 6), fixedSubgroup (graphFieldAut h 6)⁆ =
      fixedSubgroup (graphFieldAut h 6) := by
    apply Subgroup.map_injective (f := Ξ.toMonoidHom) Ξ.injective
    rw [map_commutator, hfixF]
    exact commutator_su6Levi_subgroupOf hf hk hK hσ
  have hrangeFix : (toPSL h 6).range = fixedSubgroup (graphFieldAut h 6) :=
    le_antisymm (UnitaryPilot.range_toPSL_le_fixedSubgroup h)
      (UnitaryPilot.le_range_toPSL_of_le_fixedSubgroup h hperf le_rfl)
  have hrange : (Ξ.toMonoidHom.comp (toPSL h 6)).range = A' := by
    rw [MonoidHom.range_comp, hrangeFix, hfixF]
  have hinj : Function.Injective (Ξ.toMonoidHom.comp (toPSL h 6)) :=
    Ξ.injective.comp (UnitaryPilot.toPSL_injective h)
  refine ⟨h, Ξ, (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), hc,
    fun x => ?_⟩
  rfl

theorem autExtensionComm_a5Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    AutExtensionComm
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)).subtype
      (a5LeviTwist (apply_apply_eq hK hσ)) := by
  obtain ⟨h, Ξ, eu, hc, hj⟩ := exists_model_equiv_a5Levi hf hk hK hσ
  exact autExtensionComm_of_mulEquiv Ξ hc eu hj (autExtensionComm_toPSL h)

theorem involutionDescentComp_a5Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    InvolutionDescentComp (a5LeviTwist (apply_apply_eq hK hσ))
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)) := by
  obtain ⟨h, Ξ, eu, hc, hj⟩ := exists_model_equiv_a5Levi hf hk hK hσ
  have hlie : LieModel (unitaryPSU h 6) .PSU 6 2 f :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (eu.trans (subgroupOfEquivOfLe (su6Levi_le_subsystemGroup σ))).symm
      (lieModel_su6Levi hf hk hK hσ)
  exact involutionDescentComp_of_mulEquiv Ξ hc eu (involutionDescentComp_graphFieldAut h hlie)

theorem nonempty_a5Levi_mulEquiv_of_projectiveSL (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {Kc : Type}
    [Group Kc] {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ (2 * f))
    (eK : Kc ≃* LinearFlag.projectiveSL 6 F) :
    Nonempty (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc) := by
  have := finite_of_card hK
  obtain ⟨-, Ξ, -, -, -⟩ := exists_model_equiv_a5Levi hf hk hK hσ
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card K = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF, ← pow_mul, mul_comm]
  exact ⟨Ξ.symm.trans ((CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
    (FiniteField.ringEquivOfCardEq hcard)).trans eK.symm)⟩

end Consequences

end CFSG.SeitzReduction.TwistedE6Pilot
