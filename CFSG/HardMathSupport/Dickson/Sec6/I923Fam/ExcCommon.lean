module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open scoped commutatorElement

section Entrywise


theorem fixSubgroup_entrywiseAdjointAut {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K) :
    fixSubgroup (entrywiseAdjointAut τ σ) =
      (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K) := by
  ext u
  change entrywiseAdjointAut τ σ u = u ↔ (u : ModGL τ K) ∈ entrywiseFixedGroup τ σ
  rw [mem_entrywiseFixedGroup]
  constructor
  · intro h
    exact ⟨u.2, (coe_entrywiseAdjointAut τ σ u).symm.trans (congrArg Subtype.val h)⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext ((coe_entrywiseAdjointAut τ σ u).trans h)

theorem noL2Layer_entrywise {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a)
    (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥(adjointGroup τ (fixSubfield σ))) :
    NoL2Layer (entrywiseAdjointAut τ σ) := by
  obtain ⟨-, hinj, -, hJΓ, -, hJnorm, hquot⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (hJΓ hx).1
  let S : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  let eJ : ↥(adjointGroup τ (fixSubfield σ)) ≃* ↥(fixedFieldImage τ σ) :=
    (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj
  let e : ↥S ≃* ↥(adjointGroup τ (fixSubfield σ)) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans eJ.symm
  haveI : IsSimpleGroup ↥S := e.isSimpleGroup
  refine noL2_of_simple_normal_comm _ S ?_ ?_ inferInstance ?_ ?_
  · rw [fixSubgroup_entrywiseAdjointAut]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hJΓ (Subgroup.mem_subgroupOf.1 hx))
  · rw [fixSubgroup_entrywiseAdjointAut]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    let N : Subgroup ↥(entrywiseFixedGroup τ σ) :=
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
    have hcN : ∀ x y : ↥(entrywiseFixedGroup τ σ), ⁅x, y⁆ ∈ N := by
      intro x y
      have h : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hquot _ _)
      exact (QuotientGroup.eq_one_iff _).1 h
    have h1 := hcN ⟨(a : ModGL τ K), Subgroup.mem_subgroupOf.1 ha⟩
      ⟨(b : ModGL τ K), Subgroup.mem_subgroupOf.1 hb⟩
    rw [Subgroup.mem_subgroupOf] at h1 ⊢
    simpa [commutatorElement_def] using h1
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  · intro r hr hT
    exact hL2 r hr (l2fld_isTypeL2_of_mulEquiv e hT)

theorem noL2Layer_entrywise_of_model
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {τ : Tag} {t : StatedLieTag} (ht : t ≠ .Tits) (htPSL : t ≠ .PSL) {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) {ℓ d : ℕ}
    (hX : LieModel ↥(adjointGroup τ (fixSubfield σ)) t 0 ℓ d)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a)
    (hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥) :
    NoL2Layer (entrywiseAdjointAut τ σ) :=
  noL2Layer_entrywise σ hs hnab fun _ hr =>
    not_typeL2_of_lieModel hO hX.admissible hX ht (fun h => htPSL h.1) hZ hr

end Entrywise

theorem exists_equiv_adjointGroup_of_untwisted
    {P : Type} [Group P] {τ : Tag} {q : ℕ} (h : UntwistedChevalleyModel P τ q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (P ≃* ↥(adjointGroup τ F)) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hF, hFin, hcard, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
    center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)⟩⟩

theorem untwisted_adjointGroup
    {τ : Tag} {k : Type} [Field k] [Finite k] {q : ℕ} (hk : Nat.card k = q) :
    UntwistedChevalleyModel ↥(adjointGroup τ k) τ q :=
  ⟨k, inferInstance, inferInstance, hk, ⟨((QuotientGroup.quotientMulEquivOfEq
    center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot).symm⟩⟩

end CFSG.HardMathSupport.Dickson.Sec6.I923
