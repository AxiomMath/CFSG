module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {k : Type} [Field k] {ι : Type}

theorem finiteIndex_familyGroup_inf_centralizer (a : ι → Fin τ.rank → kˣ)
    {Hh : Subgroup (ModGL τ k)} (ha : ∀ i, rootDiagUnit τ (a i) ∈ Hh) :
    ((familyGroup (K := k) a ⊓ Subgroup.centralizer (Hh : Set (ModGL τ k))).subgroupOf
      (adjointGroup τ k ⊓ Subgroup.centralizer (Hh : Set (ModGL τ k)))).FiniteIndex := by
  classical
  set Z := adjointGroup τ k ⊓ Subgroup.centralizer (Hh : Set (ModGL τ k)) with hZdef
  set T := familyGroup (K := k) a ⊓ Subgroup.centralizer (Hh : Set (ModGL τ k)) with hTdef
  have hZ : ∀ z : Z, (z : ModGL τ k) ∈ familyCentralizer τ k a := by
    intro z
    rw [mem_familyCentralizer]
    refine ⟨z.2.1, fun i => ?_⟩
    rw [Subgroup.mem_centralizer_iff.1 z.2.2 _ (ha i), mul_inv_cancel_right]
  choose w hw m hm hzm using fun z : Z => familyCentralizer_le_mul τ k a (hZ z)
  have key : ∀ z₁ z₂ : Z, w z₁ = w z₂ →
      (QuotientGroup.mk z₁ : Z ⧸ T.subgroupOf Z) = QuotientGroup.mk z₂ := by
    intro z₁ z₂ h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ z₁.2.2) z₂.2.2⟩
    change (z₁ : ModGL τ k)⁻¹ * z₂ ∈ familyGroup (K := k) a
    rw [hzm z₁, hzm z₂, h]
    have hn := Subgroup.inv_mem _ (canonicalRep_mem_normalizer_familyGroup (K := k) (hw z₂))
    have e : (m z₁ * canonicalRep (coxeterSystem τ) k (w z₂))⁻¹ *
        (m z₂ * canonicalRep (coxeterSystem τ) k (w z₂)) =
        (canonicalRep (coxeterSystem τ) k (w z₂))⁻¹ * ((m z₁)⁻¹ * m z₂) *
          ((canonicalRep (coxeterSystem τ) k (w z₂))⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hn _).1
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hm z₁)) (hm z₂))
  let f : WeylGroup τ → Z ⧸ T.subgroupOf Z := fun v =>
    if hv : ∃ z, w z = v then QuotientGroup.mk (Classical.choose hv) else QuotientGroup.mk 1
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hv : ∃ z', w z' = w z := ⟨z, rfl⟩
    refine ⟨w z, ?_⟩
    change (if hv : ∃ z', w z' = w z then QuotientGroup.mk (Classical.choose hv)
      else QuotientGroup.mk 1) = _
    rw [dif_pos hv]
    exact key _ _ (Classical.choose_spec hv)
  have : Finite (Z ⧸ T.subgroupOf Z) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem closedIdentityComponent_le_familyGroup_inf_centralizer [IsAlgClosed k]
    (a : ι → Fin τ.rank → kˣ) {Hh : Subgroup (ModGL τ k)} (ha : ∀ i, rootDiagUnit τ (a i) ∈ Hh) :
    closedIdentityComponent (adjointGroup τ k ⊓ Subgroup.centralizer (Hh : Set (ModGL τ k))) ≤
      familyGroup (K := k) a ⊓ Subgroup.centralizer (Hh : Set (ModGL τ k)) := by
  have := finiteIndex_familyGroup_inf_centralizer a ha
  exact closedIdentityComponent_le_of_isPointClosed_finiteIndex
    (isPointClosed_familyGroup_inf_centralizer a _)

end CFSG.HardMathSupport.Timmesfeld.Torality

end
