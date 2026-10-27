module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCross
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartOne.KC.OrthogonalHypCoordinates
public import CFSG.ClassicalGroups.Orthogonal.OmegaPlusFixedCard
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Fix

variable {G H : Type*} [Group G] [Group H]

@[expose] def FixRankTwo (α : MulAut G) : Prop :=
  ∀ E : Subgroup G, E ≤ fixSubgroup α → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2

theorem FixRankTwo.of_congr (e : G ≃* H) {α : MulAut G} (h : FixRankTwo (MulAut.congr e α)) :
    FixRankTwo α := by
  intro E hE hEa
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  refine h _ ?_ (hEa.map e.toMonoidHom)
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fixSubgroup, MulAut.congr_apply]
  change e (α (e.symm (e x))) = e x
  rw [MulEquiv.symm_apply_apply, (mem_fixSubgroup.mp (hE hx))]

theorem FixRankTwo.of_conj (ψ : MulAut G) {α : MulAut G} (h : FixRankTwo (ψ * α * ψ⁻¹)) :
    FixRankTwo α := by
  refine FixRankTwo.of_congr ψ ?_
  have e : MulAut.congr ψ α = ψ * α * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  rw [e]
  exact h

theorem FixRankTwo.of_inv {α : MulAut G} (h : FixRankTwo α⁻¹) : FixRankTwo α := by
  intro E hE hEa
  refine h E (fun x hx => ?_) hEa
  have hx' := mem_fixSubgroup.mp (hE hx)
  rw [mem_fixSubgroup]
  conv_lhs => rw [← hx']
  exact α.symm_apply_apply x

theorem FixRankTwo.of_mulEquiv {α : MulAut G} (e : ↥(fixSubgroup α) ≃* H)
    (hH : ∀ F : Subgroup H, CFSG.Open.IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 2) :
    FixRankTwo α := by
  intro E hE hEa
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv,
    ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact hH _ ((hEa.subgroupOf (fixSubgroup α)).map e.toMonoidHom)

end Fix

theorem exists_isCrossSimilarity_coordinateQuadPlus {K : Type} [Field K]
    {Q₈ : QuadraticForm K (Fin 8 → K)} (h : CFSG.ClassicalGroups.Orthogonal.IsPlus Q₈ 4) :
    ∃ m : coordinateSemilinearGroup 8 K, IsCrossSimilarity Q₈ (coordinateQuadPlus 4 K) m := by
  obtain ⟨P, hP⟩ := h.pairs
  have hU : CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.pairsPerp P = ⊥ := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.finrank_pairsPerp hP h.nondeg
    rw [h.finrank_eq] at h1
    exact Submodule.finrank_eq_zero.mp (by omega)
  set e := CFSG.RankThree.PartOne.KCOrthogonal.hypCoordSplitIsometry hP hU with he
  set L : (Fin 8 → K) ≃ₗ[K] (Fin 8 → K) :=
    e.toLinearEquiv.trans (reindexVectorEquiv (plusIndexEquiv 4)) with hL
  have hLQ : ∀ v, coordinateQuadPlus 4 K (L v) = Q₈ v := by
    intro v
    rw [coordinateQuadPlus, reindexQuadraticForm_apply]
    have h2 : (fun i => L v (plusIndexEquiv 4 i)) = e v := by
      funext i
      rw [hL, LinearEquiv.trans_apply, reindexVectorEquiv_apply, Equiv.symm_apply_apply]
      rfl
    rw [h2]
    exact e.map_app v
  set M : GL (Fin 8) K := matrixLinearIso.symm L with hM
  refine ⟨SemidirectProduct.inl M, 1, fun v => ?_⟩
  have h3 : coordinateSemilinearMap (SemidirectProduct.inl M : coordinateSemilinearGroup 8 K) v =
      L v := by
    change matrixLinearIso M v = L v
    rw [hM, MulEquiv.apply_symm_apply]
  rw [h3, hLQ, Units.val_one, one_mul, SemidirectProduct.right_inl]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
