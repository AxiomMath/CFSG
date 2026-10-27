module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL2

public section

namespace CFSG.EvenSporadicStandard.Induction.SporCentre

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {S : Type*} [Group S]

theorem isQuasisimple_of_isPComponent [Finite S] {F Q : Subgroup S} (hQF : Q ≤ F)
    (hQ : IsPComponent 2 (Q.subgroupOf F)) (hZ : Open.fusionZStar Q = center Q) :
    IsQuasisimple ↥Q := by
  obtain ⟨hs, hna, -, -⟩ := GrSLit.fusionZStar_quotient_of_isPComponent hQF hQ
  have e : Q ⧸ Open.fusionZStar Q ≃* Q ⧸ center Q := QuotientGroup.quotientMulEquivOfEq hZ
  have : Group.IsPerfect (Q.subgroupOf F) := CatalogueBAlternating.pComponent_perfect hQ
  have : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hQF).toMonoidHom)
      (subgroupOfEquivOfLe hQF).surjective
  refine ⟨inferInstance, (MulEquiv.isSimpleGroup_congr e).mp hs, ?_⟩
  obtain ⟨x, y, hxy⟩ := hna
  exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩

theorem isComponent_of_isPComponent [Finite S] {F Q : Subgroup S} (hQF : Q ≤ F)
    (hQ : IsPComponent 2 (Q.subgroupOf F)) (hZ : Open.fusionZStar Q = center Q) :
    IsComponent (Q.subgroupOf F) := by
  have hq := isQuasisimple_of_isPComponent hQF hQ hZ
  obtain ⟨-, -, hsub, -, -⟩ := hQ
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hQF).symm hq, hsub⟩

theorem sq_eq_one_of_forall {σ : MulAut S} (hσ : ∀ y, σ (σ y) = y) : σ ^ 2 = 1 := by
  ext y
  rw [pow_two, MulAut.mul_apply, hσ, MulAut.one_apply]

theorem orderOf_eq_two [Finite S] [IsSimpleGroup S] {σ : MulAut S} {Q : Subgroup S}
    (h : ProperFixedComponent σ Q) : orderOf σ = 2 :=
  orderOf_eq_prime (sq_eq_one_of_forall h.1) h.ne_one

theorem inner_data [Finite S] [IsSimpleGroup S] (hnab : ∃ x y : S, x * y ≠ y * x)
    {σ : MulAut S} {Q : Subgroup S} (h : ProperFixedComponent σ Q)
    (hZ : Open.fusionZStar Q = center Q) {t : S} (ht : σ = MulAut.conj t) :
    orderOf t = 2 ∧ Q ≤ centralizer ({t} : Set S) ∧
      IsComponent (Q.subgroupOf (centralizer ({t} : Set S))) := by
  obtain ⟨ht2, hQC, hQ, -⟩ := h.inner hnab ht
  exact ⟨ht2, hQC, isComponent_of_isPComponent hQC hQ hZ⟩

theorem card_quotient_center_subgroupOf {F Q : Subgroup S} (hQF : Q ≤ F) :
    Nat.card ((Q.subgroupOf F) ⧸ center (Q.subgroupOf F)) = Nat.card (Q ⧸ center Q) :=
  Nat.card_congr (CatFC.quotientCenterEquiv (subgroupOfEquivOfLe hQF)).toEquiv

end CFSG.EvenSporadicStandard.Induction.SporCentre
