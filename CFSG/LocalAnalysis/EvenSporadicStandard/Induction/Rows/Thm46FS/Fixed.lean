module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.CatFC
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fixedComponent_of_solStd {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hF : FStarSimple N') (hidx : N'.index ≤ 2) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P) :
    ∃ (σ : MulAut ↥N') (Q : Subgroup ↥N'), orderOf σ = 2 ∧ (∀ y, σ (σ y) = y) ∧
      Q ≤ fixedSubgroup σ ∧ CFSG.IsComponent (Q.subgroupOf (fixedSubgroup σ)) ∧
      CFSG.IsPComponent 2 (Q.subgroupOf (fixedSubgroup σ)) ∧ Q ≠ ⊤ ∧
      Open.fusionZStar ↥Q = center ↥Q ∧ Nonempty (↥Q ≃* ↥P) := by
  obtain ⟨-, t, ht2, hcomp⟩ := hP
  have := hF.normal
  have hPN : P ≤ N' := Hyp.le_of_perfect_of_index_le_two hidx hPq.1
  obtain ⟨σ, D, hσ, hD, -, ⟨e⟩⟩ := exists_fixedComponent hF ht2 hcomp hPN
  have hσσ : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    omega
  let K := fixedSubgroup σ
  let Q : Subgroup ↥N' := D.map K.subtype
  have hQD : Q.subgroupOf K = D := by
    show (D.map K.subtype).comap K.subtype = D
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective D
  have hle : Q ≤ K := Subgroup.map_subtype_le D
  have hPc : CFSG.IsPComponent 2 D :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have eQD : ↥Q ≃* ↥D := (D.equivMapOfInjective K.subtype K.subtype_injective).symm
  have eQP : ↥Q ≃* ↥P := eQD.trans e
  have hQq : CFSG.IsQuasisimple ↥Q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eQP.symm hPq
  have hO : CFSG.pPrimeCore 2 ↥Q ≠ ⊤ := by
    intro htop
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : Odd (Nat.card (CFSG.pPrimeCore 2 ↥Q)) :=
      Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at h1
    exact (Nat.not_even_iff_odd.2 h1) (CFSG.RankThree.OddKernel.even_card_of_isQuasisimple hQq)
  refine ⟨σ, Q, hσ, fun y => ?_, hle, hQD ▸ hD, hQD ▸ hPc, ?_,
    CatLeaf.fusionZStar_eq_center_of_quasisimple hQq hO, ⟨eQP⟩⟩
  · have := congrArg (fun φ : MulAut ↥N' => φ y) hσσ
    simpa [MulAut.mul_apply] using this
  · intro htop
    apply hσ1
    refine MulEquiv.ext fun y => ?_
    have hy : y ∈ K := (top_le_iff.1 (htop ▸ hle)) ▸ Subgroup.mem_top y
    rw [MulAut.one_apply]
    exact hy

theorem lieModel_fusionZStar_of_solStd {P Q : Type} [Group P] [Group Q] (e : Q ≃* P)
    (hZ : Open.fusionZStar Q = center Q) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : Blueprint.LieModel (P ⧸ center P) t n p f) :
    Blueprint.LieModel (Q ⧸ Open.fusionZStar Q) t n p f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans (quotientCenterEquiv e)).symm h

theorem isSporadic_fusionZStar_of_solStd {P Q : Type} [Group P] [Group Q] (e : Q ≃* P)
    (hZ : Open.fusionZStar Q = center Q) {s : TauCeti.SporadicName}
    (h : Blueprint.NativeSporadic.IsSporadic (P ⧸ center P) s) :
    Blueprint.NativeSporadic.IsSporadic (Q ⧸ Open.fusionZStar Q) s := by
  obtain ⟨f⟩ := h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans (quotientCenterEquiv e)).trans f⟩

end CFSG.EvenSporadicStandard.Induction
