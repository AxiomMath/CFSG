module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylow
import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlpha
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open CFSG.AGLEmbedding

theorem ker_coverHom {K X : Type} [Group K] [Group X] (e : K ⧸ Subgroup.center K ≃* X) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker = Subgroup.center K := by
  ext x
  simp

theorem pow_three_eq_one_of_abelianSylowDatum {K X : Type} [Group K] [Finite K] [Group X]
    (hK : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* X) (hS : AbelianSylowDatum X 3) (T : Sylow 3 K) :
    ∀ t ∈ (T : Subgroup K), t ^ 3 = 1 := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hπ : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  exact (coverAbelianSylowLemma K X _ hπ (ker_coverHom e) ‹_› 3 Nat.prime_three (by norm_num) hZ
    hZp hZc hS T).1

@[expose] def ONanSylowThreeDatum : Prop :=
  AbelianSylowDatum (Blueprint.NativeSporadic.Carrier .ONan) 3

theorem kOutTwoGroup_of_onan
    {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) : KOutTwoGroup K := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact kOutTwoGroup_of_card_outer_le_two hK (Nat.le_of_dvd Nat.two_pos
    (CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨e.trans b.symm⟩))

theorem kFactAlphaOnan3_of_datum
    (hS : ONanSylowThreeDatum) : KFactAlphaOnan3 := by
  intro K _ _ hK hZ hZp hZc he
  obtain ⟨e⟩ := he
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have e' : K ⧸ Subgroup.center K ≃* Blueprint.NativeSporadic.ON := e.trans b.symm
  refine ⟨kOutTwoGroup_of_onan hK e, fun T => ?_⟩
  have h1 := pow_three_eq_one_of_abelianSylowDatum (X := Blueprint.NativeSporadic.ON) hK hZ hZp
    hZc e'
  exact h1 hS T

end CFSG.LocalAnalysis.RankThreeTheoremC
