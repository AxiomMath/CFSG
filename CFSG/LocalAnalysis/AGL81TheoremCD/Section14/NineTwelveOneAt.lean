module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeStar
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneGen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AElevenAutSection
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutHolds

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

variable {G : Type} [Group G] [Finite G]

theorem isLinThreeFour_lie {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d.1 = .A 2 Q) :
    CFSG.AGLEmbedding.IsLinThreeFour (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨Q, hQcard, hQd⟩ := hd
  have h4 : Q.p ^ Q.exponent = 2 ^ 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hQcard
  obtain ⟨hp, he⟩ :=
    Nat.Prime.pow_inj' Q.prime_p Nat.prime_two Q.exponent_pos.ne' two_ne_zero h4
  exact ⟨d, ⟨Q, hp, he, hQd⟩, ⟨MulEquiv.refl _⟩⟩

theorem HypCGen.isTwoPrimeComponentIn_of_type
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {M E H J : Subgroup G} (h : HypCGen G M 3 E H) (hL : ¬ pLayerIn 3 H ≤ M)
    (hJ : IsKComp M H J) (htype : IsL34Type (threeStar J) ∨ IsA11Star J) :
    IsTwoPrimeComponentIn J H := by
  refine NineSettingGen.isTwoPrimeComponentIn_of_not_autSection hS h.toNineSettingGen hL hJ ?_
  intro q hq hq2 hq3 V _ _ hV hr A φ hφ
  rcases htype with hL34 | hA11
  · obtain ⟨d, ⟨Q, hQcard, hQd⟩, ⟨e⟩⟩ := hL34
    exact CFSG.LocalAnalysis.RankThreeTheoremC.kFactLThreeFourAutSection_holds
      q hq hq2 hq3 V hV hr A _ (isLinThreeFour_lie ⟨Q, hQcard, hQd⟩)
      (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
  · have hZ : Subgroup.center (threeStar J) = ⊥ := IsA11Star.center_eq_bot hA11
    obtain ⟨e⟩ := hA11
    have e' : (↥J ⧸ CFSG.pPrimeCore 3 ↥J) ⧸
        Subgroup.center (↥J ⧸ CFSG.pPrimeCore 3 ↥J) ≃* alternatingGroup (Fin 11) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans
        ((QuotientGroup.quotientBot (G := threeStar J)).trans e)
    exact not_surjective_of_mulEquiv_alternatingGroup_eleven hq hq2 hV hr A e' φ hφ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
