module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaThreeDefs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineFourTwoSigmaGenProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaThreeAltSix
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Structure
import CFSG.GH74.Generic.BProg.B3.S3T2A7LocGen
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
open CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree (not_surjective_of_isNineFourIndex_three)

section Cert


theorem nineTwelveOneSigmaThree_holds
    : NineTwelveOneSigmaThree := by
  intro G _ _ M Q H F s L hL hLM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΓ : ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ M) → CFSG.Open.rankThreeGamma 1 3 P ≤ M :=
    fun P hP => CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_self_le
      s.strongQ (hP.le.trans inf_le_right) hP.isPGroup
  obtain ⟨⟨_, -, -, hkSub, huniq⟩, -, -, -, -, hcent⟩ :=
    AGL81C.nineFourTwo_structure s.nine s.hq s.not_pLayerIn_le hΓ
  have hk : AGL81C.kSub 3 M H = L := hkSub.trans (huniq L hL).symm
  obtain ⟨hsimple, i, hi, ⟨eK⟩⟩ :=
    (nineFourTwoSigmaGen_holds G M Q H F 3 s.nine s.hq s.not_pLayerIn_le hΓ).2.2.2
  by_cases hA : ∃ (n : ℕ) (h : 5 ≤ n), i = .alternating n h
  · obtain ⟨n, h5, rfl⟩ := hA
    obtain rfl : n = 6 := by
      rcases hi with ⟨-, hn⟩ | ⟨h, -⟩
      · exact hn
      · omega
    exact Or.inr (nonempty_quot_solvableRadical_equiv_altSix s hL hk hsimple eK)
  push Not at hA
  have hLK : AGL81C.IsPComponentIn 3 L (AGL81C.kSub 3 M H) :=
    ⟨by rw [hk], CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (by rw [hk]) (AGL81C.kSub_le 3 M H) hL.2⟩
  have hZ : Subgroup.center ↥(AGL81C.kStar 3 M H) = ⊥ :=
    CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.center_eq_bot_of_centralizer hcent
  obtain ⟨eLO⟩ := AGL81C.IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hL
  have hstar : AGL81C.starImg 3 H L = AGL81C.kStar 3 M H := by
    rw [AGL81C.kStar_eq_starImg 3 M H, hk]
  let e₁ := eLO.trans (MulEquiv.subgroupCongr hstar)
  have hZ' := CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.center_eq_bot_of_equiv e₁ hZ
  let e := ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).trans
    (e₁.trans eK)
  refine Or.inl (s.nine.isTwoPrimeComponentIn_of_not_autSection
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds s.not_pLayerIn_le hLK ?_)
  intro r hr hr2 hr3 V _ _ hV hrank A φ hφ
  exact not_surjective_of_isNineFourIndex_three hr hr2 hr3 hi hA hV hrank A
    (e.toMonoidHom.comp φ) (e.surjective.comp hφ)

end Cert

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
