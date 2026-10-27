module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaStrongDefs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineFourTwoSigmaGenProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionHolds
import CFSG.GH74.Generic.BProg.B3.S3T2A7LocGen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217OTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
open CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

private noncomputable def quotCenterEquiv {G : Type} [Group G] [Finite G]
    {M H L : Subgroup G} {q : ℕ} (hq : q.Prime) (hL : AGL81C.IsPComponentIn q L H)
    (hk : AGL81C.kSub q M H = L) (hZ : Subgroup.center ↥(AGL81C.kStar q M H) = ⊥)
    {i : TauCeti.CFSGIndex} (eK : ↥(AGL81C.kStar q M H) ≃* i.Group) :
    ((↥L ⧸ CFSG.pPrimeCore q ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pPrimeCore q ↥L)) ≃* i.Group := by
  let eLO : (↥L ⧸ CFSG.pPrimeCore q ↥L) ≃* ↥(AGL81C.starImg q H L) :=
    Classical.choice (AGL81C.IsPComponentIn.nonempty_quotEquiv_starImg hq hL)
  have hstar : AGL81C.starImg q H L = AGL81C.kStar q M H := by
    rw [AGL81C.kStar_eq_starImg q M H, hk]
  let e₁ : (↥L ⧸ CFSG.pPrimeCore q ↥L) ≃* ↥(AGL81C.kStar q M H) :=
    eLO.trans (MulEquiv.subgroupCongr hstar)
  have hZ' := CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.center_eq_bot_of_equiv e₁ hZ
  exact ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).trans
    (e₁.trans eK)

section Cert


private theorem autSection_free
    {G : Type} [Group G] [Finite G]
    {M H L : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hL : AGL81C.IsPComponentIn q L H) (hk : AGL81C.kSub q M H = L)
    (hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q ↥(AGL81C.kStar q M H))
    (hZ : Subgroup.center ↥(AGL81C.kStar q M H) = ⊥) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ q → ∀ (V : Type) [Group V] [Finite V],
      IsPGroup r V → CFSG.Open.pRank r (⊤ : Subgroup V) ≤ 3 →
      ∀ (A : Subgroup (MulAut V))
        (φ : ↥A →* (↥L ⧸ CFSG.pPrimeCore q ↥L) ⧸
          Subgroup.center (↥L ⧸ CFSG.pPrimeCore q ↥L)),
      ¬ Function.Surjective φ := by
  obtain ⟨-, i, hiFour, ⟨eK⟩⟩ := hlist
  let e := quotCenterEquiv hq hL hk hZ eK
  intro r hr hr2 hrq V _ _ hV hrank A φ hφ
  exact kFactNineThreeAutSection_holds q r hq hq2 hq3 hr hr2 hrq i
    (O1217.isNineThreeIndex_of_isNineFourIndex hiFour) V hV hrank A
    (e.toMonoidHom.comp φ) (e.surjective.comp hφ)

theorem nineTwelveOneSigmaStrong_holds
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    NineTwelveOneSigmaStrong := by
  intro G _ _ M Q H F q s hq3 L hL hLM
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  have hΓ : ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf q P (H ⊓ M) →
        CFSG.Open.rankThreeGamma 1 q P ≤ M := by
    intro P hP
    exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_self_le
      s.strongQ (hP.le.trans inf_le_right) hP.isPGroup
  obtain ⟨⟨_, -, -, hkSub, huniq⟩, -, -, -, -, hcent⟩ :=
    AGL81C.nineFourTwo_structure s.nine s.hq s.not_pLayerIn_le hΓ
  have hk : AGL81C.kSub q M H = L := hkSub.trans (huniq L hL).symm
  have hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q
      ↥(AGL81C.kStar q M H) :=
    (nineFourTwoSigmaGen_holds G M Q H F q s.nine s.hq s.not_pLayerIn_le hΓ).2.2.2
  have hLK : AGL81C.IsPComponentIn q L (AGL81C.kSub q M H) := by
    refine ⟨by rw [hk], ?_⟩
    exact CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (by rw [hk]) (AGL81C.kSub_le q M H) hL.2
  have hZ : Subgroup.center ↥(AGL81C.kStar q M H) = ⊥ :=
    CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.center_eq_bot_of_centralizer hcent
  exact s.nine.isTwoPrimeComponentIn_of_not_autSection hS s.not_pLayerIn_le hLK
    (autSection_free s.qPrime s.q_ne_two hq3 hL hk hlist hZ)

end Cert

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
