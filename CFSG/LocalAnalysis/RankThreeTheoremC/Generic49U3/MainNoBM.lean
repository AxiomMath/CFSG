module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42ClassNoBM
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cor46
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cor47
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cover
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Endgame
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma43
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneEq
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Rank3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem gl83GenericU3Plane_of_class {G : Type} [Group G] [Finite G] (hS : Setting G)
    (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (h123 : KFactWeakClosureHeis) (hSig : SignalizerTwoGroupKFact)
    (hclass : GenericComponentClass G)
    (hSpor : GL83GenericListExclusionRedSpor G) : GL83GenericU3Plane G := by
  intro p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ hFi z hzJ hz1
    hz2 R hRP hRe hRc hxR hRz _
  have hc : U3Config G p P M x J :=
    ⟨hp, hM, hfail, hIH, hgen, h5, hJC, hCJ, hperf, hlt, hmin, hnot,
      ⟨Q, inferInstance, ψ, hψ, hker, hQ⟩⟩
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hfus := u3_fusion_core hS hD1 hU0 hSig hc
  have hL42 := u3_lemma42 hS hclass hSpor hc hfus
  have h47 := u3_cor47 hS hD1 hU0 hc
  have h46 := u3_cor46 hS hD1 hU0 hc hL42
  have hnorm := u3_normal_core hS hD1 hU0 hInn hWC h123 hc hfus
  have h43 := u3_lemma43 hS hD1 hU0 hc hnorm
  have hcov := u3_cover hS hD1 hU0 hInn hWC hc hfus hL42
  have hrk3 := u3_rank3_absorb hS hD1 hU0 hc
  have hR : R = u3U0 P x J := u3_plane_eq hS hD1 hc hzJ hz1 hz2 hRP hRe hRc hxR hRz
  subst hR
  obtain ⟨hU0e, hU0c, hU0S, hxU0, -, -, -⟩ := u3U0_facts hc
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  have hU0M : u3U0 P x J ≤ M := hU0S.trans (hSP.trans hPM)
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hend := u3_endgame (by have := hc.five; omega) hU0M hU0e hU0c hxU0 hx1 h47 h46 hrk3
    (u3_proper hS) hcov h43
  have hz2' : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one])
  have hzne : Subgroup.zpowers z ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
  have hCN : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    have hCx : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
        Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← hCx]
    exact Subgroup.centralizer_le_normalizer _
  exact hCN.trans (hend _ hzne hz2' (hRz.trans hCN))

theorem gl83GenericU3Plane_of_noBM {G : Type} [Group G] [Finite G] (hS : Setting G)
    (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (h123 : KFactWeakClosureHeis) (hSig : SignalizerTwoGroupKFact)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KF1At G) (hno : NoExcludedSection3 G)
    (hSpor : GL83GenericListExclusionRedSpor G) : GL83GenericU3Plane G :=
  gl83GenericU3Plane_of_class hS hD1 hU0 hInn hWC h123 hSig
    (genericComponentClass_of_inputs_noBM hS hU0 K1 K2 K3 K4 hno) hSpor

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
