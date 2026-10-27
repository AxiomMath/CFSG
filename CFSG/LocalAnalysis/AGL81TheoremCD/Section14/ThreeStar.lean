module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Cases
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.HypC
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Sylow
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Preamble
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoL34
import CFSG.Quasithin.Background.A3Structure318Star
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTenBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.PGLModelDefs
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinSubnormal
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.GroupTheory.WielandtProductAux
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl2
import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
import CFSG.Models.PGLOrders
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Open.StatedCenterThree
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.M22

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Quasithin
open CFSG.ComponentClassification.CatalogueBPrimeJoin

variable {G : Type} [Group G] [Finite G]

theorem center_threeStar_noTwo (J : Subgroup G) :
    ∀ z ∈ Subgroup.center (threeStar J), ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine center_noTwo_of_pCore_two_eq_bot ?_
  exact le_bot_iff.mp
    ((CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num)).trans_eq
      (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three))

namespace IsKComp

variable {M H J : Subgroup G}

theorem isQuasisimple (hJ : IsKComp M H J) : CFSG.IsQuasisimple (threeStar J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ((CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff 3 J
    (kSub 3 M H) hJ.1).mp hJ.2).2.2

theorem isSubnormal (hJ : IsKComp M H J) :
    (J.subgroupOf (kSub 3 M H)).IsSubnormal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ((CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff 3 J
    (kSub 3 M H) hJ.1).mp hJ.2).1

theorem primeResidual_eq_top (hJ : IsKComp M H J) :
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 J = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ((CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff 3 J
    (kSub 3 M H) hJ.1).mp hJ.2).2.1

theorem isPerfect (hJ : IsKComp M H J) : Group.IsPerfect ↥J := by
  haveI : Group.IsPerfect ↥(J.subgroupOf (kSub 3 M H)) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hJ.2
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hJ.1).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hJ.1).surjective

theorem three_dvd_card (hJ : IsKComp M H J) : 3 ∣ Nat.card J := by
  by_contra h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : CFSG.pPrimeCore 3 ↥J = ⊤ := by
    refine eq_top_iff.mpr (le_sSup ⟨inferInstance, ?_⟩)
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  haveI : Subsingleton (threeStar J) := by
    rw [threeStar, htop]
    exact QuotientGroup.subsingleton_quotient_top
  haveI : Nontrivial (threeStar J) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hJ.isQuasisimple
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (threeStar J)).exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem isPComponentIn (hJ : IsKComp M H J) : IsPComponentIn 3 J H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hJ.1.trans (kSub_le 3 M H), ?_⟩
  exact (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal
    hJ.1 (kSub_le 3 M H) (kSub_subgroupOf_isSubnormal 3 M H)).mpr hJ.2

theorem le_pLayerIn (hJ : IsKComp M H J) : J ≤ pLayerIn 3 H :=
  CFSG.LocalAnalysis.RankThreeUC.AGL81C.le_pLayerIn hJ.isPComponentIn

theorem card_center_threeStar_dvd_three
    (hJ : IsKComp M H J) (hL : IsL34Type (threeStar J)) :
    Nat.card (Subgroup.center (threeStar J)) ∣ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : commutator (threeStar J) = ⊤ := hJ.isQuasisimple.1.commutator_eq_top
  have hodd := center_threeStar_noTwo J
  have hadm : StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hbase : IsPSL 3 2 2 (CFSG.PGLModel.projSL 3 (GaloisField 2 2)) :=
    CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm (MulEquiv.refl _)
  obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type hL
  have hmod : IsPSL 3 2 2 (threeStar J ⧸ Subgroup.center (threeStar J)) :=
    IsPSL.of_mulEquiv e.symm hbase
  exact CFSG.Quasithin.H13.S126P31.card_center_dvd_three_of_quotient hperf hodd hmod

theorem isL34Star_or_isSL34Star
    (hJ : IsKComp M H J) (hL : IsL34Type (threeStar J)) :
    IsL34Star J ∨ IsSL34Star J := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (hJ.card_center_threeStar_dvd_three hL) with h | h
  · exact Or.inl ⟨hL, h⟩
  · exact Or.inr ⟨hL, h⟩

end IsKComp

namespace IsL34Star

theorem card_threeStar {J : Subgroup G} (h : IsL34Star J) :
    Nat.card (threeStar J) = 20160 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type h.1
  have hcenter : Subgroup.center (threeStar J) = ⊥ :=
    Subgroup.eq_bot_of_card_eq (Subgroup.center (threeStar J)) h.2
  have e1 : threeStar J ≃* threeStar J ⧸ Subgroup.center (threeStar J) :=
    ((QuotientGroup.quotientMulEquivOfEq (G := threeStar J)
      (M := Subgroup.center (threeStar J)) (N := ⊥) hcenter).trans
      (QuotientGroup.quotientBot (G := threeStar J))).symm
  calc Nat.card (threeStar J) =
        Nat.card (threeStar J ⧸ Subgroup.center (threeStar J)) :=
        Nat.card_congr e1.toEquiv
    _ = Nat.card (CFSG.PGLModel.projSL 3 (GaloisField 2 2)) := Nat.card_congr e.toEquiv
    _ = 20160 := CFSG.PGLModel.card_projSL_three_four

end IsL34Star

namespace IsSL34Star

theorem card_threeStar {J : Subgroup G} (h : IsSL34Star J) :
    Nat.card (threeStar J) = 60480 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type h.1
  have hmul := Subgroup.card_mul_index (Subgroup.center (threeStar J))
  rw [h.2, Subgroup.index_eq_card, Nat.card_congr e.toEquiv,
    CFSG.PGLModel.card_projSL_three_four] at hmul
  omega

end IsSL34Star

namespace IsA11Star

theorem card_threeStar {J : Subgroup G} (h : IsA11Star J) :
    Nat.card (threeStar J) = 19958400 := by
  obtain ⟨e⟩ := h
  calc Nat.card (threeStar J) = Nat.card (alternatingGroup (Fin 11)) :=
        Nat.card_congr e.toEquiv
    _ = 19958400 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num

theorem center_eq_bot {J : Subgroup G} (h : IsA11Star J) :
    Subgroup.center (threeStar J) = ⊥ := by
  obtain ⟨e⟩ := h
  exact CFSG.Quasithin.H13.Lem8.center_eq_bot_of_mulEquiv e
    (CFSG.Quasithin.H13.Lem8.center_alternatingGroup_eq_bot (by norm_num))

end IsA11Star

theorem card_threeStar_dvd_of_le {J₁ J : Subgroup G} (h : J₁ ≤ J) :
    Nat.card (threeStar J₁) ∣ Nat.card (threeStar J) := by
  have h1 := card_pPrimeCore_quotient_dvd_card_map_quotient (p := 3) (K := J₁) (H := J) h
  have hcard : Nat.card (threeStar J) =
      Nat.card (↥J ⧸ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
        (G := ↥J) 3) :=
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
      (by rfl : CFSG.pPrimeCore 3 ↥J =
        CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥J) 3)).toEquiv
  have h2 : Nat.card ((J₁.subgroupOf J).map
      (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
        (G := ↥J) 3))) ∣ Nat.card (threeStar J) := by
    have h3 := Subgroup.card_dvd_of_le (H := (J₁.subgroupOf J).map
      (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
        (G := ↥J) 3))) (K := ⊤) le_top
    rw [Subgroup.card_top] at h3
    rwa [hcard]
  exact h1.trans h2

theorem eq_kSub_of_subnormal_of_map_eq_top {M H J : Subgroup G}
    (hK : IsKComp M H (kSub 3 M H)) (hJK : J ≤ kSub 3 M H)
    (hsub : (J.subgroupOf (kSub 3 M H)).IsSubnormal)
    (hmap : (J.subgroupOf (kSub 3 M H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))) = ⊤) :
    J = kSub 3 M H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsup : J.subgroupOf (kSub 3 M H) ⊔ CFSG.pPrimeCore 3 ↥(kSub 3 M H) = ⊤ := by
    have h := Subgroup.comap_map_eq
      (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))
      (H := J.subgroupOf (kSub 3 M H))
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hdvd := CFSG.GroupTheory.WielandtProduct.index_dvd_card_of_sup_eq_top
    (H := J.subgroupOf (kSub 3 M H)) (N := CFSG.pPrimeCore 3 ↥(kSub 3 M H)) hsup
  have hcop : Nat.Coprime 3 (J.subgroupOf (kSub 3 M H)).index :=
    CFSG.pPrimeCore_coprime_card.of_dvd_right hdvd
  have htop : (⊤ : Subgroup ↥(kSub 3 M H)) ≤ J.subgroupOf (kSub 3 M H) := by
    rw [← hK.primeResidual_eq_top]
    exact primeResidual_le_subnormal_of_coprime_index 3 (J.subgroupOf (kSub 3 M H))
      hsub hcop
  exact le_antisymm hJK (Subgroup.subgroupOf_eq_top.mp (top_le_iff.mp htop))

namespace IsKComp

variable {M H J : Subgroup G}

theorem eq_kSub_of_isKComp_self (hK : IsKComp M H (kSub 3 M H)) (hJ : IsKComp M H J) :
    J = kSub 3 M H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let π : ↥K →* threeStar K := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
  let C : Subgroup (threeStar K) := (J.subgroupOf K).map π
  have hCeq : C = hJ.2.choose := hJ.2.choose_spec.2.2.1
  have hCcomp : CFSG.IsComponent C := hCeq ▸ hJ.2.choose_spec.1
  have hCsub : C.IsSubnormal := hCcomp.2
  have hKstar : CFSG.IsQuasisimple (threeStar K) := by
    simpa [K] using hK.isQuasisimple
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hKstar hCsub with
    hCtop | hCcenter
  · exact eq_kSub_of_subnormal_of_map_eq_top hK hJ.1 hJ.isSubnormal (by simpa [K, C, π] using hCtop)
  · exfalso
    have hCcomm : IsMulCommutative C :=
      ⟨⟨fun x y => Subtype.ext
        ((Subgroup.mem_center_iff.mp (hCcenter x.2) (y : threeStar K)).symm)⟩⟩
    haveI : Group.IsPerfect C := hCcomp.1.1
    haveI : Nontrivial C := CFSG.LocalCores.isQuasisimple_nontrivial hCcomp.1
    have hCbot : C = ⊥ := (Group.IsPerfect.not_isMulCommutative (G := C) hCcomm).elim
    have hJleO : J.subgroupOf K ≤ CFSG.pPrimeCore 3 ↥K := by
      have h := (Subgroup.map_eq_bot_iff (H := J.subgroupOf K) (f := π)).mp (by
        simpa [C] using hCbot)
      rwa [QuotientGroup.ker_mk'] at h
    have hdle : Nat.card J ∣ Nat.card (CFSG.pPrimeCore 3 ↥K) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ.1).toEquiv]
      exact Subgroup.card_dvd_of_le hJleO
    have h3O : 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥K) := hJ.three_dvd_card.trans hdle
    exact absurd h3O ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      CFSG.pPrimeCore_coprime_card)

end IsKComp

theorem eq_kSub_of_le_of_subnormal {M H J : Subgroup G}
    (hK : IsKComp M H (kSub 3 M H))
    (hZ : Subgroup.center (threeStar (kSub 3 M H)) = ⊥) (hJK : J ≤ kSub 3 M H)
    (hsub : (J.subgroupOf (kSub 3 M H)).IsSubnormal) (h3 : 3 ∣ Nat.card J) :
    J = kSub 3 M H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let π : ↥K →* threeStar K := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
  let C : Subgroup (threeStar K) := (J.subgroupOf K).map π
  have hCsub : C.IsSubnormal := Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hsub
  have hKstar : CFSG.IsQuasisimple (threeStar K) := by
    simpa [K] using hK.isQuasisimple
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hKstar hCsub with
    hCtop | hCcenter
  · exact eq_kSub_of_subnormal_of_map_eq_top hK hJK hsub (by simpa [K, C, π] using hCtop)
  · exfalso
    have hCbot : C = ⊥ :=
      le_bot_iff.mp (hCcenter.trans (by simpa [K] using hZ.le))
    have hJleO : J.subgroupOf K ≤ CFSG.pPrimeCore 3 ↥K := by
      have h := (Subgroup.map_eq_bot_iff (H := J.subgroupOf K) (f := π)).mp (by
        simpa [C] using hCbot)
      rwa [QuotientGroup.ker_mk'] at h
    have hdle : Nat.card J ∣ Nat.card (CFSG.pPrimeCore 3 ↥K) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJK).toEquiv]
      exact Subgroup.card_dvd_of_le hJleO
    have h3O : 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥K) := h3.trans hdle
    exact absurd h3O ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      CFSG.pPrimeCore_coprime_card)

theorem E_le_M_of_gamma {p : ℕ} (hp : p.Prime) {E M : Subgroup G}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) : E ≤ M := by
  have h2 : 2 ≤ CFSG.Open.pRank p E :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hc
  exact Subgroup.le_normalizer.trans
    ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 p E M).mp hΓ E le_rfl (by omega))

namespace HypCGen

variable {M : Subgroup G} {q : ℕ} {E H : Subgroup G}

theorem mem_QSet_of_le (h : HypCGen G M q E H) {P : Subgroup G} (hEP : E ≤ P)
    (hPM : P ≤ M) (hP : IsPGroup q P) : P ∈ QSet M q :=
  ⟨h.prime, h.odd, hPM, hP, Or.inr ⟨E, hEP, h.elem, h.card, h.gamma⟩⟩

theorem le_M_of_isPGroup (h : HypCGen G M 3 E H) (hU : NineNineOneAt M)
    {P : Subgroup G} (hEP : E ≤ P) (hP : IsPGroup 3 P) : P ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, -, hTP, hTM, -, hmax⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.exists_maxPSubgroup_of_normalizer_le
      (p := 3) (Q := E) (N := P) (M := M) h.isPGroup hEP h.E_le_M
      (fun U hEU hUM _ =>
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne.normalizer_le h.maxLocal
          (hU 3 E H h) h.E_le_M h.elem h.card h.gamma hEU hUM)
  rw [hmax P le_rfl hP hTP]
  exact hTM

end HypCGen

theorem exists_hypCGen_of_mem {M : Subgroup G} (hC : CStarGen G)
    (hM : rankThreeIsMaxTwoLocal M)
    (hσ : (sigmaSet G M).Nonempty) {p : ℕ} {Q H : Subgroup G} (hQ : Q ∈ QSet M p)
    (hH : H ∈ H2StarFam M Q) : ∃ E ≤ Q, HypCGen G M p E H := by
  haveI : IsSimpleGroup G := hC.simple
  have hp : p.Prime := QSet.prime_of_mem hQ
  have hQne : Q ≠ ⊥ := by
    have hbot : CFSG.Open.pRank p (⊥ : Subgroup G) ≤ 0 := by
      refine CFSG.SectionRank.pRank_le (p := p) (H := ⊥) (k := 0) hp.one_lt ?_
      intro E hE _
      rw [le_bot_iff.mp hE, Subgroup.card_bot]
      simp
    intro hbotQ
    have h2 := QSet.two_le_pRank_of_mem hQ
    rw [hbotQ] at h2
    omega
  have hloc : IsTwoLocal H :=
    isTwoLocal_of_mem_H2StarFam hC.nonab hC.charTwo hQne hH
  rcases (mem_QSet_iff.mp hQ).2.2.2.2 with ⟨hpσ, hpr⟩ | ⟨E, hEQ, hE, hEc, hΓ⟩
  · exact absurd (hC.embed p hpσ.1 M hM Q (QSet.le_of_mem hQ) (QSet.isPGroup_of_mem hQ)
      hpr.le H hloc hH.1.2.1) hH.1.2.2.1
  · refine ⟨E, hEQ, ?_⟩
    exact { cstar := hC
            maxLocal := hM
            sigma_nonempty := hσ
            prime := hp
            odd := QSet.ne_two_of_mem hQ
            E_le_M := E_le_M_of_gamma hp hE hEc hΓ
            elem := hE
            card := hEc
            gamma := hΓ
            mem := mem_H2StarFam_of_le hH (hEQ.trans hH.1.2.1) }

namespace S14Choice

variable {M H E Q J : Subgroup G}

theorem hypCGen (h : S14Choice G M H E Q J) : HypCGen G M 3 E H := by
  obtain ⟨p, Q₀, -, hHQ₀⟩ := h.mem
  exact { cstar := h.cstar
          maxLocal := h.maxLocal
          sigma_nonempty := h.sigma_nonempty
          prime := Nat.prime_three
          odd := by norm_num
          E_le_M := E_le_M_of_gamma Nat.prime_three h.elem (by rw [h.card]; norm_num) h.gamma
          elem := h.elem
          card := h.card
          gamma := h.gamma
          mem := mem_H2StarFam_of_le hHQ₀ h.E_le_H }

theorem mem_H2StarFam (h : S14Choice G M H E Q J) : H ∈ H2StarFam M Q := by
  obtain ⟨p, Q₀, -, hHQ₀⟩ := h.mem
  exact mem_H2StarFam_of_le hHQ₀ (h.sylow.le.trans (sup_le (kSub_le 3 M H) h.E_le_H))

theorem Q_le_M (h : S14Choice G M H E Q J) (hU : NineNineOneAt M) : Q ≤ M :=
  h.hypCGen.le_M_of_isPGroup hU h.E_le_Q h.sylow.isPGroup

theorem Q_mem_QSet (h : S14Choice G M H E Q J) (hU : NineNineOneAt M) : Q ∈ QSet M 3 :=
  h.hypCGen.mem_QSet_of_le h.E_le_Q (h.Q_le_M hU) h.sylow.isPGroup

end S14Choice

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
