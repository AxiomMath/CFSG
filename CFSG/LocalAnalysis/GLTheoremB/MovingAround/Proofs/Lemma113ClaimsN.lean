module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsCtx
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsGrun
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsB
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113g
public import CFSG.Holt.NotStar.Lemma216DihedralLinear
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionRankOne
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.GroupTheory.QuasiDihedralFusion.Classes
public import CFSG.Holt.Bender
public import CFSG.Holt.NotStar.Lemma213
public import CFSG.Holt.NotStar.Lemma216
public import CFSG.Holt.NotStar.Lemma216DihedralA7Facts
public import CFSG.Holt.PSL2Natural.Basic
public import CFSG.Holt.PSL2Natural.Lemma16
public import CFSG.Holt.PSL2Natural.Normalizer
public import CFSG.Holt.PermFacts
public import CFSG.Holt.SmallGroups
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeNormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.JRAssembly
public import CFSG.Walter.JRFacts
public import CFSG.Walter.W67.PSL2Aux
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

namespace N

variable {G : Type} [Group G] [Finite G]

theorem subOut_core {K : Subgroup G} (hK : IsLTwoTwentySeven (barOf 3 K)) {x n : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, ∀ u ∈ K, ∃ z ∈ GLAPPrimeCoreOf 3 K,
      (x⁻¹ * n⁻¹ * x * n) * u * (x⁻¹ * n⁻¹ * x * n)⁻¹ = k * u * k⁻¹ * z := by
  classical
  obtain ⟨e0⟩ := hK
  have hOut : CFSG.Holt.NotStar216.OutAbelian (barOf 3 K) :=
    (CFSG.Holt.NotStar216.outAbelian_psl2 (GaloisField 3 3)).of_mulEquiv e0
  set γx : ↥(Subgroup.normalizer (K : Set G)) := ⟨x, hx⟩ with hγx
  set γn : ↥(Subgroup.normalizer (K : Set G)) := ⟨n, hn⟩ with hγn
  obtain ⟨g, hg⟩ := hOut (barAut 3 K γx)⁻¹ (barAut 3 K γn)⁻¹
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨(k : G), k.2, fun u hu => ?_⟩
  set γc : ↥(Subgroup.normalizer (K : Set G)) := γx⁻¹ * γn⁻¹ * γx * γn with hγc
  have hc : (γc : G) = x⁻¹ * n⁻¹ * x * n := by simp [hγc, hγx, hγn]
  have key := hg (QuotientGroup.mk ⟨u, hu⟩)
  have h1 : ((barAut 3 K γx)⁻¹ * (barAut 3 K γn)⁻¹ * ((barAut 3 K γx)⁻¹)⁻¹ *
      ((barAut 3 K γn)⁻¹)⁻¹) = barAut 3 K γc := by
    simp [hγc, map_mul, map_inv]
  rw [h1, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at key
  have key' : (QuotientGroup.mk (k * ⟨u, hu⟩ * k⁻¹) : barOf 3 K) =
      QuotientGroup.mk (K.normalizerMonoidHom γc ⟨u, hu⟩) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact key.symm
  have hz := QuotientGroup.eq.1 key'
  refine ⟨((k * ⟨u, hu⟩ * k⁻¹)⁻¹ * K.normalizerMonoidHom γc ⟨u, hu⟩ : ↥K), ?_, ?_⟩
  · exact (Lemma113c.coe_mem_core_iff _).2 hz
  · have h2 : ((K.normalizerMonoidHom γc ⟨u, hu⟩ : ↥K) : G) = (γc : G) * u * (γc : G)⁻¹ := rfl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, h2, hc]
    group

namespace CtxN

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem rhoQ_eq_conj (hQK : Q ≤ Subgroup.normalizer (K : Set G)) {q : G} (hqQ : q ∈ Q) {k : G}
    (hk : k ∈ K)
    (hkey : ∀ u ∈ K, ∃ z ∈ GLAPPrimeCoreOf 3 K, q * u * q⁻¹ = k * u * k⁻¹ * z) :
    Lemma113d.rhoQ hQK ⟨q, hqQ⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : barOf 3 K) := by
  ext y
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Lemma113d.rhoQ_apply, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.conj_apply,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  obtain ⟨z, hz, hzeq⟩ := hkey u u.2
  symm
  apply QuotientGroup.eq.2
  have hzK : (((⟨k, hk⟩ * u * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹ * (K.normalizerMonoidHom ⟨q, hQK hqQ⟩) u : ↥K) :
      G) = z := by
    have h2 : (((K.normalizerMonoidHom ⟨q, hQK hqQ⟩) u : ↥K) : G) = q * u * q⁻¹ := rfl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, h2]
    rw [hzeq]
    group
  exact (Lemma113c.coe_mem_core_iff _).1 (by rw [hzK]; exact hz)


theorem inner_mem_E (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {q : G} (hqQ : q ∈ Q)
    (hin : ∃ k ∈ K, ∀ u ∈ K, ∃ z ∈ GLAPPrimeCoreOf 3 K, q * u * q⁻¹ = k * u * k⁻¹ * z) :
    q ∈ E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e0⟩ := c.hKI
  set ρ : ↥Q →* MulAut (barOf 3 K) := Lemma113d.rhoQ c.hQK with hρ
  set Inn : Subgroup (MulAut (barOf 3 K)) :=
    (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range with hInn
  set Qin : Subgroup ↥Q := Inn.comap ρ with hQin
  have hqin : (⟨q, hqQ⟩ : ↥Q) ∈ Qin := by
    obtain ⟨k, hk, hkey⟩ := hin
    exact ⟨_, (rhoQ_eq_conj c.hQK hqQ hk hkey).symm⟩
  have hconj_inj : Function.Injective (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)) :=
    L2.conj_injective e0
  have hInncard : Nat.card ↥Inn = 9828 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv]
    exact L2.card_eq_9828 e0
  set ρ' : ↥Qin →* MulAut (barOf 3 K) := ρ.comp Qin.subtype with hρ'
  have hker : Nat.card ↥ρ'.ker ≤ 3 := by
    set f : ↥Qin →* G := Q.subtype.comp Qin.subtype with hf
    have hfinj : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
    have hle : ρ'.ker.map f ≤ centBar 3 Q K := by
      rintro _ ⟨t, ht, rfl⟩
      exact (Lemma113d.rhoQ_eq_one_iff c.hQK (t : ↥Q)).1 ht
    calc Nat.card ↥ρ'.ker = Nat.card ↥(ρ'.ker.map f) :=
          (Subgroup.card_map_of_injective hfinj).symm
      _ ≤ Nat.card ↥(centBar 3 Q K) := Subgroup.card_le_of_le hle
      _ ≤ 3 := c.centBar_card_le_three hB
  have hrange : Nat.card ↥ρ'.range ≤ 27 := by
    have hrle : ρ'.range ≤ Inn := by
      rintro _ ⟨t, rfl⟩
      exact t.2
    have hdvd : Nat.card ↥ρ'.range ∣ 9828 := hInncard ▸ Subgroup.card_dvd_of_le hrle
    have hp : IsPGroup 3 ↥ρ'.range := by
      rw [MonoidHom.range_eq_map]
      exact (IsPGroup.to_subgroup (c.hQp.to_subgroup Qin) ⊤).map ρ'
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hp
    rw [hj] at hdvd ⊢
    have hj3 : j ≤ 3 := by
      by_contra h
      push Not at h
      have h81 : 81 ∣ 3 ^ j := by
        have : 3 ^ 4 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
        simpa using this
      have := h81.trans hdvd
      omega
    calc 3 ^ j ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
      _ = 27 := by norm_num
  have hQincard : Nat.card ↥Qin ≤ 81 := by
    have h := Subgroup.card_ker_mul_card_range ρ'
    rw [← h]
    calc Nat.card ↥ρ'.ker * Nat.card ↥ρ'.range ≤ 3 * 27 := Nat.mul_le_mul hker hrange
      _ = 81 := by norm_num
  set S : Subgroup G := Qin.map Q.subtype with hS
  have hSE : E ≤ S := by
    rw [c.hEeq]
    apply sup_le
    · intro y hy
      refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      exact Lemma113d.rhoQ_mem_inner c.hQK ⟨y, hy.1⟩ hy.2
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨e, c.heQ⟩, ?_, rfl⟩
      have h1 : ρ ⟨e, c.heQ⟩ = 1 := (Lemma113d.rhoQ_eq_one_iff c.hQK ⟨e, c.heQ⟩).2 c.e_mem_centBar
      show ρ ⟨e, c.heQ⟩ ∈ Inn
      rw [h1]
      exact Inn.one_mem
  have hScard : Nat.card ↥S ≤ Nat.card ↥E := by
    rw [hS, Subgroup.card_map_of_injective Q.subtype_injective, c.hEcard]
    simpa using hQincard
  have hSeq : E = S := Subgroup.eq_of_le_of_card_ge hSE hScard
  rw [hSeq]
  exact ⟨⟨q, hqQ⟩, hqin, rfl⟩

end CtxN

end N

end Lemma113Claims

theorem pieceD_subOut_holds : Lemma113g.PieceD_SubOut := by
  intro G _ _ m B M E A a e K Q h _ x hx n hn
  exact Lemma113Claims.N.subOut_core h.hK.2 hx hn

theorem pieceD_subNorm_holds : Lemma113g.PieceD_SubNorm := by
  intro G _ _ m B M E A a e K Q h _
  have h0 := lemma113_ii_piece0_holds h
  have hA := lemma113_ii_pieceA_of_inputs' Lemma113Claims.hC113 h h0
  have hB := lemma113_ii_pieceB_holds' h hA
  have c := Lemma113Claims.Ctx.of_cfg h hA
  refine ⟨hA.2.2.1, ?_, fun q hq hin => ?_⟩
  · exact Lemma113d.normalizer_zpowers_le_normalizer_K rfl c.hQ c.hQ1 c.hXN c.hKX h.hK.1 c.hKI
      c.he3 c.he1 hA.2.1 (c.hAQ h.ha.1) h0
  · exact Lemma113Claims.N.CtxN.inner_mem_E c hB hq hin

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
