module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenSixXOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LieType.BorelTits.Basic
import CFSG.Assembly.Subnormal
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenSixOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeCfg
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup


theorem threeSevenList_of_noTwo
    (hK : KFactNineThreeNoTwo) {p : ℕ} {K : Type} [Group K] [Finite K] (hp : p.Prime)
    (hp2 : p ≠ 2) (hlist : NineThreeListGroup p K) (hZ : Subgroup.center K = ⊥)
    (T : Sylow p K) (S : Subgroup (MulAut K)) (hS : IsPGroup 2 S)
    (hnorm : ∀ t ∈ (T : Subgroup K), MulAut.conj t ∈ normalizer (S : Set (MulAut K))) :
    S = ⊥ ∨ (p = 3 ∧ IsLinThreeFour K) := by
  by_cases hL : p = 3 ∧ IsLinThreeFour K
  · exact Or.inr hL
  left
  haveI : Fact p.Prime := ⟨hp⟩
  set c : K →* MulAut K := MulAut.conj with hc
  have hinj : Function.Injective c := RankOneCent.conj_injective_of_center hZ
  set I := c.range with hI
  haveI : I.Normal := RankOneCent.conj_range_normal
  let e : K ≃* I := MonoidHom.ofInjective hinj
  have he : ∀ k, (e k : MulAut K) = c k := fun k => MonoidHom.ofInjective_apply hinj
  have hlist' : NineThreeListGroup p I := by
    rcases hlist with ⟨i, hi, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
    · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
    · exact Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩
  have hL' : ¬ (p = 3 ∧ IsLinThreeFour I) := by
    rintro ⟨h3, d, hd, ⟨f⟩⟩
    exact hL ⟨h3, d, hd, ⟨e.trans f⟩⟩
  set T' : Sylow p I := T.mapSurjective (f := e.toMonoidHom) e.surjective with hT'
  have hTS : (T' : Subgroup I).map I.subtype ≤ normalizer (S : Set (MulAut K)) := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have : (I.subtype (e.toMonoidHom t)) = c t := he t
    rw [this]
    exact hnorm t ht
  have hcen := le_centralizer_of_nineThreeList hK hp hp2 hlist' hL' T' hS hTS
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  ext k
  have h1 := Subgroup.mem_centralizer_iff.mp (hcen hσ) (c k) ⟨k, rfl⟩
  have h2 : c (σ k) = c k := by
    ext g
    have := congrArg (fun τ : MulAut K => τ (σ⁻¹ g)) h1
    simp only [MulAut.mul_apply, hc, MulAut.conj_apply, MulAut.apply_inv_self] at this
    simp only [hc, MulAut.conj_apply]
    rw [this, map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  exact hinj h2

variable {G : Type} [Group G] [Finite G]

open TenSixX

theorem agl81TenSixX_of_noTwo
    (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR2 : KFactNineThreeRankTwo) (hK : KFactNineThreeNoTwo) : AGL81TenSixX G := by
  intro hS p P M H Q K hd L hL I₀ hI₀ hIX
  by_contra hcon
  have hnX : ¬ I₀ ≤ d1PlusCore p H K := fun h => hcon (Or.inl h)
  have hnL : ¬ (p = 3 ∧ IsLinThreeFour K) := fun h => hcon (Or.inr h)
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hp : p.Prime := he.prime
  have hp2 : p ≠ 2 := he.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hS.simple
  have hHtop : H ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hd.maxH.1
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hKne : d1KBar p M H ≠ ⊥ := by
    intro h
    apply hd.not_le_X0
    rw [hd.kbar, h]
    exact bot_le
  have hlist : NineThreeListGroup p (d1KBar p M H) :=
    nineThreeListGroup_d1KBar_of_escape h31 h75 hR2 hS hS.kProper he hd.base hd.le_H hHtop hKne
  have hZ : Subgroup.center (d1KBar p M H) = ⊥ :=
    center_d1KBar_eq_bot_of_escape h31 hS.kProper he hd.base hd.le_H hHtop hKne
  rw [← hd.kbar] at hlist hZ
  have hXN : d1X0 p M H ≤ normalizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.kbar]
    exact d1X0_le_normalizer_d1KBar p M H
  set Nn := normalizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hNn
  set ρ := K.normalizerMonoidHom with hρ
  set B := ((d1X0 p M H).subgroupOf Nn).map ρ with hB
  set Ib := (I₀.subgroupOf H).map π with hIb
  set S₀ := (Ib.subgroupOf Nn).map ρ with hS₀
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hI₀M : I₀ ≤ M := hI₀.le.trans (inf_le_right.trans hL.le)
  have hsub2 : IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hL.subnormal.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  have hI₀sub : IsSubnormal I₀ (H ⊓ M) := hI₀.subnormal.trans hsub2
  have hsubIb : IsSubnormal Ib (d1X0 p M H) := (hI₀sub.comap H.subtype).map π
  have hsubS : IsSubnormal S₀ B := (hsubIb.comap Nn.subtype).map ρ
  have hker : ∀ (y : Nn), (y : H ⧸ primeComplementCore (G := H) p) ∈
      Subgroup.centralizer (K : Set _) → ρ y = 1 := by
    intro y hy
    have : y ∈ ρ.ker := by
      rw [hρ, Subgroup.normalizerMonoidHom_ker]
      exact hy
    exact this
  have hS2 : IsPGroup 2 S₀ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨x', hx', hxy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
    have hx'I₀ : (x' : G) ∈ I₀ := hx'
    obtain ⟨a, ha⟩ := exists_pow_two_mem_oUpperTwo hx'I₀
    refine ⟨a, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    apply hker
    have h1 : ((y ^ 2 ^ a : Nn) : H ⧸ primeComplementCore (G := H) p) = π (x' ^ 2 ^ a) := by
      simp only [SubgroupClass.coe_pow, map_pow]
      rw [← hxy]
    rw [h1]
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (hIX ha)
    have : w = x' ^ 2 ^ a := Subtype.ext (by simpa using hwx)
    rw [← this]
    exact hw
  have hSne : S₀ ≠ ⊥ := by
    intro hbot
    apply hnX
    intro x hx
    have hxH : x ∈ H := hI₀H hx
    have hxN : π ⟨x, hxH⟩ ∈ Nn := hXN ⟨⟨x, hxH⟩, ⟨hxH, hI₀M hx⟩, rfl⟩
    have hmem : ρ ⟨π ⟨x, hxH⟩, hxN⟩ ∈ S₀ := ⟨⟨π ⟨x, hxH⟩, hxN⟩, ⟨⟨x, hxH⟩, hx, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hk : (⟨π ⟨x, hxH⟩, hxN⟩ : Nn) ∈ ρ.ker := hmem
    rw [hρ, Subgroup.normalizerMonoidHom_ker] at hk
    exact ⟨⟨x, hxH⟩, hk, rfl⟩
  have hle : S₀ ≤ pCoreOf 2 B :=
    CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hsubS hS2
  obtain ⟨T, hT⟩ := hd.sylowK
  have hnorm : ∀ t ∈ (T : Subgroup K), MulAut.conj t ∈
      normalizer (pCoreOf 2 B : Set (MulAut ↥K)) := by
    intro t ht
    have htK : (t : H ⧸ primeComplementCore (G := H) p) ∈
        (Q.subgroupOf H).map π ⊓ K := by
      rw [← hT]
      exact ⟨t, ht, rfl⟩
    obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp htK.1
    have hqX0 : (t : H ⧸ primeComplementCore (G := H) p) ∈ d1X0 p M H :=
      ⟨q, ⟨q.2, hd.base.1 (Subgroup.mem_subgroupOf.mp hq)⟩, hqt⟩
    have htN : (t : H ⧸ primeComplementCore (G := H) p) ∈ Nn := hXN hqX0
    have hρt : ρ ⟨t, htN⟩ = MulAut.conj t := by
      ext k
      simp [hρ, MulAut.conj_apply]
    have hBt : MulAut.conj t ∈ B := ⟨⟨t, htN⟩, hqX0, hρt⟩
    exact localGroup_le_normalizer_pCoreOf 2 B hBt
  rcases threeSevenList_of_noTwo hK hp hp2 hlist hZ T (pCoreOf 2 B)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B) hnorm with h | h
  · exact hSne (eq_bot_iff.mpr (hle.trans h.le))
  · exact hnL h

end CFSG.LocalAnalysis.RankThreeTheoremC
