module

public import CFSG.ClassicalInvolution.SmallCases.NDBG8
import CFSG.ClassicalInvolution.Asc77.AscAETSecFinal
import CFSG.ClassicalInvolution.SmallCases.NDBG5Weak
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB.NDBH3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem mem_omegaOfSet_twinSet {Ω : Set (Subgroup G)} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K N : Subgroup G} {z n : G} (hKz : IsUniqueInvolution K z)
    (hN : N ∈ tqMembers Ω z) (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    N ∈ omegaOfSet Ω (twinSet Ω K) := by
  refine ⟨hN.1, fun M hM => ?_⟩
  obtain ⟨hMΩ, w, hwK, hwM⟩ := hM
  have hwz : w = z := hwK.eq hKz
  subst hwz
  have hne : N ≠ M := by
    intro h
    rw [h] at hn
    exact hnz ((ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hn).eq hwM)
  exact mem_omegaNbr_of_trivialOnQuot hp2 hq hΩ hMΩ hwM hN.1 hne hN.2


theorem false_of_aViol_of_tags {Ω : Set (Subgroup G)} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {c : G} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (D₀ : LocalLieSystemAt p f (exactFamily Ω c) c)
    (htag : ∀ i, D₀.tag i ≠ .G2 ∧ D₀.tag i ≠ .trialityD4) {M J : Subgroup G} {zM zJ : G}
    (hM : M ∈ Ω) (hv : AViol Ω M J zM zJ) (hMc : c ∈ trivialOnQuot M)
    (hJc : c ∈ trivialOnQuot J) : False := by
  obtain ⟨zK, zL, hv'⟩ := AscAET.exists_aViol_exactPair hp hq hΩ hc2 hM hv hMc hJc
  have hΛ : HypOmegaMod p f
      (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hKt : M ∈ tqMembers Ω c := ⟨hM, hMc⟩
  have hKcm : exactCore c M ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hKt, exactCore_le_centralizer c M⟩
  have hKY : exactCore c M ≤ exLayer Ω c := le_centLayer hKcm
  have hK : (exactCore c M).subgroupOf (exLayer Ω c) ∈
      restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c) :=
    subgroupOf_mem_restrictFamily hKcm hKY
  obtain ⟨a, hQ⟩ := T3Typed.quotViol_of_aViol hp hq hΛ hK hv'
  have hs : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hKt⟩
  let D : OmegaLie p f (secFam Ω c) := LieSystemData.toOmegaLie D₀ (omegaGen_secFam hs)
  have hΦ : HypOmegaMod p f (secFam Ω c) := hypOmegaMod_secFam hp hq hΩ hc2
  obtain ⟨i, R, S, hR, hS, hKR, hJS⟩ := T3Typed.QuotViol.exists_components D hQ
  rw [hKR, hJS] at hQ
  exact T3Typed.QuotViol.false_of_classical hp hq hΦ D (htag i).1 (htag i).2 hR hS hQ

theorem aEmpty_of_allA1 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hΩK : HypOmegaMod p f (𝒞 K)) (hz : IsClassicalMember p f K z)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) (hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2)
    {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {n : G} (hn : IsClassicalMember p f N n)
    (hnz : n ≠ z) : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := by
  have hall' : ∀ J ∈ 𝒞 K, ∃ g : G, conjSub g K = J := by
    rintro J ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one
  have htag : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := fun i => by
    rw [(hall i).1]
    exact ⟨by decide, by decide⟩
  have hA : AEmpty (𝒞 K) K := by
    by_contra hne
    obtain ⟨J, zK, zJ, hv⟩ := T3.not_aEmpty_iff.mp hne
    have hL₀ : N ∈ omegaOfSet (𝒞 K) (twinSet (𝒞 K) K) :=
      mem_omegaOfSet_twinSet hp2 hq hΩK hKz hN hn hnz
    obtain ⟨h, hh⟩ := hall' N hL₀.1
    have hKW : K ∈ omegaOfSet (𝒞 K) (twinSet (𝒞 K) (conjSub h⁻¹ K)) := by
      have := AscAET.omegaOfSet_conj hΩK.conjInvariant hL₀ h⁻¹
      rwa [← hh, conjSub_inv_conjSub] at this
    have hM'Ω : conjSub h⁻¹ K ∈ 𝒞 K := hΩK.conjInvariant h⁻¹ K (CoreAssembly.mem_conjClass_self K)
    obtain ⟨g, hg⟩ := hall' _ hM'Ω
    have hv' := hv.conj hΩK.conjInvariant g
    rw [hg] at hv'
    obtain ⟨J', zJ', hv'', hMc, hJc⟩ :=
      AscAET.exists_weak_transfer hp2 hq hΩK hM'Ω hv' hKW hKz
    exact false_of_aViol_of_tags hp2 hq hΩK hc2 D htag hM'Ω hv'' hMc hJc
  exact T3.aEmpty_forall_of_transitive' hΩK.conjInvariant hall' hA

end CFSG.ClassicalInvolution.NDB.NDBH3
