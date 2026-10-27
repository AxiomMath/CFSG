module

public import CFSG.ClassicalInvolution.SmallCases.NDBC0
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootCtx
public import CFSG.ClassicalInvolution.SmallCases.DSplitChain
import CFSG.ClassicalInvolution.Asc77.WP3SCSModel
import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
import CFSG.ClassicalInvolution.Asc77.AscFusionS14
import CFSG.ClassicalInvolution.Asc77.WP3LayerLie
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyEdge
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnConj
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
import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.Dichotomy (involutionOddCore)

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Cover

section Class

variable {G : Type} [Group G]

theorem conjClass_eq_of_mem {K L : Subgroup G} (hL : L ∈ 𝒞 K) : 𝒞 L = 𝒞 K := by
  obtain ⟨g₀, rfl⟩ := hL
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * g₀, by show conjSub (g * g₀) K = conjSub g (conjSub g₀ K); rw [conjSub_mul]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * g₀⁻¹, by
      show conjSub (g * g₀⁻¹) (conjSub g₀ K) = conjSub g K
      rw [conjSub_mul, conjSub_inv_conjSub]⟩

end Class

section Edge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exists_tq_ne {K : Subgroup G} {z : G} (hS : Setting p f K z) :
    ∃ N ∈ tqMembers (𝒞 K) z, ∃ n : G, IsClassicalMember p f N n ∧ n ≠ z := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; have := hS.five; simp at this)
  by_contra hcon
  push Not at hcon
  have huniq : ∀ {L : Subgroup G} {a b : G}, IsClassicalMember p f L a →
      IsClassicalMember p f L b → b = a :=
    fun ha hb => ha.eq_of_isCentralInvolution hS.odd hf hb.isCentralInvolution
  have hinv := (inClass_conjugates hS.member).conjInvariant
  have htr : ∀ g : G, ∀ N ∈ tqMembers (𝒞 K) (g * z * g⁻¹), ∀ n : G,
      IsClassicalMember p f N n → n = g * z * g⁻¹ := by
    intro g N hN n hn
    have hN' : conjSub g⁻¹ N ∈ tqMembers (𝒞 K) z := by
      refine ⟨hinv g⁻¹ N hN.1, ?_⟩
      have h1 := Theorem5.mem_trivialOnQuot_conj_of_mem hN.2 g⁻¹
      have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
      rwa [e] at h1
    have h1 := hcon _ hN' _ (hn.conj g⁻¹)
    calc n = g * (g⁻¹ * n * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [h1]
  have hall : ∀ L ∈ 𝒞 K, L ∈ 𝒞 K ∧ IsClassicalMember p f L z := by
    intro L hL
    have hpath := Disconnected.tqChain_of_dConnected hS.odd hS.five hS.member hS.dconn K
      (mem_conjClass_self K) L hL
    clear hL
    induction hpath with
    | refl => exact ⟨mem_conjClass_self K, hS.member⟩
    | @tail M N _ hstep ih =>
      obtain ⟨hM, hMz⟩ := ih
      obtain ⟨hN, hE⟩ := hstep
      refine ⟨hN, ?_⟩
      obtain ⟨g, rfl⟩ := hN
      have hNc := hS.member.conj g
      rcases hE with ⟨a, ha, hNa⟩ | ⟨a, ha, hMa⟩
      · have haz : a = z := huniq hMz ha
        rw [haz] at hNa
        have hNtq : conjSub g K ∈ tqMembers (𝒞 K) z :=
          ⟨⟨g, rfl⟩, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr hNa⟩
        have e := hcon _ hNtq _ hNc
        rwa [e] at hNc
      · have hag : a = g * z * g⁻¹ := huniq hNc ha
        rw [hag] at hMa
        have hMtq : M ∈ tqMembers (𝒞 K) (g * z * g⁻¹) :=
          ⟨hM, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr hMa⟩
        have e := htr g M hMtq z hMz
        rwa [← e] at hNc
  refine singleton_not_subset_center hS.nonabelian hS.member.isCentralInvolution.ne_one ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  have h2 := huniq (hS.member.conj g) (hall (conjSub g K) ⟨g, rfl⟩).2
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [← h2]

end Edge

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

theorem hypOmegaMod (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G)) :
    Asc77.HypOmegaMod p f (𝒞 K) :=
  Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f) G hnab hp2 hq K z hz
    hBelow

theorem nonempty_lieSystem (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G)) :
    Nonempty (LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) := by
  have hΩ := hypOmegaMod hnab hp2 hq hz hBelow
  exact lieSystemAt_exactFamily hΩ.conjInvariant hΩ.classical
    (isPGroup_zpowers_of_sq_eq_one hz.isCentralInvolution.sq) hBelow
    (singleton_not_subset_center hnab hz.isCentralInvolution.ne_one)
    ⟨K, mem_tqMembers_of_isClassicalMember (mem_conjClass_self K) hz⟩

@[expose] noncomputable def toXCtx (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) : Asc77.XCtx p f (𝒞 K) z where
  K := K
  hK := mem_conjClass_self K
  hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  hΩ := hypOmegaMod hnab hp2 hq hz hBelow
  hp := hp2
  hq := hq
  D := D

end Ctx

section Sym

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem mem_trivialOnQuot_K (C : Asc77.XCtx p f Ω z) {N : Subgroup G}
    (hN : N ∈ tqMembers Ω z) {n : G} (hn : IsClassicalMember p f N n) (hNK : N ≠ C.K) :
    n ∈ trivialOnQuot C.K := by
  have hzC := Asc77.XCtx.hzC z
  obtain ⟨i₀, hi₀, hK₀⟩ := C.exists_A1_of_K
  obtain ⟨j, R, hR, hRN⟩ := C.exists_fund_of_mem hN
  have hnC := C.involution_mem_centralizer hN hn
  have hnN : oddQuotMk z ⟨n, hnC⟩ ∈ modOdd z (exactCore z N) :=
    oddQuotMk_mem_modOdd (C.involution_mem_exactCore hN hn) hnC
  by_cases hj : j = i₀
  · exfalso
    subst hj
    rw [C.fund_eq_top j hi₀ hR, Subgroup.map_top] at hRN
    have hzR : oddQuotMk z ⟨z, hzC⟩ ∈ (C.psi j).range := by
      rw [← hK₀, C.exactCore_K]
      exact oddQuotMk_mem_modOdd C.K_cl.mem hzC
    have hnz : n = z := C.classical_of_range hN hn hRN.symm hzR
    rw [hnz] at hn
    have hNe : exactCore z N = N := exactCore_eq_self hn.perfect (isSubnormal_le hn.subnormal)
    refine hNK (eq_of_modOdd_eq hn C.K_cl ?_)
    rw [← hNe, ← hRN, ← hK₀, C.exactCore_K]
  · refine mem_trivialOnQuot_of_centralizes_modOdd C.K_cl
      (isCanonical_of_isClassicalMember C.K_cl) hnC ?_
    intro y hy
    rw [← C.exactCore_K, hK₀] at hy
    obtain ⟨a, rfl⟩ := hy
    have hnR : oddQuotMk z ⟨n, hnC⟩ ∈ (C.psi j).range := by
      rw [← hRN] at hnN
      exact Subgroup.map_le_range _ _ hnN
    obtain ⟨b, hb⟩ := hnR
    rw [← hb]
    exact C.psi_commute hj b a

end Sym

end Cover

end CFSG.ClassicalInvolution.NDB
