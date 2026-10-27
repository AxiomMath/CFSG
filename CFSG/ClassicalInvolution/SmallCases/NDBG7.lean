module

public import CFSG.ClassicalInvolution.SmallCases.NDBG2
public import CFSG.ClassicalInvolution.SmallCases.DSplitChain
import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnMember
import CFSG.ClassicalInvolution.Generic.StepQuasisimple
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

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBG

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exists_tq_ne (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hconn : Disconnected.DConnected (𝒞 K)) :
    ∃ N ∈ tqMembers (𝒞 K) z, ∃ n : G, IsClassicalMember p f N n ∧ n ≠ z := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  by_contra hcon
  push Not at hcon
  have huniq : ∀ {L : Subgroup G} {a b : G}, IsClassicalMember p f L a →
      IsClassicalMember p f L b → b = a :=
    fun ha hb => ha.eq_of_isCentralInvolution hp2 hf hb.isCentralInvolution
  have hinv := (inClass_conjugates hz).conjInvariant
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
    have hpath := Disconnected.tqChain_of_dConnected hp2 hq hz hconn K (mem_conjClass_self K) L hL
    clear hL
    induction hpath with
    | refl => exact ⟨mem_conjClass_self K, hz⟩
    | @tail M N _ hstep ih =>
      obtain ⟨hM, hMz⟩ := ih
      obtain ⟨hN, hE⟩ := hstep
      refine ⟨hN, ?_⟩
      obtain ⟨g, rfl⟩ := hN
      have hNc := hz.conj g
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
  refine singleton_not_subset_center hnab hz.isCentralInvolution.ne_one ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  have h2 := huniq (hz.conj g) (hall (conjSub g K) ⟨g, rfl⟩).2
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [← h2]

end NDBG

variable (p f : ℕ) [Fact p.Prime]

@[expose] def NoAllA1Other : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, (∀ i, D.tag i = .PSL ∧ D.rank i = 2) →
        ∀ N ∈ tqMembers (𝒞 K) z, ∀ n : G, IsClassicalMember p f N n → n ≠ z → False

@[expose] def NoAllA1Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ¬ ∀ i, D.tag i = .PSL ∧ D.rank i = 2

variable {p f}

theorem noAllA1Core_of_other (h : NoAllA1Other p f) : NoAllA1Core p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall
  obtain ⟨N, hN, n, hn, hnz⟩ := NDBG.exists_tq_ne hnab hp2 hq hz hconn
  exact h G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz

theorem noAllA1_of_core (h : NoAllA1Core p f) : NoAllA1 p f :=
  fun G _ _ _ K z hS D => h G hS.nonabelian hS.odd hS.five K z hS.member hS.below hS.dconn
    (fuzzyFrameExcluded G K z hS) D

theorem bootNoAllA1_of_core (h : NoAllA1Core p f) : Asc77.BSC.BootNoAllA1 p f :=
  fun G _ _ _ K z hS D => h G hS.nonabelian hS.odd hS.five K z hS.member hS.below hS.dconn
    (Asc77.BSC.noFuzzyFrame hS) D

end CFSG.ClassicalInvolution.NDB
