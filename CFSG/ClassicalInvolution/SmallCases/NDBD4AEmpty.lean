module

public import CFSG.ClassicalInvolution.SmallCases.NDBC8
public import CFSG.ClassicalInvolution.Asc77.AscAETFinal
import CFSG.ClassicalInvolution.Asc77.ModOApi
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
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.AschTight.Sec7L713E
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.NDB.D4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T3 CFSG.ClassicalInvolution.Asc77.AscAET
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

section Tags

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem false_of_aViol_of_tags (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (D₀ : LocalLieSystemAt p f (exactFamily Ω c) c)
    (htag : ∀ i, D₀.tag i ≠ .G2 ∧ D₀.tag i ≠ .trialityD4) {M J : Subgroup G} {zM zJ : G}
    (hM : M ∈ Ω) (hv : AViol Ω M J zM zJ) (hMc : c ∈ trivialOnQuot M)
    (hJc : c ∈ trivialOnQuot J) : False := by
  obtain ⟨zK, zL, hv'⟩ := exists_aViol_exactPair hp hq hΩ hc2 hM hv hMc hJc
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

end Tags

section AEmpty

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem mem_omegaOfSet_twinSet (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} {z : G} (hKz : IsUniqueInvolution K z)
    {J : Subgroup G} {t : G} (hJ : J ∈ tqMembers Ω z) (hJt : IsClassicalMember p f J t)
    (htz : t ≠ z) : J ∈ omegaOfSet Ω (twinSet Ω K) := by
  refine ⟨hJ.1, fun M hM => ?_⟩
  obtain ⟨hMΩ, w, hwK, hwM⟩ := hM
  have hwz : w = z := (hKz.eq hwK).symm
  subst hwz
  have hne : J ≠ M := by
    intro hJM
    rw [← hJM] at hwM
    exact htz ((ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hJt).eq hwM)
  exact mem_omegaNbr_of_trivialOnQuot hp2 hq hΩ hMΩ hwM hJ.1 hne hJ.2

theorem aEmpty_of_tags (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hΩ : HypOmegaMod p f (𝒞 K)) (hz : IsClassicalMember p f K z)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    (htag : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) {J : Subgroup G} {t : G}
    (hJ : J ∈ tqMembers (𝒞 K) z) (hJt : IsClassicalMember p f J t) (htz : t ≠ z) :
    ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := by
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_sq_eq_one hKz.sq
  have hall : ∀ L ∈ 𝒞 K, ∃ g : G, conjSub g K = L := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hJW := mem_omegaOfSet_twinSet hp2 hq hΩ hKz hJ hJt htz
  have hA : AEmpty (𝒞 K) K := by
    by_contra hn
    obtain ⟨J₀, zK, zJ, hv⟩ := T3.not_aEmpty_iff.mp hn
    obtain ⟨h, hh⟩ := hall J hJ.1
    have hKW : K ∈ omegaOfSet (𝒞 K) (twinSet (𝒞 K) (conjSub h⁻¹ K)) := by
      have := AscAET.omegaOfSet_conj hΩ.conjInvariant hJW h⁻¹
      rwa [← hh, conjSub_inv_conjSub] at this
    have hM'Ω : conjSub h⁻¹ K ∈ 𝒞 K := hΩ.conjInvariant h⁻¹ K (mem_conjClass_self K)
    obtain ⟨g, hg⟩ := hall _ hM'Ω
    have hv' := hv.conj hΩ.conjInvariant g
    rw [hg] at hv'
    obtain ⟨J', zJ', hv'', hMc, hJc⟩ :=
      AscAET.exists_weak_transfer hp2 hq hΩ hM'Ω hv' hKW hKz
    exact false_of_aViol_of_tags hp2 hq hΩ hc2 D htag hM'Ω hv'' hMc hJc
  exact T3.aEmpty_forall_of_transitive' hΩ.conjInvariant hall hA

theorem aEmpty_of_d4 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G))
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {i₁ : Fin D.card}
    (hi₁ : D.tag i₁ = .POmegaPlus ∧ D.rank i₁ = 4) : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := by
  set C := Cover.toXCtx hnab hp2 hq hz hBelow D with hC
  have hQ : ¬ (C.D.tag i₁ = .PSL ∧ C.D.rank i₁ = 2) := fun h => by
    have h1 : D.tag i₁ = .PSL := h.1
    rw [hi₁.1] at h1
    exact absurd h1 (by decide)
  have htag : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    by_cases hi : i = i₁
    · subst hi
      rw [hi₁.1]
      exact ⟨by decide, by decide⟩
    · have hA1 : C.D.tag i = .PSL ∧ C.D.rank i = 2 := by
        by_contra h
        exact Cover.false_of_two_nonA1 C hnoF hi h hQ
      have h1 : D.tag i = .PSL := hA1.1
      rw [h1]
      exact ⟨by decide, by decide⟩
  obtain ⟨R, hR, J, hJ, hJR⟩ := Cover.exists_member_of_meets C i₁
  obtain ⟨t, ht⟩ := C.hΩ.classical J hJ.1
  exact aEmpty_of_tags hp2 hq C.hΩ hz D htag hJ ht (Cover.ne_z_of_le_nonA1 C hQ hJ ht hR hJR)

end AEmpty

end CFSG.ClassicalInvolution.NDB.D4
