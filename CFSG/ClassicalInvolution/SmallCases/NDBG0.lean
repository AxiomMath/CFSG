module

public import CFSG.ClassicalInvolution.Asc77.AscBSE3
public import CFSG.ClassicalInvolution.SmallCases.NDBC8
import CFSG.ClassicalInvolution.Asc77.AscT7AAlpha
import CFSG.ClassicalInvolution.Asc77.AscAETCyc
import CFSG.ClassicalInvolution.ModelFacts.Orth15RVertexExcl
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
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
import CFSG.ClassicalInvolution.Asc77.AscT7CWz
import CFSG.ClassicalInvolution.Asc77.AscT7D242
import CFSG.ClassicalInvolution.Asc77.AscT7EC23
import CFSG.ClassicalInvolution.Asc77.AscT7HC5
import CFSG.ClassicalInvolution.Asc77.AscT7K11
import CFSG.ClassicalInvolution.Asc77.AscT7L1
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBG

section Nbr

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_omegaNbr_of_tq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hKz : IsUniqueInvolution K z) {N : Subgroup G}
    (hN : N ∈ tqMembers Ω z) {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    N ∈ omegaNbr Ω K := by
  have hNΩ : N ∈ Ω := hN.1
  have hzN : z ∈ trivialOnQuot N := hN.2
  have hzN' : z ∈ Subgroup.normalizer (N : Set G) := (mem_trivialOnQuot_iff.mp hzN).1
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one
  obtain ⟨R, hRsyl, hRinv⟩ := T3.exists_sylow_normalized hz2 (Subgroup.zpowers_le.mpr hzN')
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) :=
    AscAET.le_centralizer_of_conjSub_eq hzN hRsyl.1 hRsyl.2.1 (hRinv z (Subgroup.mem_zpowers z))
  have hNK : N ≠ K := by
    intro h
    apply hnz
    have hnU : IsUniqueInvolution N n :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hn
    rw [h] at hnU
    exact hnU.eq hKz
  have hRR : R ∈ RSet Ω := mem_RSet_of_isSylow2In hNΩ hRsyl
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp hRR
  exact ⟨hNΩ, hNK, R, hRR, hRsyl.1,
    hΩ.le_normalizer_of_le_centralizer hp hq hK hNΩ hNK.symm hKz hRsyl.1 hRsyl.2.1 (by omega)
      hRC⟩

theorem mem_omegaOfSet_of_tq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hKz : IsUniqueInvolution K z) {N : Subgroup G}
    (hN : N ∈ tqMembers Ω z) {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    N ∈ omegaOfSet Ω (twinSet Ω K) := by
  have hnbr := mem_omegaNbr_of_tq hp hq hΩ hK hKz hN hn hnz
  refine T7A.mem_omegaOfSet_of_mem_kPerp hp hq hΩ hK (Set.mem_insert_of_mem _ hnbr) ?_
  rintro ⟨-, w, hwK, hwN⟩
  have hnU : IsUniqueInvolution N n := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hn
  exact hnz ((hnU.eq hwN).trans (hwK.eq hKz))

end Nbr

section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem exists_far_member {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2)) :
    ∃ N ∈ tqMembers (𝒞 K) z, ∃ n : G, IsClassicalMember p f N n ∧ n ≠ z := by
  obtain ⟨N, m, -, hN⟩ := BSC.BSE.exists_conj_twins hno hb
  obtain ⟨j₀, hj₀, -⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨htq, hcl, R, hR, himg, -⟩ := hN ⟨j₀, hj₀b⟩
  exact ⟨_, htq, m, hcl, Cover.ne_z_of_le_nonA1 C hb htq hcl hR himg⟩

theorem three_le_card_of_twin {Ω : Set (Subgroup G)} (C : XCtx p f Ω z) {b : Fin C.D.card}
    (hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2)) {T : Subgroup G} (hT : T ∈ Ω) (hTK : T ≠ C.K)
    (hTz : IsClassicalMember p f T z) : 3 ≤ C.D.card := by
  obtain ⟨j₀, hj₀, hjK⟩ := C.exists_A1_of_K
  obtain ⟨j₁, hj₁, hjT⟩ := C.exists_A1_of_member hT hTz
  have h01 : j₀ ≠ j₁ := by
    intro h
    apply hTK
    refine (Cover.eq_of_modOdd_eq C.K_cl hTz ?_).symm
    rw [← C.exactCore_K, hjK, hjT, h]
  have h0b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  have h1b : j₁ ≠ b := fun h => hb (h ▸ hj₁)
  have e01 : j₀.val ≠ j₁.val := fun h => h01 (Fin.ext h)
  have e0b : j₀.val ≠ b.val := fun h => h0b (Fin.ext h)
  have e1b : j₁.val ≠ b.val := fun h => h1b (Fin.ext h)
  have := j₀.2
  have := j₁.2
  have := b.2
  omega

theorem false_of_trialityD4_of_card {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hD4 : C.D.tag b = .trialityD4) (hcard : 3 ≤ C.D.card) : False := by
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [hD4] at h
    exact absurd h.1 (by decide)
  obtain ⟨N, m, hinj, hN⟩ := BSC.BSE.exists_conj_twins hno hb
  obtain ⟨j₀, hj₀, -⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨e, hej, heb⟩ := Fin.exists_ne_and_ne_of_two_lt j₀ b (by omega : 2 < C.D.card)
  let i₀ : {j : Fin C.D.card // j ≠ b} := ⟨j₀, hj₀b⟩
  let i₁ : {j : Fin C.D.card // j ≠ b} := ⟨e, heb⟩
  have h01 : N i₁ ≠ N i₀ := fun h => hej (congrArg Subtype.val (hinj h))
  obtain ⟨h0tq, h0cl, R₀, hR₀, himg₀, -⟩ := hN i₀
  obtain ⟨h1tq, h1cl, R₁, hR₁, himg₁, -⟩ := hN i₁
  exact false_of_trialityD4_sec C.hp C.hq C.hΩ C.hc2 C.D b hD4 h0tq h1tq h0cl h1cl h01
    (himg₀ ▸ Subgroup.map_le_range _ _) (himg₁ ▸ Subgroup.map_le_range _ _)

end Twins

end NDBG

end CFSG.ClassicalInvolution.NDB
