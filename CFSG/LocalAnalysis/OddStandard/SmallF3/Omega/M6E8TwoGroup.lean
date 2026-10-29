module

public import CFSG.GH74.Defs
import CFSG.GH74.SectionalRankExtension
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Cyc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Shape

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem m6e8_rank_le_three {T K : Subgroup G} (hT : IsPGroup 2 T) (hKT : K ≤ T)
    (hKi : K.relIndex T = 2)
    (hK2 : CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups K) :
    CFSG.GH74.sectionalTwoRank T ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.GH74.sectionalTwoRank_le_iff]
  let N : Subgroup T := K.subgroupOf T
  have hNindex : N.index = 2 := hKi
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hNindex
  have hN2 : CFSG.GH74.SectionalTwoRankLE N 2 := by
    have h2g : CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups ↥N :=
      CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hKT) hK2
    intro P _
    exact h2g P
  have hQ1 : CFSG.GH74.SectionalTwoRankLE (T ⧸ N) 1 := by
    have hcard : Nat.card (T ⧸ N) = 2 := hNindex
    exact CFSG.GH74.SectionalTwoRankLE.of_isCyclic
      (isCyclic_of_prime_card (p := 2) hcard)
  have hmain := CFSG.GH74.SectionalTwoRankLE.of_normal N hN2 hQ1
  simpa using hmain

theorem m6e8_two_group {T K : Subgroup G} {y r : G} (hT : IsPGroup 2 T)
    (hRab : CFSG.Open.IsElemAbelian 2 (T ⊓ centralizer ({y} : Set G)))
    (hR8 : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 8)
    (hrR : r ∈ T ⊓ centralizer ({y} : Set G)) (hry : r ∉ Subgroup.zpowers y)
    (hC8 : 8 < Nat.card ↥(T ⊓ centralizer ({r} : Set G)))
    (hK : K ≤ T ⊓ centralizer ({r} : Set G)) (hyK : y ∈ K) (hrK : r ∈ K)
    (hKi : K.relIndex (T ⊓ centralizer ({r} : Set G)) = 2)
    (hKR : Nat.card ↥(K ⊓ (T ⊓ centralizer ({y} : Set G))) = 4) :
    T ⊓ centralizer ({r} : Set G) = T ∧ CFSG.GH74.sectionalTwoRank T ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKT : K ≤ T := hK.trans inf_le_left
  have hRcomm : ∀ a ∈ T ⊓ centralizer ({y} : Set G),
      ∀ b ∈ T ⊓ centralizer ({y} : Set G), a * b = b * a := by
    haveI : IsMulCommutative ↥(T ⊓ centralizer ({y} : Set G)) := hRab.1
    intro a ha b hb
    simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(T ⊓ centralizer ({y} : Set G)))
      ⟨b, hb⟩)
  have hrR2 : r ^ 2 = 1 := hRab.2 r hrR
  have hrne : r ≠ 1 := by
    intro h
    exact hry (h ▸ Subgroup.one_mem (Subgroup.zpowers y))
  have hr2 : orderOf r = 2 := orderOf_eq_prime hrR2 hrne
  have hKp : IsPGroup 2 K := hT.to_le hKT
  have hcardC : Nat.card ↥K * 2 = Nat.card ↥(T ⊓ centralizer ({r} : Set G)) := by
    have h1 := Subgroup.card_mul_index
      (K.subgroupOf (T ⊓ centralizer ({r} : Set G)))
    have hKi' : (K.subgroupOf (T ⊓ centralizer ({r} : Set G))).index = 2 := hKi
    rw [hKi'] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at h1
    exact h1
  have hKgt4 : 4 < Nat.card K := by
    have h := hC8
    rw [← hcardC] at h
    omega
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKp
  have h8 : 8 ≤ Nat.card K := by
    rw [hn]
    have hn3 : 3 ≤ n := by
      by_contra h
      push Not at h
      have hlt : 4 < 2 ^ n := by rwa [← hn]
      interval_cases n <;> norm_num at hlt
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hKinf : K ⊓ (T ⊓ centralizer ({y} : Set G)) = K ⊓ centralizer ({y} : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr hKT]
  have hcard : Nat.card ↥(K ⊓ centralizer ({y} : Set G)) = 4 := by
    rw [← hKinf]; exact hKR
  have hleR : K ⊓ centralizer ({y} : Set G) ≤ T ⊓ centralizer ({y} : Set G) := by
    intro x hx
    exact ⟨hKT hx.1, hx.2⟩
  have hexp : ∀ x ∈ K ⊓ centralizer ({y} : Set G), x ^ 2 = 1 :=
    fun x hx => hRab.2 x (hleR hx)
  obtain ⟨A, hAK, hAcyc, hAi, h4, hAord, hK2⟩ :=
    m6e8_shape_subgroup hKp hyK hcard hexp h8
  have hltKR : K ⊓ (T ⊓ centralizer ({y} : Set G)) < T ⊓ centralizer ({y} : Set G) := by
    refine lt_of_le_of_ne inf_le_right (fun heq => ?_)
    have : Nat.card ↥(K ⊓ (T ⊓ centralizer ({y} : Set G))) =
        Nat.card ↥(T ⊓ centralizer ({y} : Set G)) := by rw [heq]
    rw [hKR, hR8] at this
    omega
  obtain ⟨c, hcR, hcKR⟩ := (SetLike.lt_iff_le_and_exists.mp hltKR).2
  have hcK : c ∉ K := fun hc => hcKR ⟨hc, hcR⟩
  have hcr : c * r = r * c := hRcomm c hcR r hrR
  have hcC : c ∈ T ⊓ centralizer ({r} : Set G) :=
    ⟨hcR.1, Subgroup.mem_centralizer_singleton_iff.mpr hcr⟩
  have hc2 : c * c = 1 := by simpa [pow_two] using hRab.2 c hcR
  have hrZ : ∀ k ∈ K, k * r = r * k :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hK hk).2
  have hnormC : ∀ g ∈ T, g ∈ normalizer (T ⊓ centralizer ({r} : Set G) : Set G) →
      g ∈ T ⊓ centralizer ({r} : Set G) := by
    intro g hgT hgN
    have hgr := m6e8_normalizer_fixes hK hKi hAK hAcyc hAi h4 hAord hrK hr2 hrZ hcC hcK hc2 hgN
    exact ⟨hgT, Subgroup.mem_centralizer_singleton_iff.mpr hgr⟩
  have hCT : T ⊓ centralizer ({r} : Set G) = T :=
    CFSG.ComponentClassification.AschbacherKnownGroup.Lemma37.eq_of_normalizer_le
      hT inf_le_left hnormC
  refine ⟨hCT, ?_⟩
  have hKiT : K.relIndex T = 2 := by rw [← hCT]; exact hKi
  exact m6e8_rank_le_three hT hKT hKiT hK2
