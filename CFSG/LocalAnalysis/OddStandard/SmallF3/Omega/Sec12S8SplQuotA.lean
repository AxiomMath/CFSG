module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem oddCoreIn_le_X (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

private theorem odd_card_oddCoreIn_X [Finite G] (X : Subgroup G) :
    Odd (Nat.card (oddCoreIn X)) :=
  CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X

theorem s8q_normal (N : Subgroup G) : ((oddCoreIn N).subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_le_X N)]
  exact CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn N

instance s8qNormalInst (N : Subgroup G) : ((oddCoreIn N).subgroupOf N).Normal := s8q_normal N

abbrev S8Quot (N : Subgroup G) : Type := ↥N ⧸ (oddCoreIn N).subgroupOf N

@[expose] def s8qι (V : Subgroup G) : ↥V →* S8Quot (normalizer (V : Set G)) :=
  (QuotientGroup.mk' ((oddCoreIn (normalizer (V : Set G))).subgroupOf
    (normalizer (V : Set G)))).comp (Subgroup.inclusion Subgroup.le_normalizer)

theorem s8q_inf_bot [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8) :
    oddCoreIn (normalizer (V : Set G)) ⊓ V = ⊥ := by
  have hoddO : Odd (Nat.card (oddCoreIn (normalizer (V : Set G)))) :=
    odd_card_oddCoreIn_X _
  have hdvdO : Nat.card ↥(oddCoreIn (normalizer (V : Set G)) ⊓ V) ∣
      Nat.card (oddCoreIn (normalizer (V : Set G))) :=
    Subgroup.card_dvd_of_le inf_le_left
  have hoddI : Odd (Nat.card ↥(oddCoreIn (normalizer (V : Set G)) ⊓ V)) :=
    hoddO.of_dvd_nat hdvdO
  have hdvdV : Nat.card ↥(oddCoreIn (normalizer (V : Set G)) ⊓ V) ∣ Nat.card V :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hV.2] at hdvdV
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 8)).mp hdvdV
  have hk0 : k = 0 := by
    by_contra hkne
    have hev : Even (2 ^ k) := Nat.even_pow.mpr ⟨⟨1, rfl⟩, hkne⟩
    exact (Nat.not_even_iff_odd.mpr (hk ▸ hoddI)) hev
  exact Subgroup.card_eq_one.mp (by rw [hk, hk0]; simp)

theorem s8q_comm [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8) {n v : G}
    (hn : n ∈ oddCoreIn (normalizer (V : Set G))) (hv : v ∈ V) : n * v = v * n := by
  have hnN : n ∈ normalizer (V : Set G) := oddCoreIn_le_X _ hn
  have hvN : v ∈ normalizer (V : Set G) := Subgroup.le_normalizer hv
  have hnv : n * v * n⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hnN v).mp hv
  have hcV : n * v * n⁻¹ * v⁻¹ ∈ V := V.mul_mem hnv (V.inv_mem hv)
  have hconj : v * n⁻¹ * v⁻¹ ∈ oddCoreIn (normalizer (V : Set G)) :=
    CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hvN (inv_mem hn)
  have hcO : n * v * n⁻¹ * v⁻¹ ∈ oddCoreIn (normalizer (V : Set G)) := by
    simpa only [mul_assoc] using
      (oddCoreIn (normalizer (V : Set G))).mul_mem hn hconj
  have hc : n * v * n⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← s8q_inf_bot hV]
    exact ⟨hcO, hcV⟩
  have h2 : n * v * n⁻¹ = v := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hc)
  have h3 : n * v * n⁻¹ * n = v * n := congrArg (· * n) h2
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h3

theorem s8q_le_ker [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8) :
    (oddCoreIn (normalizer (V : Set G))).subgroupOf (normalizer (V : Set G)) ≤
      V.normalizerMonoidHom.ker := by
  rw [Subgroup.normalizerMonoidHom_ker]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (s8q_comm hV hx hv).symm

@[expose] noncomputable def s8qρ [Finite G] {V : Subgroup G} (hV : IsElemAb2 V 8) :
    S8Quot (normalizer (V : Set G)) →* MulAut ↥V :=
  QuotientGroup.lift _ V.normalizerMonoidHom (s8q_le_ker hV)

end CFSG.OddStandard.SmallF3.Omega