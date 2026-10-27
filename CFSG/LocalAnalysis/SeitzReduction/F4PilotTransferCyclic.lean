module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransfer
import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

theorem exists_index_two_of_orderOf_eq_two_pow {Q : Type*} [Group Q] [Finite Q] {z : Q} {a : ℕ}
    (ha : 1 ≤ a) (hz : orderOf z = 2 ^ a) (hQ : ¬ 2 ^ (a + 1) ∣ Nat.card Q) :
    ∃ R : Subgroup Q, R.index = 2 ∧ z ∉ R ∧ ∀ q : Q, q ∉ R → 2 ^ a ∣ orderOf q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hP : IsPGroup 2 (zpowers z) := IsPGroup.of_card (by rw [Nat.card_zpowers, hz])
  have hPidx : ¬ 2 ∣ (zpowers z).index := by
    intro h
    apply hQ
    rw [← (zpowers z).card_mul_index, Nat.card_zpowers, hz, pow_succ _ (b + 1)]
    exact Nat.mul_dvd_mul_left _ h
  set S : Sylow 2 Q := hP.toSylow hPidx with hS
  have hScyc : IsCyclic (S : Subgroup Q) := by
    rw [hS, IsPGroup.toSylow_coe]
    infer_instance
  have hSc : Nat.card S = 2 ^ (b + 1) := by
    change Nat.card (zpowers z) = 2 ^ (b + 1)
    rw [Nat.card_zpowers, hz]
  obtain ⟨-, -, -, ⟨hKn, hKodd, hKidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  set K := pPrimeCore 2 Q with hK
  set π := QuotientGroup.mk' K with hπ
  set w := π z with hwdef
  have hcardQK : Nat.card (Q ⧸ K) = 2 ^ (b + 1) := by
    rw [← index_eq_card, hKidx, hSc]
  have hw : orderOf w = 2 ^ (b + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · intro h1
      rw [hwdef, ← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 : orderOf (z ^ 2 ^ b) = 2 := by
        rw [orderOf_pow_of_dvd (by positivity) (by rw [hz]; exact pow_dvd_pow 2 (Nat.le_succ b)),
          hz, pow_succ, Nat.mul_div_cancel_left 2 (by positivity)]
      have h3 := K.orderOf_dvd_natCard h1
      rw [h2] at h3
      exact (Nat.not_even_iff_odd.2 hKodd) (even_iff_two_dvd.2 h3)
    · rw [hwdef, ← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  have htop : zpowers w = ⊤ := by
    apply eq_top_of_card_eq
    rw [Nat.card_zpowers, hw, hcardQK]
  set R₁ := zpowers (w ^ 2) with hR₁
  have hR₁card : Nat.card R₁ = 2 ^ b := by
    rw [hR₁, Nat.card_zpowers, orderOf_pow_of_dvd two_ne_zero
      (by rw [hw, pow_succ]; exact dvd_mul_left 2 _), hw, pow_succ,
      Nat.mul_div_cancel _ two_pos]
  have hR₁idx : R₁.index = 2 := by
    have h := R₁.card_mul_index
    rw [hR₁card, hcardQK, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  refine ⟨R₁.comap π, ?_, ?_, ?_⟩
  · rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective K)]
    exact hR₁idx
  · intro hzR
    have hwR : w ∈ R₁ := hzR
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hwR)
    rw [← pow_mul] at hk
    have hk1 : w ^ (2 * k) = w ^ 1 := by rw [hk, pow_one]
    have h2 := pow_eq_pow_iff_modEq.1 hk1
    rw [hw] at h2
    have h3 : 2 * k ≡ 1 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 (Nat.succ_ne_zero b)) h2
    unfold Nat.ModEq at h3
    omega
  · intro q hqR
    have hqR₁ : π q ∉ R₁ := hqR
    have hq : π q ∈ zpowers w := htop ▸ mem_top _
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hq)
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hodd
    · exfalso
      apply hqR₁
      rw [← hk, ← two_mul, pow_mul]
      exact pow_mem (mem_zpowers _) j
    · have h1 : w ^ (k * orderOf q) = 1 := by
        rw [pow_mul, hk, ← map_pow, pow_orderOf_eq_one, map_one]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hw] at h2
      exact (Nat.Coprime.pow_left (b + 1) (Nat.coprime_two_left.2 hodd)).dvd_of_dvd_mul_left h2

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_index_two_of_unique_of_quotient {M G₀ : Subgroup G}
    [(G₀.subgroupOf M).Normal] {t : G} (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) {x : G}
    (hxM : x ∈ M) {a : ℕ} (ha : 1 ≤ a) (hxo : orderOf x = 2 ^ a)
    (hxQ : orderOf (QuotientGroup.mk' (G₀.subgroupOf M) ⟨x, hxM⟩) = 2 ^ a)
    (hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ G₀.subgroupOf M)) {n : ℕ} (hpow : IsConj t (x ^ n)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  obtain ⟨R, hRidx, hxR, hR⟩ := exists_index_two_of_orderOf_eq_two_pow ha hxQ hQ
  set Y := (R.comap (QuotientGroup.mk' (G₀.subgroupOf M))).map M.subtype with hY
  have hYM : Y ≤ M := map_subtype_le _
  have hmemY : ∀ y (hy : y ∈ M), y ∈ Y ↔ QuotientGroup.mk' (G₀.subgroupOf M) ⟨y, hy⟩ ∈ R := by
    intro y hy
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro h
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hYidx : Y.relIndex M = 2 := by
    rw [relIndex, hY, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective,
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hRidx]
  refine exists_normal_index_two_of_unique_of_relIndex_eq_two hYM hYidx huniq hxM
    (fun h => hxR ((hmemY x hxM).1 h)) hxo (fun y hy hyY _ => ?_) hpow
  have h1 := hR _ (fun h => hyY ((hmemY y hy).2 h))
  have h2 : orderOf (QuotientGroup.mk' (G₀.subgroupOf M) ⟨y, hy⟩) ∣ orderOf y := by
    rw [← orderOf_mk y hy]
    exact orderOf_map_dvd _ _
  rw [hxo]
  exact Nat.le_of_dvd (orderOf_pos y) (h1.trans h2)

theorem false_of_simple_of_unique_of_quotient [IsSimpleGroup G] (hG : 2 < Nat.card G)
    {M G₀ : Subgroup G} [(G₀.subgroupOf M).Normal] {t : G}
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) {x : G} (hxM : x ∈ M) {a : ℕ} (ha : 1 ≤ a)
    (hxo : orderOf x = 2 ^ a)
    (hxQ : orderOf (QuotientGroup.mk' (G₀.subgroupOf M) ⟨x, hxM⟩) = 2 ^ a)
    (hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ G₀.subgroupOf M)) {n : ℕ} (hpow : IsConj t (x ^ n)) :
    False :=
  CFSG.SeitzReduction.not_exists_normal_index_two_of_simple hG
    (exists_normal_index_two_of_unique_of_quotient huniq hxM ha hxo hxQ hQ hpow)

end CFSG.SeitzReduction.F4Pilot
