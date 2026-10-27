module

public import CFSG.Goldschmidt.Steps.GoldTypeBender
public import CFSG.Goldschmidt75.Sec41a

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

theorem eq_of_sq_eq_one_of_isCyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z] {a b : Z}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite Z
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := Z) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset Z) ⊆ Finset.univ.filter (fun x : Z => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have hcard : ({1, a, b} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp [Ne.symm ha1, Ne.symm hb1]
  have := Finset.card_le_card hsub
  omega

theorem quaternion_eq_a_of_orderOf_eq_two (m : ℕ) [NeZero m] {q : QuaternionGroup m}
    (hq : orderOf q = 2) : q = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have hm_pos : 0 < m := NeZero.pos m
  have hm_lt : m < 2 * m := by omega
  cases q with
  | xa i =>
      rw [QuaternionGroup.orderOf_xa] at hq
      omega
  | a i =>
      have horder := hq
      rw [QuaternionGroup.orderOf_a] at horder
      have hdiv_mul := Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * m) i.val)
      rw [horder] at hdiv_mul
      have hgcd : Nat.gcd (2 * m) i.val = m := by omega
      obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (2 * m) i.val
      rw [hgcd] at hk
      have hi_lt : i.val < 2 * m := ZMod.val_lt i
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi0
        have h1 : (QuaternionGroup.a i : QuaternionGroup m) = 1 := by
          rw [QuaternionGroup.one_def]
          congr 1
          exact (ZMod.val_eq_zero i).mp hi0
        rw [h1, orderOf_one] at hq
        omega
      have hk1 : k = 1 := by
        rcases Nat.lt_or_ge k 2 with h | h
        · rcases k with _ | k
          · simp [hk] at hi_ne_zero
          · omega
        · nlinarith
      congr 1
      apply ZMod.val_injective
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt, hk, hk1, mul_one]

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_of_sq_eq_one_of_odd_index {N : Subgroup X} [N.Normal] (hN : Odd N.index) {s : X}
    (hs : s ^ 2 = 1) : s ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N s) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hs, map_one]
  have h2 : orderOf (QuotientGroup.mk' N s) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' N s) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hN)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff s).mp h3

theorem commute_of_stronglyEmbedded {M : Subgroup X}
    (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) (P : Sylow 2 X) {s t : X}
    (hs : s ∈ (P : Subgroup X)) (ht : t ∈ (P : Subgroup X)) (hs2 : s ^ 2 = 1) (ht2 : t ^ 2 = 1) :
    s * t = t * s := by
  have hM' : fusionStronglyEmbedded M :=
    ⟨hM.1, hM.2.1, fun g hg => hM.2.2 g⁻¹ fun h => hg (by simpa using M.inv_mem h)⟩
  by_cases hs1 : s = 1
  · rw [hs1, one_mul, mul_one]
  by_cases ht1 : t = 1
  · rw [ht1, one_mul, mul_one]
  rcases CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_3 X M
      hM' with hcyc | ⟨K, N, hK, hN, hKNn, hKN, hKodd, hNodd, hB⟩
  · have hst : (⟨s, hs⟩ : (P : Subgroup X)) = ⟨t, ht⟩ := by
      rcases hcyc P with hc | ⟨r, hr, ⟨e⟩⟩
      · exact eq_of_sq_eq_one_of_isCyclic (Subtype.ext hs2) (Subtype.ext ht2)
          (fun h => hs1 (congrArg Subtype.val h)) (fun h => ht1 (congrArg Subtype.val h))
      · have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
        have key : ∀ x : (P : Subgroup X), x ^ 2 = 1 → x ≠ 1 →
            e x = QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) := by
          intro x hx hx1
          apply quaternion_eq_a_of_orderOf_eq_two
          rw [MulEquiv.orderOf_eq]
          exact orderOf_eq_prime hx hx1
        exact e.injective ((key _ (Subtype.ext hs2) fun h => hs1 (congrArg Subtype.val h)).trans
          (key _ (Subtype.ext ht2) fun h => ht1 (congrArg Subtype.val h)).symm)
    rw [show s = t from congrArg Subtype.val hst]
  · have hsN : s ∈ N := mem_of_sq_eq_one_of_odd_index hNodd hs2
    have htN : t ∈ N := mem_of_sq_eq_one_of_odd_index hNodd ht2
    set π := QuotientGroup.mk' (K.subgroupOf N)
    have hPN : IsPGroup 2 ((P.subgroupOf N).map π) := (P.isPGroup'.comap_subtype).map π
    obtain ⟨PQ, hPQ⟩ := hPN.exists_le_sylow
    have hsQ : π ⟨s, hsN⟩ ∈ (PQ : Subgroup (N ⧸ K.subgroupOf N)) :=
      hPQ ⟨⟨s, hsN⟩, mem_subgroupOf.mpr hs, rfl⟩
    have htQ : π ⟨t, htN⟩ ∈ (PQ : Subgroup (N ⧸ K.subgroupOf N)) :=
      hPQ ⟨⟨t, htN⟩, mem_subgroupOf.mpr ht, rfl⟩
    have hsZ : π ⟨s, hsN⟩ ∈ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
        (PQ : Subgroup (N ⧸ K.subgroupOf N)) := by
      rw [← CFSG.Goldschmidt.GoldType.omega1_eq_sylowCenter_of_bender hB PQ]
      exact CFSG.Goldschmidt.GoldType.mem_omega1 hsQ (by rw [← map_pow]; rw [show
        (⟨s, hsN⟩ : N) ^ 2 = 1 from Subtype.ext hs2, map_one])
    have hcomm := (CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter.mp
      hsZ).2 _ htQ
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hcomm
    set c : N := ((⟨t, htN⟩ : N) * ⟨s, hsN⟩)⁻¹ * ((⟨s, hsN⟩ : N) * ⟨t, htN⟩) with hc
    have hmem : (c : X) ∈ K := hcomm
    have hcX : (c : X) = (t * s)⁻¹ * (s * t) := rfl
    have hmemP : (c : X) ∈ (P : Subgroup X) := by
      rw [hcX]
      exact mul_mem (inv_mem (mul_mem ht hs)) (mul_mem hs ht)
    have h1 := eq_one_of_mem_odd_of_mem_sylow P hKodd hmem hmemP
    rw [hcX] at h1
    exact (inv_mul_eq_one.mp h1).symm

end CFSG.Goldschmidt75
