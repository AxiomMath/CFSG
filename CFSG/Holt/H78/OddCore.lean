module

public import CFSG.Holt.H78.Count
import CFSG.Holt.H78.Prelim
import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Reflections

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

private theorem mul_pow_add_two_eq {t u : G} (ht : t * t = 1) (hu : u⁻¹ = u) (i : ℕ) :
    t * (t * u) ^ (i + 2) = (t * u)⁻¹ * (t * (t * u) ^ i) * (t * u)⁻¹⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc t * (t * u) ^ (i + 2) = t * t * u * ((t * u) ^ i * (t * u)) := by
        rw [show i + 2 = i + 1 + 1 from rfl, pow_succ', pow_succ]
        simp only [mul_assoc]
    _ = u * ((t * u) ^ i * (t * u)) := by rw [ht, one_mul]
    _ = u * t * (t * (t * u) ^ i) * (t * u) := by
        rw [mul_assoc u t, ← mul_assoc t t, ht, one_mul, mul_assoc]
    _ = (t * u)⁻¹ * (t * (t * u) ^ i) * (t * u)⁻¹⁻¹ := by rw [inv_inv, mul_inv_rev, hu, ht']

theorem mul_pow_mul_mem_longInv {t u : G} (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) :
    ∀ i : ℕ, t * (t * u) ^ i ∈ longInv G Ω
  | 0 => by rwa [pow_zero, mul_one]
  | 1 => by rwa [pow_one, ← mul_assoc, mul_self_eq_one_of_mem_longInv ht, one_mul]
  | i + 2 => by
    rw [mul_pow_add_two_eq (mul_self_eq_one_of_mem_longInv ht) (inv_eq_self_of_mem_longInv hu)]
    exact conj_mem_longInv (mul_pow_mul_mem_longInv ht hu i) _

private theorem mem_of_sq_mem_of_odd_orderOf {x : G} {K : Subgroup G} (hx : Odd (orderOf x))
    (h : x ^ 2 ∈ K) : x ∈ K := by
  obtain ⟨m, hm⟩ := hx
  have e : (x ^ 2) ^ (m + 1) = x := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  exact e ▸ K.pow_mem h _

theorem eq_of_commute_mul
    (hodd : ∀ a ∈ longInv G Ω, ∀ b ∈ longInv G Ω, Odd (orderOf (a * b))) {t a b : G}
    (ht : t ∈ longInv G Ω) (ha : a ∈ longInv G Ω) (hb : b ∈ longInv G Ω)
    (h : Commute t (a * b)) : a = b := by
  have ha2 := mul_self_eq_one_of_mem_longInv ha
  have hb2 := mul_self_eq_one_of_mem_longInv hb
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by simpa using conj_pow_mul_eq_inv ha2 hb2 1
  have hinv : (t * a) * (a * b) * (t * a)⁻¹ = (a * b)⁻¹ := by
    calc (t * a) * (a * b) * (t * a)⁻¹ = t * (a * (a * b) * a⁻¹) * t⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [h1, h.inv_right.eq, mul_inv_cancel_right]
  have e1 : SemiconjBy (t * a) (a * b) (a * b)⁻¹ := by
    show (t * a) * (a * b) = (a * b)⁻¹ * (t * a)
    rw [← hinv, inv_mul_cancel_right]
  have e2 : SemiconjBy (t * a) (a * b)⁻¹ (a * b) := by simpa using e1.inv_right
  have hsq : Commute ((t * a) ^ 2) (a * b) := by
    rw [sq]
    exact e2.mul_left e1
  obtain ⟨m, hm⟩ := hodd t ht a ha
  have e : ((t * a) ^ 2) ^ (m + 1) = t * a := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf (t * a) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hc : Commute (t * a) (a * b) := e ▸ hsq.pow_left (m + 1)
  have hx : (a * b)⁻¹ = a * b := mul_right_cancel (e1.eq.symm.trans hc.eq)
  have hdvd : orderOf (a * b) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [sq]; nth_rewrite 2 [← hx]; exact mul_inv_cancel _)
  have h1' : orderOf (a * b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact h'
    · have := hodd a ha b hb
      rw [h'] at this
      exact absurd this (by decide)
  rw [eq_inv_of_mul_eq_one_left (orderOf_eq_one_iff.mp h1'), inv_eq_self_of_mem_longInv hb]

variable [Finite G]

theorem odd_orderOf_mul_of_eq_of_commute
    (hJ : ∀ a ∈ longInv G Ω, ∀ b ∈ longInv G Ω, Commute a b → a = b) {t u : G}
    (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : Odd (orderOf (t * u)) := by
  have ht2 := mul_self_eq_one_of_mem_longInv ht
  have hu2 := mul_self_eq_one_of_mem_longInv hu
  rw [← Nat.not_even_iff_odd]
  rintro ⟨k, hk⟩
  have hpos : 0 < orderOf (t * u) := orderOf_pos _
  have hz : (t * u) ^ k ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hzinv : ((t * u) ^ k)⁻¹ = (t * u) ^ k :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, ← hk, pow_orderOf_eq_one])
  have hcomm : Commute t (t * (t * u) ^ k) := by
    have h := conj_pow_mul_eq_inv ht2 hu2 k
    rw [hzinv, inv_eq_self_of_mem_longInv ht] at h
    show t * (t * (t * u) ^ k) = t * (t * u) ^ k * t
    rw [h, ← mul_assoc, ht2, one_mul]
  exact hz (mul_eq_left.mp (hJ t ht _ (mul_pow_mul_mem_longInv ht hu k) hcomm).symm)

end Reflections

section Lemma23i

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem isPretransitive_of_isPretransitive_subgroup {K : Subgroup G} (hK : IsPretransitive K Ω) :
    IsPretransitive G Ω :=
  ⟨fun α β => let ⟨k, hk⟩ := hK.exists_smul_eq α β; ⟨k, hk⟩⟩

theorem longInvAt_nonempty_of_mem_longInv [IsPretransitive G Ω] {t : G} (ht : t ∈ longInv G Ω)
    (α : Ω) : (longInvAt G Ω α).Nonempty := by
  obtain ⟨β, hβ⟩ := exists_mem_longInvAt ht
  obtain ⟨g, rfl⟩ := exists_smul_eq G β α
  exact ⟨_, conj_mem_longInvAt hβ g⟩

variable [Finite G] [Finite Ω] [FaithfulSMul G Ω]

theorem eq_of_mem_longInv_of_commute (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t u : G}
    (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) (htu : Commute t u) : t = u :=
  haveI := hO
  eq_of_commute_of_existsUnique_fixed ht.1 hu.1 htu ht.2 hu.2

theorem odd_orderOf_mul_of_isPretransitive (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    {t u : G} (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : Odd (orderOf (t * u)) :=
  odd_orderOf_mul_of_eq_of_commute (fun _ ha _ hb => eq_of_mem_longInv_of_commute hO ha hb) ht hu

end Lemma23i

section Lemma23iZStar

variable {G : Type} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem mul_mem_pPrimeCore_of_isPretransitive (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    {t u : G} (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : t * u ∈ CFSG.pPrimeCore 2 G := by
  have : Fintype G := Fintype.ofFinite G
  have ht1 : t ≠ 1 := fun h => by
    have h2 := ht.1
    rw [h, orderOf_one] at h2
    omega
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G t ht1
    (mul_self_eq_one_of_mem_longInv ht) fun g hg =>
      eq_of_mem_longInv_of_commute hO (conj_mem_longInv ht g) ht hg
  have hNO : N ≤ CFSG.pPrimeCore 2 G := le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
  have hsq : (u * t) ^ 2 ∈ N := by
    have e : (u * t) ^ 2 = u * t * u⁻¹ * t⁻¹ := by
      rw [inv_eq_self_of_mem_longInv hu, inv_eq_self_of_mem_longInv ht, sq, ← mul_assoc]
    rw [e]
    exact hN u
  have hut := hNO (mem_of_sq_mem_of_odd_orderOf (odd_orderOf_mul_of_isPretransitive hO hu ht) hsq)
  have e : t * u = (u * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_self_of_mem_longInv hu, inv_eq_self_of_mem_longInv ht]
  rw [e]
  exact inv_mem hut

theorem mul_mem_jOddCore_of_isPretransitive (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    {t u : G} (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : t * u ∈ jOddCore G Ω := by
  rw [jOddCore_eq_jHull_inf_pPrimeCore]
  exact ⟨mul_mem (mem_jHull_of_mem_longInv ht) (mem_jHull_of_mem_longInv hu),
    mul_mem_pPrimeCore_of_isPretransitive hO ht hu⟩

theorem lemma_2_3_i (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t : G}
    (ht : t ∈ longInv G Ω) :
    IsPretransitive (jOddCore G Ω) Ω ∧ jHull G Ω = jOddCore G Ω ⊔ Subgroup.zpowers t := by
  have := isPretransitive_of_isPretransitive_subgroup hO
  refine ⟨⟨fun α β => ?_⟩, le_antisymm ?_ ?_⟩
  · obtain ⟨a, ha⟩ := longInvAt_nonempty_of_mem_longInv ht α
    obtain ⟨b, hb⟩ := longInvAt_nonempty_of_mem_longInv ht β
    exact ⟨⟨_, Subgroup.pow_mem _ (mul_mem_jOddCore_of_isPretransitive hO ha.1 hb.1) _⟩,
      pow_period_div_two_mul_smul_eq ha hb⟩
  · refine jHull_le_iff.mpr fun u hu => ?_
    have e : u = t * (t * u) := by rw [← mul_assoc, mul_self_eq_one_of_mem_longInv ht, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_left (mul_mem_jOddCore_of_isPretransitive hO ht hu))
  · exact sup_le jOddCore_le_jHull (Subgroup.zpowers_le.mpr (mem_jHull_of_mem_longInv ht))

theorem mul_mem_jOddCore_inf_of_mem_longInvSwap (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    {s u : G} {α β : Ω} (hs : s ∈ longInvSwap G Ω α β) (hu : u ∈ longInvSwap G Ω α β) :
    s * u ∈ jOddCore G Ω ⊓ (stabilizer G α ⊓ stabilizer G β) :=
  ⟨mul_mem_jOddCore_of_isPretransitive hO hs.1 hu.1,
    mul_mem_stabilizer_inf_of_mem_longInvSwap hs hu⟩

theorem eq_of_conj_mul_eq (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t u s s' : G}
    (ht : t ∈ longInv G Ω) (hs : s ∈ longInv G Ω) (hs' : s' ∈ longInv G Ω)
    (h : (s * u) * t * (s * u)⁻¹ = (s' * u) * t * (s' * u)⁻¹) :
    s = s' := by
  have hc : Commute (u * t * u⁻¹) (s' * s) := by
    show u * t * u⁻¹ * (s' * s) = s' * s * (u * t * u⁻¹)
    have e1 : s' * s * (u * t * u⁻¹) = s' * ((s * u) * t * (s * u)⁻¹) * s := by group
    have e2 : s' * ((s' * u) * t * (s' * u)⁻¹) * s =
        (s' * s') * (u * t * u⁻¹) * (s'⁻¹ * s) := by group
    rw [e1, h, e2, mul_self_eq_one_of_mem_longInv hs', one_mul, inv_eq_self_of_mem_longInv hs']
  exact (eq_of_commute_mul (fun _ ha _ hb => odd_orderOf_mul_of_isPretransitive hO ha hb)
    (conj_mem_longInv ht u) hs' hs hc).symm

private def conjSwap {t u : G} {α β : Ω} (ht : t ∈ longInvAt G Ω α)
    (hu : u ∈ longInvSwap G Ω α β) (s : longInvSwap G Ω α β) : longInvAt G Ω α :=
  ⟨((s : G) * u) * t * ((s : G) * u)⁻¹, by
    have h := conj_mem_longInvAt ht ((s : G) * u)
    rwa [mem_stabilizer_iff.mp (mul_mem_stabilizer_inf_of_mem_longInvSwap s.2 hu).1] at h⟩

private theorem conjSwap_injective (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t u : G}
    {α β : Ω} (ht : t ∈ longInvAt G Ω α) (hu : u ∈ longInvSwap G Ω α β) :
    Function.Injective (conjSwap ht hu) := fun s s' h =>
  Subtype.ext (eq_of_conj_mul_eq hO ht.1 s.2.1 s'.2.1 (congrArg Subtype.val h))

theorem card_longInvSwap_le_of_isPretransitive (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (α β : Ω) : Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) := by
  have := isPretransitive_of_isPretransitive_subgroup hO
  rcases (longInvSwap G Ω α β).eq_empty_or_nonempty with h | ⟨u, hu⟩
  · simp [h]
  obtain ⟨t, ht⟩ := longInvAt_nonempty_of_mem_longInv hu.1 α
  exact Nat.card_le_card_of_injective _ (conjSwap_injective hO ht hu)

theorem card_longInvSwap_eq_of_isPretransitive (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (α β : Ω) : Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) := by
  classical
  have := isPretransitive_of_isPretransitive_subgroup hO
  have := Fintype.ofFinite Ω
  by_cases hβα : β = α
  · rw [hβα, longInvSwap_self]
  have hle : ∀ β' ∈ Finset.univ.erase α,
      Nat.card (longInvSwap G Ω α β') ≤ Nat.card (longInvAt G Ω α) :=
    fun β' _ => card_longInvSwap_le_of_isPretransitive hO α β'
  have hconst : ∑ _β' ∈ Finset.univ.erase α, Nat.card (longInvAt G Ω α) =
      Nat.card (longInvAt G Ω α) * (Fintype.card Ω - 1) := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ,
      smul_eq_mul, mul_comm]
  exact (Finset.sum_eq_sum_iff_of_le hle).mp
    ((sum_card_longInvSwap_of_isPretransitive α).trans hconst.symm) β
    (Finset.mem_erase.mpr ⟨hβα, Finset.mem_univ β⟩)

theorem exists_mem_jOddCore_conj_eq (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t s : G}
    {α : Ω} (ht : t ∈ longInvAt G Ω α) (hs : s ∈ longInvAt G Ω α) (β : Ω) :
    ∃ g ∈ jOddCore G Ω ⊓ (stabilizer G α ⊓ stabilizer G β), g * t * g⁻¹ = s := by
  have hcard := card_longInvSwap_eq_of_isPretransitive hO α β
  have : Nonempty (longInvAt G Ω α) := ⟨⟨t, ht⟩⟩
  have hpos : 0 < Nat.card (longInvSwap G Ω α β) := hcard ▸ Nat.card_pos
  obtain ⟨⟨u, hu⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨⟨s', hs'⟩, hfs⟩ :=
    ((conjSwap_injective hO ht hu).bijective_of_nat_card_le hcard.ge).2 ⟨s, hs⟩
  exact ⟨s' * u, mul_mem_jOddCore_inf_of_mem_longInvSwap hO hs' hu, congrArg Subtype.val hfs⟩

theorem holtDelta'_eq_orbit_of_le (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {α β γ : Ω}
    (hγ : γ ∈ holtDelta' G Ω α β) {K : Subgroup G}
    (hK₁ : jOddCore G Ω ⊓ (stabilizer G α ⊓ stabilizer G β) ≤ K)
    (hK₂ : K ≤ stabilizer G α ⊓ stabilizer G β) : holtDelta' G Ω α β = orbit K γ := by
  obtain ⟨s, hs, rfl⟩ := hγ
  ext δ
  constructor
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨g, hg, rfl⟩ := exists_mem_jOddCore_conj_eq hO hs hs' β
    have hgβ : g⁻¹ • β = β := inv_smul_eq_iff.mpr (mem_stabilizer_iff.mp hg.2.2).symm
    refine ⟨⟨g, hK₁ hg⟩, ?_⟩
    show g • s • β = (g * s * g⁻¹) • β
    rw [mul_smul, mul_smul, hgβ]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hmem : s • β ∈ holtDelta' G Ω α β := ⟨s, hs, rfl⟩
    have h : k • s • β ∈ k • holtDelta' G Ω α β := Set.smul_mem_smul_set hmem
    rwa [mem_stabilizer_iff.mp (stabilizer_inf_le_stabilizer_holtDelta' α β (hK₂ hk))] at h

theorem holtDelta'_eq_orbit_of_isPretransitive (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    {α β γ : Ω} (hγ : γ ∈ holtDelta' G Ω α β) :
    holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ :=
  holtDelta'_eq_orbit_of_le hO hγ inf_le_right le_rfl

theorem holtDelta'_eq_orbit_jHull_of_isPretransitive
    (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {α β γ : Ω} (hγ : γ ∈ holtDelta' G Ω α β) :
    holtDelta' G Ω α β = orbit ↥(jHull G Ω ⊓ (stabilizer G α ⊓ stabilizer G β)) γ :=
  holtDelta'_eq_orbit_of_le hO hγ (inf_le_inf_right _ jOddCore_le_jHull) inf_le_right

theorem lemma_2_3_ii (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (α β : Ω) :
    Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) ∧
      (∀ t ∈ longInvAt G Ω α, ∀ s ∈ longInvAt G Ω α,
        ∃ g ∈ jHull G Ω ⊓ (stabilizer G α ⊓ stabilizer G β), g * t * g⁻¹ = s) ∧
      ∀ γ ∈ holtDelta' G Ω α β,
        holtDelta' G Ω α β = orbit ↥(jHull G Ω ⊓ (stabilizer G α ⊓ stabilizer G β)) γ ∧
          holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ := by
  refine ⟨card_longInvSwap_eq_of_isPretransitive hO α β, fun t ht s hs => ?_, fun γ hγ =>
    ⟨holtDelta'_eq_orbit_jHull_of_isPretransitive hO hγ,
      holtDelta'_eq_orbit_of_isPretransitive hO hγ⟩⟩
  obtain ⟨g, hg, rfl⟩ := exists_mem_jOddCore_conj_eq hO ht hs β
  exact ⟨g, inf_le_inf_right _ jOddCore_le_jHull hg, rfl⟩

end Lemma23iZStar

section Lemma24i

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem orbit_jOddCore_eq_of_forall_nonempty (hJ : ∀ β : Ω, (longInvAt G Ω β).Nonempty)
    (ω : Ω) : orbit ↥(jOddCore G Ω) ω = orbit ↥(CFSG.pPrimeCore 2 G) ω := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨g, jOddCore_le_pPrimeCore hg⟩, rfl⟩
  · rintro _ ⟨⟨n, hn⟩, rfl⟩
    have hn' : n ∈ CFSG.pPrimeCore 2 G := hn
    obtain ⟨t, ht⟩ := hJ ω
    have ht' := conj_mem_longInvAt ht n
    have hmem : t * (n * t * n⁻¹) ∈ jOddCore G Ω := by
      rw [jOddCore_eq_jHull_inf_pPrimeCore]
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem (mem_jHull_of_mem_longInv ht.1) (mem_jHull_of_mem_longInv ht'.1), ?_⟩
      have e : t * (n * t * n⁻¹) = t * n * t⁻¹ * n⁻¹ := by
        rw [inv_eq_self_of_mem_longInv ht.1]
        group
      rw [e]
      exact mul_mem ((CFSG.pPrimeCore_normal (p := 2) (G := G)).conj_mem n hn' t) (inv_mem hn')
    exact ⟨⟨_, Subgroup.pow_mem _ hmem _⟩, pow_period_div_two_mul_smul_eq ht ht'⟩

theorem orbit_jOddCore_eq (hG : IsStarGroup G Ω) (ω : Ω) :
    orbit ↥(jOddCore G Ω) ω = orbit ↥(CFSG.pPrimeCore 2 G) ω :=
  orbit_jOddCore_eq_of_forall_nonempty hG.longInvAt_nonempty ω

theorem IsStarGroup.isPretransitive_jOddCore_iff (hG : IsStarGroup G Ω) :
    IsPretransitive (jOddCore G Ω) Ω ↔ IsPretransitive (CFSG.pPrimeCore 2 G) Ω := by
  constructor <;> intro h <;> refine ⟨fun α β => ?_⟩
  · have hβ : β ∈ orbit ↥(jOddCore G Ω) α := h.exists_smul_eq α β
    rw [orbit_jOddCore_eq hG] at hβ
    exact mem_orbit_iff.mp hβ
  · have hβ : β ∈ orbit ↥(CFSG.pPrimeCore 2 G) α := h.exists_smul_eq α β
    rw [← orbit_jOddCore_eq hG] at hβ
    exact mem_orbit_iff.mp hβ

end Lemma24i

section Data

variable {G : Type} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

@[expose] def HoltData.ofIsPretransitiveOddCore (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    {t : G} (ht : t ∈ longInv G Ω) : HoltData G Ω :=
  .ofIsPretransitive ht (lemma_2_3_i hO ht).1 (lemma_2_3_i hO ht).2

theorem holtStructure_of_isPretransitive_oddCore (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (hJ : (longInv G Ω).Nonempty) : HoltStructure G Ω :=
  let ⟨_, ht⟩ := hJ
  ⟨.ofIsPretransitiveOddCore hO ht⟩

theorem IsStarGroup.holtStructure_of_isPretransitive_pPrimeCore (hG : IsStarGroup G Ω)
    (hO : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) : HoltStructure G Ω :=
  holtStructure_of_isPretransitive_oddCore hO hG.longInv_nonempty

end Data

end CFSG.Holt.H78
