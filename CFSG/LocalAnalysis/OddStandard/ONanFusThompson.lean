module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.OddStandard.ONanRec

open Equiv Equiv.Perm Subgroup

theorem cycleType_eq_replicate_of_free {X : Type*} [Fintype X] [DecidableEq X] (σ : Perm X)
    {k : ℕ} (hσ : σ ^ 2 ^ k = 1)
    (hfree : ∀ (x : X) (m : ℕ), 0 < m → m < 2 ^ k → (σ ^ m) x ≠ x) :
    σ.cycleType = Multiset.replicate σ.cycleType.card (2 ^ k) := by
  refine Multiset.eq_replicate_card.2 fun m hm => ?_
  have hdvd : m ∣ 2 ^ k := (dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one hσ)
  by_contra hne
  have hlt : m < 2 ^ k := lt_of_le_of_ne (Nat.le_of_dvd (by positivity) hdvd) hne
  obtain ⟨c, τ, hcτ, hd, hc, hcard⟩ := mem_cycleType_iff.1 hm
  have hc' := hc
  obtain ⟨x, hx, -⟩ := hc
  have hτx : τ x = x := (hd x).resolve_left hx
  have hcm : c ^ m = 1 := by
    rw [← hcard, ← hc'.orderOf]
    exact pow_orderOf_eq_one c
  have hσm : (σ ^ m) x = x := by
    rw [hcτ, (hd.commute).mul_pow, Perm.mul_apply, Perm.pow_apply_eq_self_of_apply_eq_self hτx,
      hcm]
    rfl
  exact hfree x m (lt_of_lt_of_le zero_lt_two (one_lt_of_mem_cycleType hm)) hlt hσm

theorem sign_eq_of_free {X : Type*} [Fintype X] [DecidableEq X] (σ : Perm X) {k : ℕ}
    (hk : 1 ≤ k) (hσ : σ ^ 2 ^ k = 1)
    (hfree : ∀ (x : X) (m : ℕ), 0 < m → m < 2 ^ k → (σ ^ m) x ≠ x) :
    sign σ = (-1) ^ (Fintype.card X / 2 ^ k) := by
  have hcyc := cycleType_eq_replicate_of_free σ hσ hfree
  have hfix : Fintype.card (Function.fixedPoints σ) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => hfree x 1 one_pos ?_ ?_⟩
    · calc 1 < 2 := one_lt_two
        _ = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    · rw [pow_one]
      exact hx
  have hev : ¬ Odd (2 ^ k) := by
    rw [Nat.not_odd_iff_even]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  rw [sign_of_cycleType_eq_replicate (by positivity) hcyc]
  simp only [hev, ite_false, hfix, Nat.sub_zero]

theorem exists_pow_eq_involution {G : Type*} [Group G] {r : G} {k : ℕ} (hr : orderOf r = 2 ^ k)
    {m : ℕ} (hm0 : 0 < m) (hmk : m < 2 ^ k) :
    ∃ j : ℕ, (r ^ m) ^ j = r ^ 2 ^ (k - 1) := by
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm0.ne'
  have hak : a < k := by
    have h2 : 2 ^ a ≤ 2 ^ a * u := Nat.le_mul_of_pos_right _ hu.pos
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h2 hmk)
  refine ⟨2 ^ (k - 1 - a), ?_⟩
  have hsq : (r ^ 2 ^ (k - 1)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hr]
    exact pow_orderOf_eq_one r
  have hexp : 2 ^ a * u * 2 ^ (k - 1 - a) = 2 ^ (k - 1) * u := by
    have : 2 ^ (k - 1) = 2 ^ a * 2 ^ (k - 1 - a) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; ring
  rw [← pow_mul, hexp, pow_mul]
  obtain ⟨w, rfl⟩ := hu
  rw [pow_succ, pow_mul, hsq, one_pow, one_mul]

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_index_eq (hG : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    {Q : Subgroup G} {r : G} {k : ℕ} (hk : 1 ≤ k) (hr : orderOf r = 2 ^ k) {m : ℕ}
    (hm : Odd m) (hidx : Q.index = m * 2 ^ k) :
    ∃ g : G, g⁻¹ * r ^ 2 ^ (k - 1) * g ∈ Q := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype (G ⧸ Q) := Fintype.ofFinite _
  let φ0 : G →* Perm (G ⧸ Q) := MulAction.toPermHom G (G ⧸ Q)
  let φ : G →* ℤˣ := (Perm.sign : Perm (G ⧸ Q) →* ℤˣ).comp φ0
  have hσ : (φ0 r) ^ 2 ^ k = 1 := by
    rw [← map_pow, ← hr, pow_orderOf_eq_one, map_one]
  have hfree : ∀ (x : G ⧸ Q) (n : ℕ), 0 < n → n < 2 ^ k → ((φ0 r) ^ n) x ≠ x := by
    intro x n hn0 hnk hfix
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨j, hj⟩ := exists_pow_eq_involution hr hn0 hnk
    have h1 : g⁻¹ * r ^ n * g ∈ Q := by
      have h2 : (φ0 r ^ n) (g : G ⧸ Q) = ((r ^ n * g : G) : G ⧸ Q) := by
        rw [← map_pow]
        rfl
      rw [h2] at hfix
      have h3 := Q.inv_mem (QuotientGroup.eq.1 hfix)
      simpa [mul_assoc] using h3
    apply hcon g
    rw [← hj]
    have h4 : g⁻¹ * (r ^ n) ^ j * g = (g⁻¹ * r ^ n * g) ^ j := by
      have := conj_pow (a := g⁻¹) (b := r ^ n) (i := j)
      simpa using this.symm
    rw [h4]
    exact Q.pow_mem h1 j
  have hsign := sign_eq_of_free (φ0 r) hk hσ hfree
  have hcard : Fintype.card (G ⧸ Q) = m * 2 ^ k := by
    rw [← hidx, Subgroup.index, Nat.card_eq_fintype_card]
  have hφr : φ r = -1 := by
    show Perm.sign (φ0 r) = -1
    rw [hsign, hcard, Nat.mul_div_cancel _ (by positivity), hm.neg_one_pow]
  have hrange : φ.range = ⊤ := by
    refine eq_top_iff.2 fun u _ => ?_
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨r, hφr⟩
  have hker : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  exact hG φ.ker inferInstance hker

theorem exists_conj_mem_of_cyclic_complement (hG : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    {P Q : Subgroup G} (hPidx : ¬ 2 ∣ P.index) {r : G} {k : ℕ} (hk : 1 ≤ k)
    (hr : orderOf r = 2 ^ k) (hcard : Nat.card P = Nat.card Q * 2 ^ k) :
    ∃ g : G, g⁻¹ * r ^ 2 ^ (k - 1) * g ∈ Q := by
  refine exists_conj_mem_of_index_eq hG hk hr (m := P.index) ?_ ?_
  · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hPidx)
  · have h1 := Q.card_mul_index
    have h2 := P.card_mul_index
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have : Nat.card Q * Q.index = Nat.card Q * (P.index * 2 ^ k) := by
      rw [h1, ← h2, hcard]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this

omit [Finite G] in
theorem no_normal_index_two_of_simple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN h2
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.index_bot] at h2
    obtain ⟨a, b, hab⟩ := hnab
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : IsCyclic G := isCyclic_of_prime_card (p := 2) h2
    exact hab (hc.commGroup.mul_comm a b)
  · rw [h, Subgroup.index_top] at h2
    omega

end CFSG.OddStandard.ONanRec
