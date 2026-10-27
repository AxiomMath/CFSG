module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Skeleton

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

variable {C : Type*} [Group C] {L : Type*} [Group L] {ψ : Fin 3 → L →* C} {g : L} {p : ℕ}

theorem exists_zpow_mul_zpow_of_mem_plane
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) {z : C} (hz : z ∈ plane ψ g) :
    ∃ i j : ℤ, z = ψ 0 g ^ i * ψ 1 g ^ j := by
  have h01 : Commute (ψ 0 g) (ψ 1 g) := hcomm 0 1 (by decide) g g
  unfold plane at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨i', j', rfl⟩ := hy
    refine ⟨i + i', j + j', ?_⟩
    have hc := (h01.symm.zpow_zpow j i').eq
    have hrw : ψ 0 g ^ i * ψ 1 g ^ j * (ψ 0 g ^ i' * ψ 1 g ^ j') =
        ψ 0 g ^ i * (ψ 1 g ^ j * ψ 0 g ^ i') * ψ 1 g ^ j' := by simp only [mul_assoc]
    rw [hrw, hc, zpow_add, zpow_add]
    simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, ((h01.symm.zpow_zpow j i).inv_inv).eq, zpow_neg, zpow_neg]

theorem exists_pow_mul_pow_mem_of_relIndex (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime)
    (hZ : ∀ x : L, x ^ p = 1 → (∀ A, Commute x A) → x = 1) (hg : orderOf g = p)
    {B : Subgroup C} (hB : B ≤ plane ψ g) (hBi : B.relIndex (plane ψ g) = p) :
    ∃ x y : ℕ, x < p ∧ y < p ∧ (x ≠ 0 ∨ y ≠ 0) ∧ ψ 0 (g ^ x) * ψ 1 (g ^ y) ∈ B := by
  have hp0 : 0 < p := hp.pos
  have hB1 : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hcon
    have hcard : Nat.card (plane ψ g) = p := by
      rw [← hBi, hbot, Subgroup.relIndex_bot_left]
    have hfin : Finite (plane ψ g) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    have hord0 : orderOf (ψ 0 g) = p := by rw [orderOf_injective (ψ 0) (hinj 0) g, hg]
    have h0 : ψ 0 g ∈ plane ψ g := Subgroup.subset_closure (by simp)
    have h1 : ψ 1 g ∈ plane ψ g := Subgroup.subset_closure (by simp)
    have hz : Subgroup.zpowers (ψ 0 g) ≤ plane ψ g :=
      (Subgroup.zpowers_le).2 h0
    have hzcard : Nat.card (Subgroup.zpowers (ψ 0 g)) = p := by rw [Nat.card_zpowers, hord0]
    have heq : Subgroup.zpowers (ψ 0 g) = plane ψ g :=
      Subgroup.eq_of_le_of_card_ge hz (by rw [hcard, hzcard])
    have hmem : ψ 1 g ∈ Subgroup.zpowers (ψ 0 g) := by rw [heq]; exact h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcm : ∀ A, Commute (ψ 1 (g ^ (1 : ℤ))) (ψ 1 A) := by
      intro A
      rw [zpow_one, ← hk, ← map_zpow]
      exact hcomm 0 1 (by decide) _ _
    have hdvd := dvd_of_commute_range_of_center hinj hZ hg 1 1 hcm
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdvd)
  obtain ⟨b, hbB, hb1⟩ := hB1
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_of_mem_plane hcomm (hB hbB)
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : (0 : ℤ) < p := by exact_mod_cast hp0
  refine ⟨(i % p).toNat, (j % p).toNat, ?_, ?_, ?_, ?_⟩
  · have := Int.emod_lt_of_pos i hpos
    omega
  · have := Int.emod_lt_of_pos j hpos
    omega
  · by_contra hcon
    push Not at hcon
    apply hb1
    rw [hij, ← map_zpow, ← map_zpow]
    have hi : (i % p).toNat = 0 := hcon.1
    have hj : (j % p).toNat = 0 := hcon.2
    have hi' : i % p = 0 := by
      have := Int.emod_nonneg i hpz
      omega
    have hj' : j % p = 0 := by
      have := Int.emod_nonneg j hpz
      omega
    have e1 : g ^ i = 1 := by
      rw [← zpow_mod_orderOf, hg, hi', zpow_zero]
    have e2 : g ^ j = 1 := by
      rw [← zpow_mod_orderOf, hg, hj', zpow_zero]
    rw [e1, e2]
    simp
  · have key : ∀ n : ℤ, g ^ n = g ^ (n % (p : ℤ)).toNat := by
      intro n
      have hmod := zpow_mod_orderOf g n
      rw [hg] at hmod
      rw [← hmod, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg n hpz)]
    rw [← key i, ← key j, map_zpow, map_zpow, ← hij]
    exact hbB

theorem centralizer_pow_mul_pow_le
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime)
    (hg : orderOf g = p) {x y m : ℕ} (hx : ¬ p ∣ x) (hy : (y : ZMod p) = (x : ZMod p) * (m : ZMod p)) :
    Subgroup.centralizer ({ψ 0 (g ^ x) * ψ 1 (g ^ y)} : Set C) ≤
      Subgroup.centralizer ({ψ 0 g * ψ 1 (g ^ m)} : Set C) := by
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  set u : C := ψ 0 g * ψ 1 (g ^ m) with hu
  have hc : Commute (ψ 0 g) (ψ 1 (g ^ m)) := hcomm 0 1 (by decide) _ _
  have hup : u ^ p = 1 := by
    rw [hu, hc.mul_pow, ← map_pow, hgp, map_one, ← map_pow, ← pow_mul, mul_comm, pow_mul, hgp,
      one_pow, map_one, one_mul]
  have hux : ψ 0 (g ^ x) * ψ 1 (g ^ y) = u ^ x := by
    have hyx : g ^ y = (g ^ m) ^ x := by
      rw [← pow_mul, mul_comm, pow_eq_pow_iff_modEq, hg]
      exact (ZMod.natCast_eq_natCast_iff y (x * m) p).1 (by rw [hy, Nat.cast_mul])
    rw [hu, hc.mul_pow, map_pow, hyx, map_pow]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x * k % p = 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have hx0 : (x : ZMod p) ≠ 0 := fun h => hx ((ZMod.natCast_eq_zero_iff x p).1 h)
    refine ⟨((x : ZMod p)⁻¹).val, ?_⟩
    have h1 : ((x * ((x : ZMod p)⁻¹).val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_inv_cancel₀ hx0, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rwa [Nat.mod_eq_of_lt hp.one_lt] at h1
  have huk : (u ^ x) ^ k = u := by
    rw [← pow_mul, ← Nat.div_add_mod (x * k) p, hk, pow_add, pow_mul, hup, one_pow, one_mul,
      pow_one]
  intro z hz
  rw [hux] at hz
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have := (Commute.pow_right (show Commute z (u ^ x) from (hz _ rfl).symm) k).eq
  rw [huk] at this
  exact this.symm

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
