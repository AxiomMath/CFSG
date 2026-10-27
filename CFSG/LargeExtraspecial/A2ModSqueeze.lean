module

public import CFSG.LargeExtraspecial.A2ModBasic

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.RankThree.OrthogonalInvolutions

section Coprime

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem dvd_card_pow_finrank_commSpace_sub_one [Finite K] [FiniteDimensional K V] {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) {g : V ≃ₗ[K] V} (hg : g ^ p = 1) :
    p ∣ Nat.card K ^ finrank K (commSpace g) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have hP : IsPGroup p (Subgroup.zpowers g) := by
    rintro ⟨x, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change ((fun n : ℤ => g ^ n) k) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hfix : MulAction.fixedPoints (Subgroup.zpowers g) V = (fixSpace g : Set V) := by
    ext v
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixSpace]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · rintro h ⟨x, hx⟩
      have hg' : g ∈ MulAction.stabilizer (V ≃ₗ[K] V) v := by
        rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
        exact h
      exact Subgroup.zpowers_le.mpr hg' hx
  have hcong := hP.card_modEq_card_fixedPoints V
  rw [hfix] at hcong
  change Nat.card V ≡ Nat.card (fixSpace g) [MOD p] at hcong
  rw [Module.natCard_eq_pow_finrank (K := K) (V := V),
    Module.natCard_eq_pow_finrank (K := K) (V := fixSpace g),
    ← finrank_commSpace_add_finrank_fixSpace g] at hcong
  set q := Nat.card K
  set w := finrank K (commSpace g)
  set f := finrank K (fixSpace g)
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hle : q ^ f ≤ q ^ (w + f) := Nat.pow_le_pow_right hq (Nat.le_add_left f w)
  have hdvd := (Nat.modEq_iff_dvd' hle).mp hcong.symm
  rw [pow_add, mul_comm, ← Nat.mul_sub_one] at hdvd
  have hcop : Nat.Coprime p (q ^ f) :=
    Nat.Coprime.pow_right f ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK)
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem dvd_two_pow_finrank_commSpace_sub_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ^ p = 1) : p ∣ 2 ^ finrank (ZMod 2) (commSpace g) - 1 := by
  have h := dvd_card_pow_finrank_commSpace_sub_one hp (K := ZMod 2) ?_ hg
  · rwa [Nat.card_zmod] at h
  · rw [Nat.card_zmod]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem orderOf_two_le_finrank_commSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    orderOf (2 : ZMod p) ≤ finrank (ZMod 2) (commSpace g) := by
  have h := dvd_two_pow_finrank_commSpace_sub_one hp.out hp2 hg
  have h1 := one_le_finrank_commSpace hg1
  have hpow : (2 : ZMod p) ^ finrank (ZMod 2) (commSpace g) = 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at h
    exact h
  exact Nat.le_of_dvd h1 (orderOf_dvd_of_pow_eq_one hpow)

theorem eq_one_of_pow_prime_of_finrank_commSpace_le {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ^ p = 1) {m : ℕ} (hm : finrank (ZMod 2) (commSpace g) ≤ m)
    (hpj : ∀ j, 1 ≤ j → j ≤ m → ¬ p ∣ 2 ^ j - 1) : g = 1 := by
  by_contra hg1
  exact hpj _ (one_le_finrank_commSpace hg1) hm (dvd_two_pow_finrank_commSpace_sub_one hp hp2 hg)

end Coprime

section Squeeze

variable {X : Type*} [Group X] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem squeeze (ρ : X →* (V ≃ₗ[ZMod 2] V)) (S : Finset X) {g : X}
    (hg : g ∈ Subgroup.closure (S : Set X)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hgp : g ^ p = 1)
    (hpj : ∀ j, 1 ≤ j → j ≤ ∑ s ∈ S, finrank (ZMod 2) (commSpace (ρ s)) → ¬ p ∣ 2 ^ j - 1) :
    ρ g = 1 :=
  eq_one_of_pow_prime_of_finrank_commSpace_le hp hp2 (by rw [← map_pow, hgp, map_one])
    ((Submodule.finrank_mono (commSpace_le_commSpaceOf ρ hg)).trans
      (finrank_commSpaceOf_closure_le ρ S)) hpj

end Squeeze

end CFSG.LargeExtraspecial.A2Mod
