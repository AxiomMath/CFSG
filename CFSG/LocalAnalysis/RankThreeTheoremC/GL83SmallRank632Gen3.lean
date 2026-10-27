module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers

private def zmodThreeProdHom {Γ : Type*} [Group Γ] {x z : Γ} (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxz : x * z = z * x) : Multiplicative (ZMod 3 × ZMod 3) →* Γ where
  toFun p := x ^ (Multiplicative.toAdd p).1.val * z ^ (Multiplicative.toAdd p).2.val
  map_one' := by simp
  map_mul' p q := by
    have hc : Commute (x ^ (Multiplicative.toAdd q).1.val) (z ^ (Multiplicative.toAdd p).2.val) :=
      (Commute.pow_pow (show Commute x z from hxz) _ _)
    rw [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ hx,
      ← pow_eq_pow_mod _ hz, pow_add, pow_add]
    exact hc.mul_mul_mul_comm _ _

private theorem card_sup_le_mul {V : Type*} [CommGroup V] [Finite V] (H K : Subgroup V) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  let f : H × K → ↥(H ⊔ K) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨h, hh, k, hk, rfl⟩ := Subgroup.mem_sup.1 hv
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_surjective f hf

private theorem card_le_mul_fixedSubgroups_aux {Γ V : Type*} [Group Γ] [CommGroup V] [Finite V]
    (hV3 : ¬ 3 ∣ Nat.card V) (ρ : Γ →* MulAut V) {x z : Γ}
    (hx : x ^ 3 = 1) (hz : z ^ 3 = 1) (hxz : x * z = z * x)
    (hfree : ∀ v : V, ρ z v = v → v = 1) :
    Nat.card V ≤ Nat.card (fixedSubgroup ρ x) * Nat.card (fixedSubgroup ρ (x * z)) *
      Nat.card (fixedSubgroup ρ (x * z ^ 2)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card V) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hV3
  have htop : (fixedSubgroup ρ x ⊔ fixedSubgroup ρ (x * z) ⊔ fixedSubgroup ρ (x * z ^ 2)) = ⊤ := by
    refine finite_prime_coprime_fixed_lines_generate 3 Nat.prime_three
      (ρ.comp (zmodThreeProdHom hx hz hxz)) _ hcop ?_
    rintro ⟨a, b⟩ hne v hv
    have hfix : ∀ c : ZMod 3, ρ (x ^ (c * a).val * z ^ (c * b).val) v = v := fun c => hv c
    have hone : (1 : ZMod 3).val = 1 := rfl
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb => hne (by rw [ha, hb]; rfl)
      have h1 := hfix b⁻¹
      rw [ha, mul_zero, inv_mul_cancel₀ hb, ZMod.val_zero, hone, pow_zero, pow_one,
        one_mul] at h1
      rw [hfree v h1]
      exact one_mem _
    · have h1 := hfix a⁻¹
      rw [inv_mul_cancel₀ ha, hone, pow_one] at h1
      have hlt : (a⁻¹ * b).val < 3 := ZMod.val_lt _
      rcases (by omega : (a⁻¹ * b).val = 0 ∨ (a⁻¹ * b).val = 1 ∨ (a⁻¹ * b).val = 2) with h | h | h
      · rw [h, pow_zero, mul_one] at h1
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left h1)
      · rw [h, pow_one] at h1
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h1)
      · rw [h] at h1
        exact Subgroup.mem_sup_right h1
  calc Nat.card V = Nat.card ↥(fixedSubgroup ρ x ⊔ fixedSubgroup ρ (x * z) ⊔
        fixedSubgroup ρ (x * z ^ 2)) := by rw [htop, Subgroup.card_top]
    _ ≤ Nat.card ↥(fixedSubgroup ρ x ⊔ fixedSubgroup ρ (x * z)) *
        Nat.card (fixedSubgroup ρ (x * z ^ 2)) := card_sup_le_mul _ _
    _ ≤ Nat.card (fixedSubgroup ρ x) * Nat.card (fixedSubgroup ρ (x * z)) *
        Nat.card (fixedSubgroup ρ (x * z ^ 2)) :=
      Nat.mul_le_mul_right _ (card_sup_le_mul _ _)

theorem card_le_mul_fixedSubgroups {Γ V : Type*} [Group Γ] [Group V] [Finite V]
    (hV : ∀ a b : V, a * b = b * a) (hV3 : ¬ 3 ∣ Nat.card V) (ρ : Γ →* MulAut V) {x z : Γ}
    (hx : x ^ 3 = 1) (hz : z ^ 3 = 1) (hxz : x * z = z * x)
    (hfree : ∀ v : V, ρ z v = v → v = 1) :
    Nat.card V ≤ Nat.card (fixedSubgroup ρ x) * Nat.card (fixedSubgroup ρ (x * z)) *
      Nat.card (fixedSubgroup ρ (x * z ^ 2)) := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hV }
  exact card_le_mul_fixedSubgroups_aux hV3 ρ hx hz hxz hfree

theorem card_modEq_one_of_fixedPointFree {V : Type*} [Group V] [Finite V] (σ : MulAut V)
    (h3 : σ ^ 3 = 1) (hfree : ∀ v : V, σ v = v → v = 1) : Nat.card V ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers σ) := by
    have hord : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  have hmod := hp.card_modEq_card_fixedPoints V
  have hfix : MulAction.fixedPoints (Subgroup.zpowers σ) V = {1} := by
    ext v
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hfree v (h ⟨σ, Subgroup.mem_zpowers σ⟩)
    · rintro rfl g
      exact map_one (g : MulAut V)
  rw [hfix] at hmod
  simpa using hmod

end CFSG.LocalAnalysis.RankThreeTheoremC
