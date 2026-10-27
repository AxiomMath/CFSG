module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviA5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviChar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviSubsys
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviD4
public import CFSG.GroupTheory.ProjectiveElemAbelianRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


private theorem card_le_pow_five_of_le_graphFixedParabolicLevi_twE6MaxA2A1
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v})
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p ^ 5 := by
  have hsub : E ≤ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 3} :=
    le_subsystemGroup_of_le_graphFixedParabolicLevi_A2A1 hF σ hσ hp hp2 hpq hE hEel
  have hfix : E ≤ twistedFixedGroup TwistTag.E6 F σ.toRingHom :=
    (hE.trans (graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F)
      (σ := σ.toRingHom) (J := twE6MaxA2A1))).trans
      (graphFixedRootGroup_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom))
  exact card_le_pow_five_subsystemGroup_e6A2A1 hF σ hσ hp hp2 hpq hPRL hEel (le_inf hsub hfix)

private theorem card_le_pow_five_of_le_graphFixedParabolicLevi_twE6MaxA1A2
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v})
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p ^ 5 := by
  have hfix : E ≤ twistedFixedGroup TwistTag.E6 F σ.toRingHom :=
    (hE.trans (graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F)
      (σ := σ.toRingHom) (J := twE6MaxA1A2))).trans
      (graphFixedRootGroup_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom))
  have hbound := card_le_mul_card_inf_subsystemGroup_A1A2 hF σ hσ hp hp2 hpq hE hEel
  have hE'el : CFSG.Open.IsElemAbelian p
      (E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 2 ∧ i.val ≠ 4}) :=
    hEel.mono inf_le_left
  have hE' : E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 2 ∧ i.val ≠ 4} ≤
      subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 2 ∧ i.val ≠ 4} ⊓
        twistedFixedGroup TwistTag.E6 F σ.toRingHom :=
    le_inf inf_le_right (inf_le_left.trans hfix)
  have hle := card_le_pow_four_subsystemGroup_e6A1A2 hF σ hσ hp hp2 hpq hPRL hE'el hE'
  calc Nat.card E
      ≤ p * Nat.card ↥(E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 2 ∧ i.val ≠ 4}) :=
        hbound
    _ ≤ p * p ^ 4 := Nat.mul_le_mul_left p hle
    _ = p ^ 5 := by ring

private theorem card_le_pow_five_of_le_graphFixedParabolicLevi_twE6MaxD4
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p ^ 5 := by
  haveI : CharP F 2 := by
    have hn : 1 ≤ n * 2 := by
      have h2F : 2 ≤ Nat.card F := by
        haveI : Fintype F := Fintype.ofFinite F
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card (α := F)
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp at hF
        omega
      · omega
    exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := n * 2) hn (by rw [hF, pow_mul])
  have hbound := card_le_mul_card_inf_subsystemGroup_D4 hF σ hσ hp hp2 hpq hE hEel
  have hE'el : CFSG.Open.IsElemAbelian p
      (E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 0 ∧ i.val ≠ 5}) :=
    hEel.mono inf_le_left
  have hle : Nat.card ↥(E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 0 ∧ i.val ≠ 5}) ≤
      p ^ 4 :=
    card_le_pow_four_subsystemGroup_e6D4 hp hp2 inf_le_right hE'el
  calc Nat.card E
      ≤ p * Nat.card ↥(E ⊓ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 0 ∧ i.val ≠ 5}) :=
        hbound
    _ ≤ p * p ^ 4 := Nat.mul_le_mul_left p hle
    _ = p ^ 5 := by ring

theorem rk2TwE6LeviRankInputMaximal_holds : Rk2TwE6LeviRankInputMaximal := by
  intro F _ _ n hF σ hσ p hp hp2 hpq
  have hrF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact CFSG.LieType.SeitzGeneration.dvd_sq_sub_one_of_dvd_add_one hpq
  have hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup p R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ p) v = a • v) →
      Nat.card R ≤ p ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} := by
    intro V _ _ _ R hR hcomm hpow
    exact CFSG.GroupTheory.card_le_pow_finrank_sub_one_mul_card_scalar hp hp2 hrF R hR hcomm hpow
  exact ⟨fun E hE hEel =>
      card_le_pow_five_of_le_graphFixedParabolicLevi_A5 hF σ hσ hp hp2 hpq hE hEel,
    fun E hE hEel =>
      card_le_pow_five_of_le_graphFixedParabolicLevi_twE6MaxA2A1 hF σ hσ hp hp2 hpq hPRL hE hEel,
    fun E hE hEel =>
      card_le_pow_five_of_le_graphFixedParabolicLevi_twE6MaxA1A2 hF σ hσ hp hp2 hpq hPRL hE hEel,
    fun E hE hEel =>
      card_le_pow_five_of_le_graphFixedParabolicLevi_twE6MaxD4 hF σ hσ hp hp2 hpq hE hEel⟩

end CFSG.LocalAnalysis.GLTheoremA
