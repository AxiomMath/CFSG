module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltAct
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFacts

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

theorem p456_isThreeCycle : p456.IsThreeCycle := card_support_eq_three_iff.mp (by decide)

theorem p123_isThreeCycle : p123.IsThreeCycle := card_support_eq_three_iff.mp (by decide)

theorem disjoint_p456_p123 : Disjoint p456.support p123.support := by decide

theorem pow_three_of_commute_p456_p123 {σ : Perm (Fin 7)} (h1 : Commute σ p456)
    (h2 : Commute σ p123) : σ ^ 3 = 1 := by
  have hrest : ∀ x, x ∉ p456.support → x ∉ p123.support → σ x = x := by
    intro x hx1 hx2
    have h0 : ∀ y : Fin 7, y ∉ p456.support → y ∉ p123.support → y = 0 := by decide
    obtain ⟨hs1, -⟩ := (p456_isThreeCycle.isCycle.commute_iff).mp h1
    obtain ⟨hs2, -⟩ := (p123_isThreeCycle.isCycle.commute_iff).mp h2
    have a1 : σ x ∉ p456.support := fun h => hx1 ((hs1 x).mp h)
    have a2 : σ x ∉ p123.support := fun h => hx2 ((hs2 x).mp h)
    exact (h0 _ a1 a2).trans (h0 x hx1 hx2).symm
  obtain ⟨i, j, hσ⟩ := eq_zpow_mul_zpow_of_commute p456_isThreeCycle p123_isThreeCycle
    disjoint_p456_p123 hrest h1 h2
  have hc : Commute p456 p123 := by
    show p456 * p123 = p123 * p456
    decide
  have h3a : p456 ^ 3 = 1 := by decide
  have h3b : p123 ^ 3 = 1 := by decide
  rw [hσ, ((hc.zpow_left i).zpow_right j).mul_pow, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast,
    zpow_natCast, h3a, h3b, one_zpow, one_zpow, one_mul]

theorem le_centralizer_of_isPGroup {G : Type*} [Group G] {B : Subgroup G}
    (ψB : B ≃* alternatingGroup (Fin 7)) {u v : G} (hu : u ∈ normalizer (B : Set G))
    (hv : v ∈ normalizer (B : Set G)) (hu' : actPerm ψB (Or.inr le_rfl) ⟨u, hu⟩ = p456)
    (hv' : actPerm ψB (Or.inr le_rfl) ⟨v, hv⟩ = p123) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (B : Set G)) (hPu : P ≤ centralizer ({u} : Set G))
    (hPv : P ≤ centralizer ({v} : Set G)) : P ≤ centralizer (B : Set G) := by
  intro h hh
  set σ := actPerm ψB (Or.inr le_rfl) ⟨h, hPN hh⟩ with hσ
  have hcomm : ∀ {z : G} (hz : z ∈ normalizer (B : Set G)), h * z = z * h →
      Commute σ (actPerm ψB (Or.inr le_rfl) ⟨z, hz⟩) := fun hz hhz => by
    show σ * _ = _ * σ
    rw [hσ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hhz
  have c1 := hcomm hu (mem_centralizer_singleton_iff.mp (hPu hh))
  have c2 := hcomm hv (mem_centralizer_singleton_iff.mp (hPv hh))
  rw [hu'] at c1
  rw [hv'] at c2
  have h3 := pow_three_of_commute_p456_p123 c1 c2
  obtain ⟨k, hk⟩ := hP ⟨h, hh⟩
  have h2k : σ ^ 2 ^ k = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨h, hPN hh⟩ : normalizer (B : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hord : orderOf σ ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2k)
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact (actPerm_eq_one_iff ψB (Or.inr le_rfl) ⟨h, hPN hh⟩).mp hord

end CFSG.ComponentClassification.RankTwoAlt
