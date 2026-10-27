module

public import CFSG.FeitThompson.Representations.NormalKernelLayerWeightedDegreeSum
import CFSG.FeitThompson.Representations.NoncoherentChiefReduction
import CFSG.FeitThompson.Local.OddFrobeniusComplementCyclicSylows
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInducedFamily
open scoped Pointwise

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {H E : Subgroup L}

theorem isCoherent_kerLayerIndFam_bot_of_exponent_dvd_sub_one
    [H.Normal] [Group.IsNilpotent ↥H]
    (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥) (_hE : E ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0)
    (hexp : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥H → Monoid.exponent ↥E ∣ p - 1) :
    IsCoherent (kerLayerIndFam (⊥ : Subgroup L) H) τ := by
  by_contra hnc
  obtain ⟨p, a, -, hp, ha, -, hcard, -, hnd⟩ :=
    exists_prime_pow_natCard_not_dvd_sub_one_of_not_isCoherent
      (E := E) hodd hH hmul hinf hC τ hτiso hτ1 hnc
  have hpH : p ∣ Nat.card ↥H := hcard ▸ dvd_pow_self p (by omega)
  have hexpE : Monoid.exponent ↥E = Nat.card ↥E :=
    exponent_eq_natCard_of_free_complement hodd hH hC
  exact hnd (hexpE ▸ hexp p hp hpH)

theorem isCoherent_kerLayerIndFam_bot_of_exponent_dvd_sub_one_of_series
    [H.Normal]
    (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥) (hE : E ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hnil : ∃ (t : ℕ) (S : ℕ → Subgroup ↥H), S 0 = ⊥ ∧ S t = ⊤ ∧ (∀ i < t, S i ≤ S (i + 1)) ∧
      (∀ i, (S i).Normal) ∧ ∀ i, 1 ≤ i → i ≤ t → ⁅(⊤ : Subgroup ↥H), S i⁆ ≤ S (i - 1))
    (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0)
    (hexp : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥H → Monoid.exponent ↥E ∣ p - 1) :
    IsCoherent (kerLayerIndFam (⊥ : Subgroup L) H) τ :=
  haveI : Group.IsNilpotent ↥H := (isNilpotent_iff_exists_normal_series_commutator_le ↥H).2 hnil
  isCoherent_kerLayerIndFam_bot_of_exponent_dvd_sub_one
    (E := E) hodd hH hE hmul hinf hC τ hτiso hτ1 hexp

end CFSG.FeitThompson

end
