module

public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G G' : Type*} [Group G] [Group G'] {π : Set ℕ} {m n : ℕ}

theorem isHallSubgroup_iff_natCard_div [Finite G] {H : Subgroup G} :
    IsHallSubgroup π H ↔
      IsPiNumber π (Nat.card H) ∧ IsPiNumber πᶜ (Nat.card G / Nat.card H) := by
  rw [isHallSubgroup_iff, Subgroup.index_eq_card, natCard_quotient_eq_natCard_div]

theorem isHallSubgroup_iff_natCard_range_leftCoset {H : Subgroup G} :
    IsHallSubgroup π H ↔ IsPiNumber π (Nat.card H) ∧
      IsPiNumber πᶜ (Nat.card (Set.range fun g : G => g • (H : Set G))) := by
  rw [isHallSubgroup_iff, natCard_range_leftCoset]

theorem natCard_comap_of_surjective [Finite G] {f : G →* G'} (hf : Function.Surjective f)
    (J : Subgroup G') : Nat.card (J.comap f) = Nat.card f.ker * Nat.card J := by
  have : Finite G' := Finite.of_surjective f hf
  have hidx : (J.comap f).index = J.index := Subgroup.index_comap_of_surjective J hf
  have h1 : (J.comap f).index * Nat.card (J.comap f) = Nat.card G := Subgroup.index_mul_card _
  have h2 : J.index * Nat.card J = Nat.card G' := Subgroup.index_mul_card J
  have h3 : f.ker.index * Nat.card f.ker = Nat.card G := Subgroup.index_mul_card _
  have h4 : f.ker.index = Nat.card G' := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hf, Subgroup.card_top]
  refine Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := J))) ?_
  calc J.index * Nat.card (J.comap f) = Nat.card G := by rw [← hidx]; exact h1
    _ = Nat.card G' * Nat.card f.ker := by rw [← h4]; exact h3.symm
    _ = J.index * (Nat.card f.ker * Nat.card J) := by rw [← h2]; ring

theorem IsHallSubgroup.comap_of_surjective [Finite G] {f : G →* G'}
    (hf : Function.Surjective f) (hker : IsPiNumber π (Nat.card f.ker))
    {J : Subgroup G'} (hJ : IsHallSubgroup π J) : IsHallSubgroup π (J.comap f) :=
  ⟨by rw [natCard_comap_of_surjective hf J]; exact hker.mul hJ.1,
    by rw [Subgroup.index_comap_of_surjective J hf]; exact hJ.2⟩

theorem IsHallSubgroup.comap_mk' [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsPiNumber π (Nat.card N)) {J : Subgroup (G ⧸ N)} (hJ : IsHallSubgroup π J) :
    IsHallSubgroup π (J.comap (QuotientGroup.mk' N)) :=
  hJ.comap_of_surjective (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk'])

theorem le_comap_mk' {N : Subgroup G} [N.Normal] (J : Subgroup (G ⧸ N)) :
    N ≤ J.comap (QuotientGroup.mk' N) :=
  (QuotientGroup.ker_mk' N).ge.trans (Subgroup.ker_le_comap _ J)

end

end CFSG.FeitThompson

