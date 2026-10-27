module

public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X Y : Type*} [Group X] [Group Y]

theorem natCard_map_dvd (K : Subgroup X) (f : X →* Y) : Nat.card (K.map f) ∣ Nat.card K := by
  have hrange : K.map f = (f.comp K.subtype).range := by
    rw [MonoidHom.range_comp, K.range_subtype]
  rw [hrange, ← natCard_setRange_eq_natCard_range]
  exact natCard_setRange_dvd_natCard_domain _

theorem commutator_le_inf_of_sup_normal {D A K : Subgroup X} {p : ℕ} (hp : p.Prime)
    [D.Normal] [Finite A] (hA : IsPGroup p A) (hDA : (D ⊔ A).Normal)
    (hK : Nat.Coprime (Nat.card K) p) (hKA : A ≤ Subgroup.normalizer (K : Set X)) :
    ⁅K, A⁆ ≤ K ⊓ D := by
  have := Fact.mk hp
  set φ : X →* X ⧸ D := QuotientGroup.mk' D
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective D
  have hD : D.map φ = ⊥ := (Subgroup.map_eq_bot_iff D).2 (QuotientGroup.ker_mk' D).ge
  have hmapA : (D ⊔ A).map φ = A.map φ := by rw [Subgroup.map_sup, hD, bot_sup_eq]
  have : (A.map φ).Normal := hmapA ▸ hDA.map _ hsurj
  have hKn : A.map φ ≤ Subgroup.normalizer ((K.map φ : Subgroup (X ⧸ D)) : Set (X ⧸ D)) :=
    le_trans (Subgroup.map_mono hKA) (Subgroup.le_normalizer_map _)
  have h1 : ⁅K.map φ, A.map φ⁆ ≤ K.map φ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hKn
  have h2 : ⁅K.map φ, A.map φ⁆ ≤ A.map φ := Subgroup.commutator_le_right _ _
  have hcop : Nat.Coprime (Nat.card (K.map φ)) (Nat.card (A.map φ)) := by
    obtain ⟨n, hn⟩ := hA.exists_card_eq
    refine Nat.Coprime.coprime_dvd_left (natCard_map_dvd K φ) ?_
    refine Nat.Coprime.coprime_dvd_right (natCard_map_dvd A φ) ?_
    rw [hn]
    exact hK.pow_right n
  have hbot : ⁅K.map φ, A.map φ⁆ = ⊥ :=
    le_bot_iff.1 (Subgroup.disjoint_of_coprime_natCard hcop h1 h2)
  refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hKA) ?_
  rw [← QuotientGroup.ker_mk' D, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator]
  exact hbot

theorem commutator_le_inf_of_card_eq_prime_pow {D A K : Subgroup X} {p n : ℕ} (hp : p.Prime)
    [D.Normal] (hA : Nat.card A = p ^ n) (hDA : (D ⊔ A).Normal)
    (hK : Nat.Coprime (Nat.card K) p) (hKA : A ≤ Subgroup.normalizer (K : Set X)) :
    ⁅K, A⁆ ≤ K ⊓ D := by
  have : Finite A := Nat.finite_of_card_ne_zero (by
    rw [hA]; exact pow_ne_zero n hp.pos.ne')
  exact commutator_le_inf_of_sup_normal hp (IsPGroup.of_card hA) hDA hK hKA

theorem commutator_le_of_sup_normal {D A K : Subgroup X} {p : ℕ} (hp : p.Prime)
    [D.Normal] [Finite A] (hA : IsPGroup p A) (hDA : (D ⊔ A).Normal)
    (hK : Nat.Coprime (Nat.card K) p) (hKA : A ≤ Subgroup.normalizer (K : Set X)) :
    ⁅K, A⁆ ≤ D :=
  (commutator_le_inf_of_sup_normal hp hA hDA hK hKA).trans inf_le_right

end

end CFSG.FeitThompson
