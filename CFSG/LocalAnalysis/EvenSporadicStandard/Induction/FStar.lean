module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

@[expose] def FStarSimple {H : Type} [Group H] (N : Subgroup H) : Prop :=
  CFSG.generalizedFitting H = N ∧ IsSimpleGroup ↥N ∧ ∃ a b : ↥N, a * b ≠ b * a

variable {H : Type} [Group H] {N : Subgroup H}

theorem FStarSimple.generalizedFitting_eq (h : FStarSimple N) : CFSG.generalizedFitting H = N :=
  h.1

theorem FStarSimple.isSimpleGroup (h : FStarSimple N) : IsSimpleGroup ↥N := h.2.1

theorem FStarSimple.nonabelian (h : FStarSimple N) : ∃ a b : ↥N, a * b ≠ b * a := h.2.2

theorem FStarSimple.normal (h : FStarSimple N) : N.Normal :=
  h.1 ▸ (CFSG.LocalCores.generalized_fitting_characteristic (G := H)).2

theorem FStarSimple.centralizer_le [Finite H] (h : FStarSimple N) :
    centralizer (N : Set H) ≤ N :=
  h.1 ▸ CFSG.centralizer_generalizedFitting_le H

theorem fStarSimple_top (H : Type) [Group H] [Finite H] [IsSimpleGroup H]
    (hna : ∃ a b : H, a * b ≠ b * a) : FStarSimple (⊤ : Subgroup H) := by
  have hn : (CFSG.generalizedFitting H).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := H)).2
  have hC := CFSG.centralizer_generalizedFitting_le H
  have htop : CFSG.generalizedFitting H = ⊤ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exfalso
      rw [h] at hC
      obtain ⟨a, b, hab⟩ := hna
      have hb : b ∈ centralizer ((⊥ : Subgroup H) : Set H) := by
        rw [mem_centralizer_iff]
        intro m hm
        rw [coe_bot, Set.mem_singleton_iff] at hm
        rw [hm, one_mul, mul_one]
      have ha : a ∈ centralizer ((⊥ : Subgroup H) : Set H) := by
        rw [mem_centralizer_iff]
        intro m hm
        rw [coe_bot, Set.mem_singleton_iff] at hm
        rw [hm, one_mul, mul_one]
      have hb1 : b = 1 := Subgroup.mem_bot.mp (hC hb)
      have ha1 : a = 1 := Subgroup.mem_bot.mp (hC ha)
      exact hab (by rw [ha1, hb1])
    · exact h
  refine ⟨htop, MulEquiv.isSimpleGroup (Subgroup.topEquiv (G := H)), ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩

end CFSG.EvenSporadicStandard.Induction
