module

public import CFSG.GH74.GLS.Stage2.Local.Closed
public import CFSG.GH74.GLS.Stage2.Local.P34Step1

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

@[expose] def Step23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ → HasTwoInvolutionClasses (HBar H) →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) ∧
        (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) ∧ PerfInJ H

@[expose] def Step5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → HasTwoInvolutionClasses (HBar H) → FUS H → False

@[expose] def Step6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H →
      (∀ Y : Subgroup G, Cen z ≤ Y → Y < H → Prop34Concl z k S Y) → C0 z k S H →
        IsCoatom (barIn H (Cen z)) ∧ barIn H (LC z) ≤ generalizedFitting (HBar H) ∧
          CFSG.GH74.GLS.Bg.Fm (barIn H (Cen z)) = barIn H (zpowers z)

theorem leaf_prop34_of (h93 : IVK93) (hm12 : Prop34M12) (hOne : NoOneClassC0) (h23 : Step23) (h5 : Step5)
    (h6 : Step6) : Leaf_Prop34 := by
  intro G _ _ z k S hctx
  suffices hmain : ∀ n : ℕ, ∀ H : Subgroup G, Nat.card ↥H = n → Cen z ≤ H → H ≠ ⊤ →
      Prop34Concl z k S H from fun H hCH hne => hmain _ H rfl hCH hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hCH hne
    by_cases hV : pCore 2 (HBar H) = ⊥
    · have h2 := hasTwoInvolutionClasses hctx hne hCH
      obtain ⟨hs, hnab, hPerf⟩ := h23 G z k S hctx H hne hCH hV h2
      rcases h93 G z k S hctx H hne hCH hV hs hnab hPerf h2 with hC0 | hFUS
      · have hIH : ∀ Y : Subgroup G, Cen z ≤ Y → Y < H → Prop34Concl z k S Y := by
          intro Y hY hlt
          refine ih (Nat.card ↥Y) ?_ Y rfl hY (ne_top_of_lt (hlt.trans_le le_top))
          rw [← hn]
          exact Subgroup.card_lt_of_lt hlt
        obtain ⟨hcoatom, hLle, hFm⟩ := h6 G z k S hctx H hne hCH hIH hC0
        have hC0' := hC0
        obtain ⟨ε, q, L₁, L₂, hk, hL4, hq3, hpsp, hnS, hO2⟩ := hC0
        have hq4 : q % 4 = (if ε then 3 else 1) := by
          rcases hL4.fusion with ⟨-, hone⟩ | ⟨h2, -⟩
          · exact (hOne G z k S hctx H hne hCH hC0' hone).elim
          · exact h2
        exact Or.inr (Or.inr ⟨ε, q, L₁, L₂, hk, hL4, hq4, hq3, hpsp, hcoatom, hLle, hnS, hO2, hFm⟩)
      · exact (h5 G z k S hctx H hne hCH h2 hFUS).elim
    · refine Or.inl ?_
      by_cases hk : k = Kind.m12
      · subst hk
        exact hm12 G z S hctx H hne hCH hV
      · exact stepOne hctx hk hCH hV

end CFSG.GH74.GLS.Stage2.Local.P34
