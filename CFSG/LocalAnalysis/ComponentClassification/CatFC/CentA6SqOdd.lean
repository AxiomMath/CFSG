module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqMain

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)

@[expose] def OddA6Family (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t n p f →
    LieModel S t n p f → ∀ σ : MulAut S, orderOf σ = 2 → Nat.card (autCentralizer σ) ≤ 5760 →
    Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)) →
    129600 ∣ Nat.card S → False

theorem a6OddArm_of_families (h : ∀ t, OddA6Family t) : A6OddArm := by
  intro S _ _ _ _ σ hP hσ hC hC' h129
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hP
  exact h t S n p f hp hp2 hadm hm σ hσ hC hC' h129

end CFSG.ComponentClassification.CatFC
