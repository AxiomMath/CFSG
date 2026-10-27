module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCls2

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

section Main

theorem sum_cent_eq : ∑ j : Fin 9, 3317760 / centTab[(j : ℕ)]! = 10575 := by
  decide

theorem invol_classes (hPA : Pg ≤ AutC) (htF : ∀ c ∈ Pg, c tF = tF) :
    ∀ g : Pg, g * g = 1 → g ≠ 1 → ∃ j : Fin 9, ∃ c : Pg, g = c * repPg j * c⁻¹ := by
  let X : Set Pg := {g | g * g = 1 ∧ g ≠ 1}
  have hX : ∀ c g : Pg, g ∈ X → c * g * c⁻¹ ∈ X := by
    rintro c g ⟨h1, h2⟩
    refine ⟨?_, fun h => h2 ?_⟩
    · calc c * g * c⁻¹ * (c * g * c⁻¹) = c * (g * g) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
  have hr : ∀ j : Fin 9, repPg j ∈ X := fun j =>
    ⟨Subtype.ext (repPerm_sq j.2), fun h => repPerm_ne_one j.2 (congrArg Subtype.val h)⟩
  have hinv : ∀ c g : Pg, fp ((c * g * c⁻¹ : Pg) : Equiv.Perm (Fin 128)) =
      fp (g : Equiv.Perm (Fin 128)) :=
    fun c g => fp_conj hPA htF c.2 g
  have hdist : ∀ j j' : Fin 9, fp (repPg j : Equiv.Perm (Fin 128)) =
      fp (repPg j' : Equiv.Perm (Fin 128)) → j = j' := by
    intro j j' h
    by_contra hne
    apply fpTab_ne j.2 j'.2 (fun e => hne (Fin.ext e))
    rw [← fp_repPerm j.2, ← fp_repPerm j'.2]
    exact h
  have hsum : ∑ j : Fin 9, Nat.card Pg / Nat.card (Subgroup.centralizer ({repPg j} : Set Pg)) =
      Nat.card X := by
    simp only [card_Pg, card_cent]
    rw [show Nat.card X = 10575 from card_invol]
    exact sum_cent_eq
  exact fun g hg1 hg2 => cover_by_classes X hX (fun j : Fin 9 => repPg j) hr
    (fun g : Pg => fp (g : Equiv.Perm (Fin 128))) hinv hdist hsum g ⟨hg1, hg2⟩

end Main

end CFSG.EvenSporadicStandard.Fin76b.W16
