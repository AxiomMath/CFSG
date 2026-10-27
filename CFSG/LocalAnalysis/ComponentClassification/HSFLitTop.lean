module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGen4
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Blueprint Assembly.LowTwoRank

@[expose] def FritzTheoremB : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ (t : X) (L : Subgroup X), Config t L →
    ¬ (∀ P : Subgroup X, IsPGroup 2 P → ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P) →
    Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6)) ∧
      Nonempty (X ≃* NativeSporadic.HS)

theorem hsflit_of_parts
    (hGH : UFrontier.GH74ModelsInput)
    (hEven : ∀ (Y : Type) [Group Y] [Finite Y], (LieModel Y .PSL 2 2 3 ∨ LieModel Y .PSL 2 2 4 ∨
      LieModel Y .PSL 3 2 2 ∨ LieModel Y .twistedB2 0 2 3) → ∀ y : Y, orderOf y = 2 → Excluded y)
    (hSpor : ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1 ∨ s = .J2 ∨
      s = .J3 ∨ s = .McL ∨ s = .Ly) →
      ∀ y : NativeSporadic.Carrier s, orderOf y = 2 → Excluded y)
    (hB : FritzTheoremB) : GSLit.HarrisSolomonFritzInput := by
  intro X _ _ _ hnonab t ht L hLt hL hs hrank hsyl hcyc
  have h : Config t L := ⟨ht, hLt, hL, hs, hrank, hsyl, hcyc⟩
  by_cases hsect : ∀ P : Subgroup X, IsPGroup 2 P →
      ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P
  · exact Or.inl (oddLieType_of_gen4 hGH hEven hSpor hnonab h hsect)
  · exact Or.inr (hB X hnonab t L h hsect)

end CFSG.ComponentClassification.HSFLit
