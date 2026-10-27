module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Main

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def T1bLieHardAt (t : StatedLieTag) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → ∀ p : ℕ, p.Prime → p ≠ 2 →
      (CFSG.Open.pRank p (⊤ : Subgroup L) < 7 ∨ p ∣ Nat.card (Subgroup.center L)) →
      (∃ (n r f : ℕ), CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f ∧
        ¬ OutEasy p t n r f) →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 1

theorem t1bLieHard_of_five (hPSL : T1bLieHardAt .PSL) (hPSU : T1bLieHardAt .PSU)
    (hPOP : T1bLieHardAt .POmegaPlus) (hE6 : T1bLieHardAt .E6)
    (hTE6 : T1bLieHardAt .twistedE6) : T1bLieHard := by
  intro L _ _ hLC hq hK p hp hp2 hcond ⟨t, n, r, f, hm, hE⟩
  have key : ∀ t, T1bLieHardAt t → CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f →
      ¬ OutEasy p t n r f →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 1 :=
    fun t ht hm hE => ht L hLC hq hK p hp hp2 hcond ⟨n, r, f, hm, hE⟩
  cases t
  case PSL => exact key _ hPSL hm hE
  case PSU => exact key _ hPSU hm hE
  case POmegaPlus => exact key _ hPOP hm hE
  case E6 => exact key _ hE6 hm hE
  case twistedE6 => exact key _ hTE6 hm hE
  all_goals exact absurd trivial hE

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
