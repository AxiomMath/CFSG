module

public import CFSG.LieType.BorelTits.Twisted
public import CFSG.LieType.BorelTits.Ree
public import CFSG.LieType.BorelTits.Tits
public import CFSG.LieType.BorelTits.Suzuki

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem holds_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n r f : ℕ}
    (h : LieModel X t n r f) (ht : t ≠ .Tits) : Holds X r := by
  rcases h with ⟨-, hcl⟩ | ⟨-, -, hce⟩ | ⟨-, -, hree⟩ | ⟨-, -, hsz⟩
  · exact holds_of_statedClassicalModel hcl
  · exact holds_of_chevalleyExceptionalModel hce
  · exact holds_of_reeTitsModel hree ht
  · exact holds_of_suzukiModel hsz

theorem holdsTits_of_lieModel_tits {X : Type} [Group X] {n r f : ℕ}
    (h : LieModel X .Tits n r f) : HoldsTits X r := by
  rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact holdsTits_of_reeTitsModel_tits hree
  · exact absurd hsz (by decide)

theorem lieModel_conclusion (X : Type) [Group X] (t : StatedLieTag) (n r f : ℕ)
    (hmodel : LieModel X t n r f) (U : Subgroup X) (hU : U ≠ ⊥) (hUr : IsPGroup r U) :
    ∃ (S : Sylow r X) (P : Subgroup X), P ≠ ⊤ ∧
      Subgroup.normalizer (U : Set X) ≤ P ∧
      pCoreOf r (Subgroup.normalizer (U : Set X)) ≤ pCoreOf r P ∧ U ≤ pCoreOf r P ∧
      (t ≠ .Tits → Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) ∧
      (t = .Tits → (S : Subgroup X) ≤ P) := by
  by_cases ht : t = .Tits
  · subst ht
    obtain ⟨S, P, hP, hN, hcore, hUP, hSP⟩ := holdsTits_of_lieModel_tits hmodel U hU hUr
    exact ⟨S, P, hP, hN, hcore, hUP, fun h => absurd rfl h, fun _ => hSP⟩
  · obtain ⟨S, P, hP, hN, hcore, hUP, hSP⟩ := holds_of_lieModel hmodel ht U hU hUr
    exact ⟨S, P, hP, hN, hcore, hUP, fun _ => hSP, fun h => absurd h ht⟩

end CFSG.LieType.BorelTits
