module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelCd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Transport
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Transfer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.NativeSporadic CFSG.EvenSmallLie

theorem exists_localModel_of_equiv {X : Type} [Group X] (E₀ : Subgroup X) (M : LocalModel X E₀)
    {Λ : Type} [Group Λ] (ψ : Λ ≃* X) : ∃ E' : Subgroup Λ, LocalModel Λ E' :=
  ⟨E₀.map ψ.symm.toMonoidHom, M.of_mulEquiv ψ.symm⟩

theorem exists_localModel
    (R : Fi22CoverRest) {G : Type} [Group G] {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Fi22) :
    ∃ E' : Subgroup L, LocalModel L E' := by
  obtain ⟨τ, hτ⟩ : ∃ τ : center L, τ ≠ 1 := by
    obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.1 h2
    by_cases hx : x = 1
    · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
    · exact ⟨x, hx⟩
  obtain ⟨ψ, -⟩ := exists_iso_Cd hq h2 hQ (τ := (τ : L)) τ.2 (fun h => hτ (Subtype.ext h))
  exact exists_localModel_of_equiv E0 (localModel_Cd R) ψ

end CFSG.EvenSporadicStandard.TwoFi22.DS81
