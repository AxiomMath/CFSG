module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10SporOrd
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10SporComp
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10SporFi
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10SporB
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10SporM

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

theorem a10SporadicClause_holds
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x)
    (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hA : IsA10Type (↥P ⧸ Open.fusionZStar ↥P)) :
    Nonempty (S ≃* NativeSporadic.Carrier .HN) := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  by_cases hs : s = .HN
  · subst hs
    exact ⟨e⟩
  have key : A10SporClauseFor s := by
    cases s with
    | M11 => exact a10SporClause_M11
    | M12 => exact a10SporClause_M12
    | M22 => exact a10SporClause_M22
    | M23 => exact a10SporClause_M23
    | M24 => exact a10SporClause_M24
    | J1 => exact a10SporClause_J1
    | J2 => exact a10SporClause_J2
    | J3 => exact a10SporClause_J3
    | J4 => exact a10SporClause_J4
    | Co1 => exact a10SporClause_Co1
    | Co2 => exact a10SporClause_Co2
    | Co3 => exact a10SporClause_Co3
    | Fi22 => exact a10SporClause_Fi22
    | Fi23 => exact a10SporClause_Fi23
    | Fi24Prime => exact a10SporClause_Fi24Prime
    | HS => exact a10SporClause_HS
    | McL => exact a10SporClause_McL
    | He => exact a10SporClause_He
    | Ru => exact a10SporClause_Ru
    | Suz => exact a10SporClause_Suz
    | ONan => exact a10SporClause_ONan
    | HN => exact absurd rfl hs
    | Ly => exact a10SporClause_Ly
    | Th => exact a10SporClause_Th
    | B => exact a10SporClause_B
    | M => exact a10SporClause_M
  exact (key S hna ⟨e⟩ σ P h hA).elim

end CFSG.ComponentClassification.EvenPump
