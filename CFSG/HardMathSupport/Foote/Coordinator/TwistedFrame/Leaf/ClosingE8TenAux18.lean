module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux17

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Glue

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem mem_mRoots_of_notBset {β : Fin Tag.E8.rank → ℤ}
    (h : β ∈ Deg1 TwClass.e8Ten.tag ∧ β ∉ CoordsAux.Bset TwClass.e8Ten) : β ∈ mRoots := by
  obtain ⟨hD, hB⟩ := h
  have hβ' : β ∈ deg1Roots :=
    mem_deg1Roots.2 ⟨(CoordAux.mem_Deg1.1 hD).1, (CoordAux.mem_Deg1.1 hD).2⟩
  rcases deg1_cases hβ' with hM | hS
  · exact hM
  · exact absurd ⟨hD, mem_S₁_of_sRoots hS⟩ hB

theorem opposite_two_of_cases
    {H : Subgroup (ModGL Tag.E8 K)}
    (hb : TwBasic (TwClass.e8Ten.X₁ D) (TwClass.e8Ten.X₂ D))
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K)
    (hBH : conjSub q (Heis.Uneg Tag.E8 K) ≤ H)
    (hBX : ¬ conjSub q (Heis.Uneg Tag.E8 K) ≤ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)
    (case1 : ∀ v : ModGL Tag.E8 K, v ∈ Qθ Tag.E8 K → conjSub v (Heis.Uneg Tag.E8 K) ≤ H →
      (∀ β, CoordsAux.κ D v β ≠ 0 → β ∈ mRoots) →
      (∃ β, CoordsAux.κ D v β ≠ 0 ∧ (cls β = 2 ∨ cls β = 3)) →
      ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
        heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D))
    (case2 : ∀ v : ModGL Tag.E8 K, v ∈ Qθ Tag.E8 K → conjSub v (Heis.Uneg Tag.E8 K) ≤ H →
      (∀ β, CoordsAux.κ D v β ≠ 0 → β ∈ mRoots ∧ (cls β = 1 ∨ cls β = 4)) →
      (∃ β, CoordsAux.κ D v β ≠ 0) →
      ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
        heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)) :
    ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  obtain ⟨v, hvQ, hvB, hvs, hvne⟩ := opposite_reduce TwClass.e8Ten D hb hXH hq hBH hBX
  have hvM : ∀ β, CoordsAux.κ D v β ≠ 0 → β ∈ mRoots := fun β hβ =>
    mem_mRoots_of_notBset (hvs β hβ)
  by_cases h1 : ∃ β, CoordsAux.κ D v β ≠ 0 ∧ (cls β = 2 ∨ cls β = 3)
  · exact case1 v hvQ hvB hvM h1
  · refine case2 v hvQ hvB (fun β hβ => ⟨hvM β hβ, ?_⟩) hvne
    have h2 := mRoots_cls β (hvM β hβ)
    by_contra hcon
    apply h1
    exact ⟨β, hβ, by omega⟩

end Glue

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
