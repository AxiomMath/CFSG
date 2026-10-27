module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Neg
public import Certificates.Data.SmithE8MAbel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.SmithE8M CFSG.SeitzReduction.E7Pilot CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction

@[expose] def Bk (k : Fin 5) : Finset (Fin e7Data.d) :=
  Finset.univ.filter fun c =>
    (∃ β ∈ e7RepFrames k, e7Data.wt c ⬝ᵥ β = 1) ∧
    ∀ i : Fin 126, 0 < height (e8mRoot i) → (∀ β ∈ e7RepFrames k, 0 ≤ iform (e8mRoot i) β) →
      e7Data.wt c ⬝ᵥ e8mRoot i ≠ -1

set_option maxRecDepth 20000 in
theorem frame_orth : ∀ k : Fin 5, ∀ β ∈ e7RepFrames k, ∀ β' ∈ e7RepFrames k, β ≠ β' →
    MinData.toWeight β ⬝ᵥ β' = 0 := by decide +kernel

set_option maxRecDepth 20000 in
theorem bk_clique (k : Fin 5) (hk : k.val ≤ 2) : ∀ μ ∈ Bk k, ∀ l ∈ Bk k, μ ≠ l → ∃ i : Fin 126,
    e7Data.wt l = e7Data.wt μ + MinData.toWeight (e8mRoot i) ∧
    e7Data.wt μ ⬝ᵥ e8mRoot i = -1 ∧
    ∀ ν ∈ Bk k, ν ≠ μ → ν ≠ l → e7Data.wt ν ⬝ᵥ e8mRoot i ≠ -1 := by
  have h : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases h with h | h | h
  · obtain rfl : k = 0 := Fin.ext h
    decide +kernel
  · obtain rfl : k = 1 := Fin.ext h
    decide +kernel
  · obtain rfl : k = 2 := Fin.ext h
    decide +kernel

@[expose] def PivSet (k : Fin 5) : Finset (Fin e7Data.d) :=
  Finset.univ.filter fun c => ∃ a : Fin e7Data.d, ∃ β ∈ e7RepFrames k,
    e7Data.wt a ⬝ᵥ β = -1 ∧ (∀ β' ∈ e7RepFrames k, β' ≠ β → e7Data.wt a ⬝ᵥ β' ≠ -1) ∧
      e7Data.wt c = e7Data.wt a + MinData.toWeight β

set_option maxRecDepth 20000 in
theorem card_Piv : ∀ k : Fin 5, 12 ≤ (PivSet k).card ∧ (k ≠ 0 → 14 ≤ (PivSet k).card) := by
  decide +kernel

@[expose] def Pk (γ : Fin (Tag.rank .E7) → ℤ) : Bool := decide (γ ⟨1, by decide⟩ ≠ 0)

set_option maxRecDepth 20000 in
theorem witness_rep : ∀ k : Fin 5, 3 ≤ k.val → ∃ a c : Fin e7Data.d,
    (∀ γ ∈ e7RepFrames k, Pk γ = true → e7Data.wt a ⬝ᵥ γ = -1) ∧
    e7Data.wt c = -e7Data.wt a ∧
    e7Data.wt c = e7Data.wt a + (((e7RepFrames k).filter Pk).map MinData.toWeight).sum := by
  decide +kernel

end CFSG.GF2Type.SmithTypeE.E8
