module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Basic

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore


@[expose] def E8KillsSeventyEight {L : Type} [Field L] (a : Fin 2 → Fin Tag.E8.rank → Lˣ) :
    Prop :=
  ∀ c : Fin 2 → ZMod 3, c ≠ 0 →
    {α : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 α ∧
      rootChar (fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val) α = 1}.ncard = 78

@[expose] def E8D4OrthOrbit {L : Type} [Field L] (a : Fin 2 → Fin Tag.E8.rank → Lˣ)
    (w : WeylGroup Tag.E8) : Prop :=
  (familyKernel a).ncard = 24 ∧
    (∀ γ ∈ familyKernel a, w • γ = γ ∨ iform γ (w • γ) = 0) ∧
    (∀ d ∈ familyKernel a, IsOrthTriple w d → ∀ β ∈ familyKernel a, IsOrthTriple w β →
      ∃ l : List (Fin Tag.E8.rank → ℤ), l.length ≤ 2 ∧
        (∀ δ ∈ l, δ ∈ familyKernel a ∧ IsOrthTriple w δ) ∧
        (l.map (tripleRefl w)).prod • β ∈ ({d, w • d, w ^ 2 • d} : Set (Fin Tag.E8.rank → ℤ))) ∧
    ∃ d ∈ familyKernel a, iform d (w • d) = 0 ∧ iform d (w ^ 2 • d) = 0 ∧
      iform (w • d) (w ^ 2 • d) = 0

@[expose] def E8D4Triangles (w : WeylGroup Tag.E8) : Prop :=
  (∀ α, IsRoot Tag.E8 α → w • α ≠ α) ∧
    ∑ j, (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) j = -4

@[expose] def E8ThreeKilledPlaneBlocks : Prop :=
  ∀ (L : Type) [Field L] (a : Fin 2 → Fin Tag.E8.rank → Lˣ),
    (∀ (s : Fin 2) (i : Fin Tag.E8.rank), a s i ^ 3 = 1) →
    (familyKernel (τ := Tag.E8) a).Nonempty →
    ∀ w : WeylGroup Tag.E8, w ^ 3 = 1 → (∀ s, w ∈ rootCharStabilizer (a s)) →
      w ∈ kernelWeylGroup (familyChar a) ∨
        (∃ B : KernelBlocks Tag.E8 (familyKernel a),
          ∀ j : Fin 3, (fun α => w • α) '' B.blk j = B.blk (j + 1)) ∨
        (E8KillsSeventyEight a ∧ (E8D4OrthOrbit a w ∨ E8D4Triangles w))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
