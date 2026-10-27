module

public import CFSG.LieType.Chevalley.E7Three.PauliWords
public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.RankThree.PartOne.KLAY.RootSL2
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.FrameWords

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Chevalley.E7Three.PauliWords

open scoped MatrixGroups

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem frame_mem_adjointGroup (ρ : SL(3, K) →* ModGL τ K)
    (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ) (hF : IsA2Frame ρ σ) (A : SL(3, K)) :
    ρ A ∈ adjointGroup τ K := by
  have hle : rootSpan τ K {α | ∃ i j : Fin 3, i ≠ j ∧ α = σ i j} ≤ adjointGroup τ K :=
    iSup_le fun α => iSup_le fun hα => rootSubgroup_le_adjointGroup α
  apply hle
  rw [← hF.range]
  exact ⟨A, rfl⟩

theorem diagonalWord_image (θ : SL(3, K) →* ModGL τ K) (j : Fin τ.rank)
    (hθ : θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (Pi.single j 1))
    (ζ : Kˣ) : θ (diagonalWord ζ) = torusElt τ K j ζ := by
  rw [diagonalWord, ← MonoidHom.comp_apply, hθ,
    CFSG.RankThree.PartOne.KLAY.rootSL2_single]
  change simpleRootSL2 τ K j (HSL ζ) = torusElt τ K j ζ
  exact simpleRootSL2_HSL j ζ

theorem centralWord_image (θ : SL(3, K) →* ModGL τ K) (i j : Fin τ.rank)
    (h0 : θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (Pi.single i 1))
    (h1 : θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (Pi.single j 1))
    (ζ : Kˣ) : θ (centralWord ζ) = torusElt τ K i ζ * torusElt τ K j (ζ ^ 2) := by
  rw [centralWord, map_mul, ← MonoidHom.comp_apply, h0,
    ← MonoidHom.comp_apply, h1, CFSG.RankThree.PartOne.KLAY.rootSL2_single,
    CFSG.RankThree.PartOne.KLAY.rootSL2_single]
  change simpleRootSL2 τ K i (HSL ζ) * simpleRootSL2 τ K j (HSL (ζ ^ 2)) = _
  rw [simpleRootSL2_HSL, simpleRootSL2_HSL]

theorem cycleWord_image (θ : SL(3, K) →* ModGL τ K)
    (α β : Fin τ.rank → ℤ) (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h0 : θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K α)
    (h1 : θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K β) :
    θ (cycleWord (K := K)) = canonicalRep (coxeterSystem τ) K (rootReflection α) *
      canonicalRep (coxeterSystem τ) K (rootReflection β) := by
  rw [cycleWord, map_mul, ← MonoidHom.comp_apply, h0, ← MonoidHom.comp_apply, h1]
  change rootWeylSL2 τ K α 1 * rootWeylSL2 τ K β 1 = _
  rw [EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo hα,
    EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo hβ]

end CFSG.LieType.Chevalley.E7Three.FrameWords
