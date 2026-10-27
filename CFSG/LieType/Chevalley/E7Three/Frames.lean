module

public import CFSG.LieType.Chevalley.E7Three.PinnedBlocks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Frames

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.PartOne.KA5L CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Chevalley.E7Three.PinnedBlocks

open scoped MatrixGroups

@[expose] def nativePairs : Fin 3 → Option (Fin Tag.E7.rank) × Option (Fin Tag.E7.rank) :=
  ![(some (e7Index 1), some (e7Index 3)),
    (some (e7Index 5), some (e7Index 6)), (none, some (e7Index 0))]

@[expose] def nativeWeights (r : Fin 3) : Fin 3 → Fin Tag.E7.rank → ℤ :=
  ![0, -e7ExtVec (nativePairs r).1,
    -(e7ExtVec (nativePairs r).1 + e7ExtVec (nativePairs r).2)]

@[expose] def nativeA2Roots (r : Fin 3) (i j : Fin 3) : Fin Tag.E7.rank → ℤ :=
  nativeWeights r i - nativeWeights r j

theorem nativePairs_edge (r : Fin 3) :
    (nodeIdx (nativePairs r).1, nodeIdx (nativePairs r).2) ∈ e7EdgeIdx := by
  fin_cases r <;> decide +kernel

theorem nativeA2Roots_orthogonal : ∀ r s : Fin 3, r ≠ s → ∀ i j k l : Fin 3,
    nativeA2Roots r i j ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ nativeA2Roots s k l) = 0 := by
  simp only [nativeA2Roots, nativeWeights, nativePairs]
  decide +kernel

variable {K : Type} [Field K] [CharP K 2]

theorem frame_roots_eq (r : Fin 3) (ρ : SL(3, K) →* ModGL .E7 K)
    (σ : Fin 3 → Fin 3 → Fin Tag.E7.rank → ℤ) (hF : IsA2Frame ρ σ)
    (h01 : σ 0 1 = kacE7.extRoot (nativePairs r).1)
    (h12 : σ 1 2 = kacE7.extRoot (nativePairs r).2) : σ = nativeA2Roots r := by
  rw [kacE7_extRoot] at h01 h12
  have h00 : σ 0 0 = 0 := by
    have h : σ 0 0 + σ 0 0 = σ 0 0 + 0 := by
      simpa only [add_zero] using hF.add 0 0 0
    exact add_left_cancel h
  have h02 : σ 0 2 = e7ExtVec (nativePairs r).1 + e7ExtVec (nativePairs r).2 := by
    rw [← hF.add 0 1 2, h01, h12]
  have h0 : ∀ i : Fin 3, σ i 0 = nativeWeights r i := by
    intro i
    fin_cases i
    · simpa [nativeWeights] using h00
    · simpa [nativeWeights, h01] using hF.neg 0 1
    · simpa [nativeWeights, h02] using hF.neg 0 2
  funext i j
  rw [hF.eq_sub i j, h0 i, h0 j]
  rfl

theorem exists_raw_three_frames :
    ∃ ρ : Fin 3 → SL(3, K) →* ModGL .E7 K,
      ∀ r, IsA2Frame (ρ r) (nativeA2Roots r) := by
  have h : ∀ r : Fin 3, ∃ ρ : SL(3, K) →* ModGL .E7 K,
      IsA2Frame ρ (nativeA2Roots r) := by
    intro r
    obtain ⟨ρ, σ, hF, h01, h12⟩ :=
      e7_frames (L := K) (nativePairs r).1 (nativePairs r).2 (nativePairs_edge r)
    have hσ : σ = nativeA2Roots r := frame_roots_eq r ρ σ hF h01 h12
    exact ⟨ρ, by simpa only [hσ] using hF⟩
  choose ρ hρ using h
  exact ⟨ρ, hρ⟩

theorem nativeFrames_commute (ρ : Fin 3 → SL(3, K) →* ModGL .E7 K)
    (hρ : ∀ r, IsA2Frame (ρ r) (nativeA2Roots r)) {r s : Fin 3} (hrs : r ≠ s)
    (A B : SL(3, K)) : Commute (ρ r A) (ρ s B) := by
  let S₁ : Set (Fin Tag.E7.rank → ℤ) :=
    {α | ∃ i j : Fin 3, i ≠ j ∧ α = nativeA2Roots r i j}
  let S₂ : Set (Fin Tag.E7.rank → ℤ) :=
    {β | ∃ k l : Fin 3, k ≠ l ∧ β = nativeA2Roots s k l}
  have hS₁ : ∀ α ∈ S₁, IsRoot .E7 α := by
    rintro α ⟨i, j, hij, rfl⟩
    exact (hρ r).isRoot i j hij
  have hS₂ : ∀ β ∈ S₂, IsRoot .E7 β := by
    rintro β ⟨k, l, hkl, rfl⟩
    exact (hρ s).isRoot k l hkl
  have horth : ∀ α ∈ S₁, ∀ β ∈ S₂,
      α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    rintro α ⟨i, j, hij, rfl⟩ β ⟨k, l, hkl, rfl⟩
    exact nativeA2Roots_orthogonal r s hrs i j k l
  have hA : ρ r A ∈ rootSpan .E7 K S₁ := by
    rw [← (hρ r).range]
    exact ⟨A, rfl⟩
  have hB : ρ s B ∈ rootSpan .E7 K S₂ := by
    rw [← (hρ s).range]
    exact ⟨B, rfl⟩
  exact rootSpan_commute_of_orth (L := K) (Or.inr (Or.inr (Or.inl rfl)))
    hS₁ hS₂ horth _ hA _ hB

theorem exists_three_pinned_frames :
    ∃ (ρ : Fin 3 → SL(3, K) →* ModGL .E7 K) (d : Fin 3 → Fin 3 → Kˣ),
      (∀ r, IsA2Frame (ρ r) (nativeA2Roots r)) ∧
      (∀ r,
        ((ρ r).comp (conjDiag3Hom (d r))).comp (blockSL K 3 2 0 (by omega)) =
          rootSL2 .E7 K (kacE7.extRoot (nativePairs r).1) ∧
        ((ρ r).comp (conjDiag3Hom (d r))).comp (blockSL K 3 2 1 (by omega)) =
          rootSL2 .E7 K (kacE7.extRoot (nativePairs r).2)) ∧
      ∀ r s, r ≠ s → ∀ A B,
        Commute ((ρ r).comp (conjDiag3Hom (d r)) A)
          ((ρ s).comp (conjDiag3Hom (d s)) B) := by
  obtain ⟨ρ, hρ⟩ := exists_raw_three_frames (K := K)
  have hp : ∀ r : Fin 3, ∃ d : Fin 3 → Kˣ,
      ((ρ r).comp (conjDiag3Hom d)).comp (blockSL K 3 2 0 (by omega)) =
        rootSL2 .E7 K (kacE7.extRoot (nativePairs r).1) ∧
      ((ρ r).comp (conjDiag3Hom d)).comp (blockSL K 3 2 1 (by omega)) =
        rootSL2 .E7 K (kacE7.extRoot (nativePairs r).2) := by
    intro r
    obtain ⟨d, h0, h1⟩ := exists_pinned_blocks (ρ r) (nativeA2Roots r) (hρ r)
    refine ⟨d, h0.trans ?_, h1.trans ?_⟩ <;>
      congr 1 <;> simp [nativeA2Roots, nativeWeights, kacE7_extRoot] <;> abel
  choose d hd using hp
  refine ⟨ρ, d, hρ, hd, ?_⟩
  intro r s hrs A B
  change Commute (ρ r (conjDiag3 (d r) A)) (ρ s (conjDiag3 (d s) B))
  exact nativeFrames_commute ρ hρ hrs _ _

end CFSG.LieType.Chevalley.E7Three.Frames
