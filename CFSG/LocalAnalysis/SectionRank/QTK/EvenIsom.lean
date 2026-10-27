module

public import CFSG.ClassicalGroups.Orthogonal.BasisCheck
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.SectionRank.QTK

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank

variable (K : Type) [Field K] [CharP K 2]

abbrev cast2 : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

abbrev castMat {ι : Type} (M : Matrix ι ι (ZMod 2)) : Matrix ι ι K := M.map (cast2 K)

variable {K} {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem castMat_mulVec (M : Matrix ι ι (ZMod 2)) (w : ι → ZMod 2) :
    castMat K M *ᵥ (cast2 K ∘ w) = cast2 K ∘ (M *ᵥ w) := by
  funext i
  exact (RingHom.map_mulVec (cast2 K) M w i).symm

omit [Fintype ι] in
theorem single_eq_cast (i : ι) :
    (Pi.single i 1 : ι → K) = cast2 K ∘ (Pi.single i 1 : ι → ZMod 2) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem isometry_castMat_of_basis (Q : QuadraticForm K (ι → K)) (Q₂ : (ι → ZMod 2) → ZMod 2)
    (hQ : ∀ w, Q (cast2 K ∘ w) = cast2 K (Q₂ w)) (M : Matrix ι ι (ZMod 2))
    (h1 : ∀ i, Q₂ (M *ᵥ Pi.single i 1) = Q₂ (Pi.single i 1))
    (h2 : ∀ i j, Q₂ (M *ᵥ (Pi.single i 1 + Pi.single j 1)) =
      Q₂ (Pi.single i 1 + Pi.single j 1)) (v : ι → K) :
    Q (castMat K M *ᵥ v) = Q v := by
  have hcol : ∀ i, castMat K M *ᵥ Pi.single i 1 = cast2 K ∘ (M *ᵥ Pi.single i 1) := by
    intro i
    rw [single_eq_cast (K := K), castMat_mulVec]
  have hsum : ∀ a b : ι → ZMod 2, cast2 K ∘ a + cast2 K ∘ b = cast2 K ∘ (a + b) := by
    intro a b
    funext j
    simp
  refine CFSG.ClassicalGroups.Orthogonal.quad_apply_eq_of_basis Q (mulVecLin (castMat K M)) ?_ ?_ v
  · intro i
    rw [mulVecLin_apply, hcol, hQ, single_eq_cast (K := K), hQ, h1]
  · intro i j
    simp only [polar, mulVecLin_apply, hcol]
    rw [single_eq_cast (K := K) i, single_eq_cast (K := K) j, hsum, hsum, hQ, hQ, hQ, hQ, hQ, hQ,
      ← mulVec_add, h2, h1, h1]

theorem statedQuadPlus_comp_cast {m : ℕ} (w : Fin m ⊕ Fin m → ZMod 2) :
    StatedQuadPlus m K (cast2 K ∘ w) = cast2 K (StatedQuadPlus m (ZMod 2) w) := by
  simp only [StatedQuadPlus, Function.comp_apply, map_sum, map_mul]

theorem statedQuadMinus_comp_cast {n : ℕ} (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 2) :
    StatedQuadMinus n K 1 1 (cast2 K ∘ w) = cast2 K (StatedQuadMinus n (ZMod 2) 1 1 w) := by
  simp only [StatedQuadMinus, Function.comp_apply, map_sum, map_mul, map_add, map_pow, map_one]

end CFSG.SectionRank.QTK
