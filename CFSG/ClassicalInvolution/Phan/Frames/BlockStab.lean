module

public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg Module Matrix

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem blockEmb_smul_single_of_not_mem {m k i : ℕ} (h : i + k ≤ m) (A : Su K p f k) {l : Fin m}
    (hl : ¬ (i ≤ l.val ∧ l.val < i + k)) :
    blockEmb K p f m k i h A • (Pi.single l 1 : Fin m → K) = Pi.single l 1 := by
  funext a
  rw [smul_def, coe_coe_blockEmb]
  by_cases ha : i ≤ a.val ∧ a.val < i + k
  · have hal : a ≠ l := fun h' => hl (h' ▸ ha)
    have hx : a = blockIdx i h ⟨a.val - i, by omega⟩ := Fin.ext (by simp only [blockIdx_val]; omega)
    rw [hx, blockMat_mulVec_blockIdx, Pi.single_eq_of_ne (hx ▸ hal)]
    have : (fun y : Fin k => (Pi.single l 1 : Fin m → K) (blockIdx i h y)) = 0 := by
      funext y
      have hyl : blockIdx i h y ≠ l := fun h' => hl (by
        rw [← h']; simp only [blockIdx_val]; have := y.isLt; omega)
      simp [Pi.single_eq_of_ne hyl]
    rw [this, Matrix.mulVec_zero]
    rfl
  · exact blockMat_mulVec_of_not_mem _ _ ha

theorem mem_range_blockEmb_of_smul_single {m k i : ℕ} (h : i + k ≤ m) (x : Su K p f m)
    (hx : ∀ l : Fin m, ¬ (i ≤ l.val ∧ l.val < i + k) → x • (Pi.single l 1 : Fin m → K) =
      Pi.single l 1) : x ∈ (blockEmb K p f m k i h).range := by
  set σ := unitaryInvolution K p f with hσdef
  set X : Matrix (Fin m) (Fin m) K := ((x : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) with hX
  have hXX : conjTr σ X * X = 1 := x.2.2
  have hcol : ∀ l : Fin m, ¬ (i ≤ l.val ∧ l.val < i + k) → ∀ a : Fin m,
      X a l = (1 : Matrix (Fin m) (Fin m) K) a l := by
    intro l hl a
    have := congrFun (hx l hl) a
    rw [smul_def, Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply] using this
  have hrow : ∀ l : Fin m, ¬ (i ≤ l.val ∧ l.val < i + k) → ∀ b : Fin m,
      X l b = (1 : Matrix (Fin m) (Fin m) K) l b := by
    intro l hl b
    have h1 : conjTr σ X *ᵥ (Pi.single l 1 : Fin m → K) = Pi.single l 1 := by
      have := congrArg (fun v => conjTr σ X *ᵥ v) (hx l hl)
      simp only [smul_def] at this
      rw [Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec] at this
      exact this.symm
    have h2 := congrFun h1 b
    rw [Matrix.mulVec_single_one] at h2
    have h3 : σ (X l b) = (Pi.single l 1 : Fin m → K) b := h2
    rw [Matrix.one_apply]
    by_cases hlb : l = b
    · subst hlb
      rw [ite_eq_left rfl]
      simpa using h3
    · rw [ite_eq_right hlb]
      have : (Pi.single l 1 : Fin m → K) b = 0 := Pi.single_eq_of_ne (Ne.symm hlb) _
      rw [this] at h3
      exact (map_eq_zero_iff σ σ.injective).mp h3
  set A : Matrix (Fin k) (Fin k) K := Matrix.of fun x y => X (blockIdx i h x) (blockIdx i h y)
    with hA
  have hXA : X = blockMat m i A := by
    ext a b
    rw [blockMat_apply]
    by_cases hab : (i ≤ a.val ∧ a.val < i + k) ∧ (i ≤ b.val ∧ b.val < i + k)
    · rw [dite_eq_left hab]
      simp only [hA, Matrix.of_apply]
      congr 2 <;> exact Fin.ext (by simp only [blockIdx_val]; omega)
    · rw [dite_eq_right hab]
      by_cases hb : i ≤ b.val ∧ b.val < i + k
      · exact hrow a (fun ha => hab ⟨ha, hb⟩) b
      · exact hcol b hb a
  have hdet : A.det = 1 := by
    rw [← det_blockMat h A, ← hXA]
    exact x.2.1
  have hAA : conjTr σ A * A = 1 := by
    refine blockMat_injective h ?_
    rw [blockMat_mul h, ← conjTr_blockMat, ← hXA, hXX, blockMat_one]
  have hiso : ∀ y z, herm σ (A *ᵥ y) (A *ᵥ z) = herm σ y z := fun y z => by
    rw [herm_mulVec, hAA, Matrix.one_mulVec]
  refine ⟨mkSU σ A hdet hiso, ?_⟩
  exact Subtype.ext (Units.ext hXA.symm)

theorem mem_range_blockEmb_iff {m k i : ℕ} (h : i + k ≤ m) (x : Su K p f m) :
    x ∈ (blockEmb K p f m k i h).range ↔
      ∀ l : Fin m, ¬ (i ≤ l.val ∧ l.val < i + k) →
        x • (Pi.single l 1 : Fin m → K) = Pi.single l 1 :=
  ⟨by
    rintro ⟨A, rfl⟩ l hl
    exact blockEmb_smul_single_of_not_mem h A hl,
    mem_range_blockEmb_of_smul_single h x⟩

end CFSG.ClassicalInvolution.Phan
