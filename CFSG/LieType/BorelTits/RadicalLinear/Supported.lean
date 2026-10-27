module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalStd

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix CFSG.StandardType.GGOppRad

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem det_eq_one_of_apply_eq_one_of_notMem {ℓ : ι → ℕ} {T : Finset (ι × ι)}
    (hT : ∀ p ∈ T, ℓ p.1 < ℓ p.2) {M : Matrix ι ι K}
    (hM : ∀ c a, (c, a) ∉ T → M c a = (1 : Matrix ι ι K) c a) : M.det = 1 := by
  have hblock : M.BlockTriangular ℓ := by
    intro i j hij
    have hnot : (i, j) ∉ T := fun h => absurd (hT _ h) (not_lt.mpr hij.le)
    have hne : i ≠ j := fun h => (ne_of_lt hij) (congrArg ℓ h.symm)
    rw [hM i j hnot, Matrix.one_apply, if_neg hne]
  rw [hblock.det]
  refine Finset.prod_eq_one fun y _ => ?_
  have hdiag : M.toSquareBlock ℓ y = 1 := by
    ext i j
    have hnot : (i.1, j.1) ∉ T := fun h => (ne_of_lt (hT _ h)) (i.2.trans j.2.symm)
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hM i.1 j.1 hnot, Matrix.one_apply,
      Matrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (congrArg Subtype.val hij)]
    · rw [if_neg hij, if_neg fun h => hij (Subtype.ext h)]
  rw [hdiag, Matrix.det_one]

private noncomputable def supportedMat (T : Finset (ι × ι)) (x : ↥T → K) : Matrix ι ι K :=
  fun c a => if h : (c, a) ∈ T then x ⟨(c, a), h⟩ else (1 : Matrix ι ι K) c a

private theorem supportedMat_det {ℓ : ι → ℕ} {T : Finset (ι × ι)}
    (hT : ∀ p ∈ T, ℓ p.1 < ℓ p.2) (x : ↥T → K) : (supportedMat T x).det = 1 :=
  det_eq_one_of_apply_eq_one_of_notMem hT fun _ _ h => dif_neg h

private noncomputable def supportedEquiv (ℓ : ι → ℕ) (T : Finset (ι × ι))
    (hT : ∀ p ∈ T, ℓ p.1 < ℓ p.2) :
    {g : SpecialLinearGroup ι K //
      ∀ c a, (c, a) ∉ T → (g : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a} ≃ (↥T → K) where
  toFun g p := (g.1 : Matrix ι ι K) p.1.1 p.1.2
  invFun x := ⟨⟨supportedMat T x, supportedMat_det hT x⟩, fun _ _ h => dif_neg h⟩
  left_inv g := by
    obtain ⟨g, hg⟩ := g
    refine Subtype.ext (Subtype.ext ?_)
    ext c a
    by_cases h : (c, a) ∈ T
    · simp [supportedMat, h]
    · simp [supportedMat, h, hg c a h]
  right_inv x := by
    funext p
    obtain ⟨⟨c, a⟩, h⟩ := p
    simp [supportedMat, h]

theorem card_supported [Finite K] (ℓ : ι → ℕ) (T : Finset (ι × ι))
    (hT : ∀ p ∈ T, ℓ p.1 < ℓ p.2) :
    Nat.card {g : SpecialLinearGroup ι K //
        ∀ c a, (c, a) ∉ T → (g : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a} =
      Nat.card K ^ T.card := by
  have hcard : Nat.card (↥T → K) = Nat.card K ^ T.card := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ↥T), Fintype.card_coe]
  rw [Nat.card_congr (supportedEquiv ℓ T hT), hcard]

theorem card_stdU [Finite K] (ℓ : ι → ℕ) :
    Nat.card (stdU (K := K) ℓ) =
      Nat.card K ^ (Finset.univ.filter fun p : ι × ι => ℓ p.1 < ℓ p.2).card := by
  let T := Finset.univ.filter fun p : ι × ι => ℓ p.1 < ℓ p.2
  have hT : ∀ p ∈ T, ℓ p.1 < ℓ p.2 := by
    intro p hp
    simpa [T] using hp
  have e : (stdU (K := K) ℓ) ≃
      {g : SpecialLinearGroup ι K //
        ∀ c a, (c, a) ∉ T → (g : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a} :=
    Equiv.subtypeEquivRight fun g => by
      rw [mem_stdU_iff]
      simp [T]
  exact (Nat.card_congr e).trans (card_supported ℓ T hT)

end CFSG.LieType.BorelTits.RadicalLinear
