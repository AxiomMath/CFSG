module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPairs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {m : ℕ} {K : Type} [Field K]

section Entries

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mul_single_one_apply (G : Matrix ι ι K) (a b x y : ι) :
    (G * Matrix.single a b (1 : K)) x y = if y = b then G x a else 0 := by
  by_cases hy : y = b
  · subst hy
    rw [if_pos rfl]
    simpa using Matrix.mul_single_apply_same (1 : K) a y x G
  · rw [if_neg hy]
    exact Matrix.mul_single_apply_of_ne (1 : K) a b x y hy G

theorem single_one_mul_apply (G : Matrix ι ι K) (a b x y : ι) :
    (Matrix.single a b (1 : K) * G) x y = if x = a then G b y else 0 := by
  by_cases hx : x = a
  · subst hx
    rw [if_pos rfl]
    simpa using Matrix.single_mul_apply_same (1 : K) x b y G
  · rw [if_neg hx]
    exact Matrix.single_mul_apply_of_ne (1 : K) a b x y hx G

end Entries

theorem entry_eq_of_commute_rpMat {G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    {a b : Fin m ⊕ Fin m} (h : G * rpMat K a b = rpMat K a b * G) (x y : Fin m ⊕ Fin m) :
    (if y = b then G x a else 0) - (if y = a.swap then G x b.swap else 0) =
      (if x = a then G b y else 0) - (if x = b.swap then G a.swap y else 0) := by
  have := congrFun (congrFun h x) y
  simp only [rpMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, mul_single_one_apply,
    single_one_mul_apply] at this
  exact this

theorem exists_coord_ne (hm : 2 ≤ m) (u x : Fin m ⊕ Fin m) :
    ∃ b : Fin m ⊕ Fin m, coordIdx u ≠ coordIdx b ∧ b.swap ≠ x := by
  obtain ⟨j, hj⟩ : ∃ j : Fin m, coordIdx u ≠ j := by
    by_cases h0 : coordIdx u = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, h0⟩
  by_cases hx : x = Sum.inr j
  · exact ⟨Sum.inr j, by simpa using hj, by rw [hx]; simp⟩
  · exact ⟨Sum.inl j, by simpa using hj, by simpa using Ne.symm hx⟩

theorem eq_smul_one_of_commute_rpMat (hm : 2 ≤ m)
    (G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (h : ∀ a b : Fin m ⊕ Fin m, coordIdx a ≠ coordIdx b → G * rpMat K a b = rpMat K a b * G) :
    ∃ c : K, G = c • 1 := by
  have hoff : ∀ x u : Fin m ⊕ Fin m, x ≠ u → G x u = 0 := by
    intro x u hxu
    obtain ⟨b, hb1, hb2⟩ := exists_coord_ne hm u x
    have hbu : b ≠ u.swap := fun hbu => hb1 (by rw [hbu, coordIdx_swap])
    have key := entry_eq_of_commute_rpMat (h u b hb1) x b
    rw [if_pos rfl, if_neg hbu, if_neg hxu, if_neg (Ne.symm hb2)] at key
    simpa using key
  have hdiag : ∀ a b : Fin m ⊕ Fin m, coordIdx a ≠ coordIdx b → G a a = G b b := by
    intro a b hab
    have hba : b ≠ a.swap := fun hba => hab (by rw [hba, coordIdx_swap])
    have hab' : a ≠ b.swap := fun hab' => hab (by rw [hab', coordIdx_swap])
    have key := entry_eq_of_commute_rpMat (h a b hab) a b
    rw [if_pos rfl, if_neg hba, if_pos rfl, if_neg hab'] at key
    simpa using key
  have hall : ∀ u v : Fin m ⊕ Fin m, G u u = G v v := by
    intro u v
    by_cases huv : coordIdx u = coordIdx v
    · obtain ⟨w, hw1, -⟩ := exists_coord_ne hm u u
      exact (hdiag u w hw1).trans (hdiag v w (by rw [← huv]; exact hw1)).symm
    · exact hdiag u v huv
  refine ⟨G (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩), Matrix.ext fun x y => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    simp [hall x (Sum.inl ⟨0, by omega⟩)]
  · simp [hoff x y hxy, Matrix.one_apply_ne hxy]

theorem rpMat_apply_self {a b : Fin m ⊕ Fin m} (h : coordIdx a ≠ coordIdx b) :
    rpMat K a b a b = 1 := by
  have h2 : b.swap ≠ a := fun e => h (by rw [← e, coordIdx_swap])
  simp [rpMat, Matrix.single_apply, h2]

theorem eq_of_rel_rpMat (hm : 2 ≤ m) (σ : K →+* K)
    (G H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (hHG : H * G = 1)
    (h : ∀ a b : Fin m ⊕ Fin m, coordIdx a ≠ coordIdx b → ∀ t : K,
      G * (1 + σ t • rpMat K a b) = (1 + t • rpMat K a b) * G) :
    (∀ t : K, σ t = t) ∧ ∃ c : K, G = c • 1 := by
  have hcomm : ∀ a b : Fin m ⊕ Fin m, coordIdx a ≠ coordIdx b →
      G * rpMat K a b = rpMat K a b * G := by
    intro a b hab
    have h1 := h a b hab 1
    simp only [map_one, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    exact add_left_cancel h1
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute_rpMat hm G hcomm
  refine ⟨fun t => ?_, c, hc⟩
  let a₀ : Fin m ⊕ Fin m := Sum.inl ⟨0, by omega⟩
  let b₀ : Fin m ⊕ Fin m := Sum.inl ⟨1, by omega⟩
  have hab : coordIdx a₀ ≠ coordIdx b₀ := by simp [a₀, b₀, Fin.ext_iff]
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    rw [hc, Matrix.mul_zero] at hHG
    have := congrFun (congrFun hHG a₀) a₀
    simp at this
  have h1 := h a₀ b₀ hab t
  rw [hc] at h1
  have h2 := congrFun (congrFun h1 a₀) b₀
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, rpMat_apply_self hab,
    smul_eq_mul, Matrix.one_apply_ne (show a₀ ≠ b₀ from fun e => hab (by rw [e]))] at h2
  have h3 : (σ t - t) * c = 0 := by linear_combination h2
  have h4 := (mul_eq_zero.1 h3).resolve_right hc0
  exact sub_eq_zero.1 h4

theorem eq_one_of_smul_isometry [CharP K 2] (hm : 1 ≤ m) {c : K}
    (h : ∀ v : Fin m ⊕ Fin m → K, CFSG.LieType.Universal.Spin.quadPlus m K (c • v) =
      CFSG.LieType.Universal.Spin.quadPlus m K v) : c = 1 := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let v : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i₀) 1 + Pi.single (Sum.inr i₀) 1
  have e1 : CFSG.LieType.Universal.Spin.quadPlus m K v = 1 := by
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply,
      Finset.sum_eq_single i₀ (fun i _ hi => by simp [v, Pi.single_apply, hi]) (by simp)]
    simp [v]
  have h1 := h v
  rw [QuadraticMap.map_smul, e1, smul_eq_mul, mul_one] at h1
  have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (c - 1) ^ 2 = 0 := by linear_combination h1 + (1 - c) * h2'
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
