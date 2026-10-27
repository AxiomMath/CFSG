module

public import CFSG.GH74.QTGen4.Recog.G23.HSL
public meta import CFSG.GH74.QTGen4.Recog.G23.HSL

public section

namespace CFSG.GH74.QTGen4.Recog.G23

theorem gap2_inv_exists : ∀ g : M2, g.det ≠ 0 → ∃ g' : M2, g * g' = 1 ∧ g' * g = 1 := by
  decide +kernel

theorem gap2_conj_exists : ∀ X Y : M2, X * X * X = 1 → Y * Y * Y = 1 →
    (Y * Y) * (X * X) * Y * (X * X) * (Y * Y) * X = 1 → X * Y * (X * Y) = -1 →
    ∃ g : M2, g.det ≠ 0 ∧ g * mx = X * g ∧ g * my = Y * g := by
  let conjFor : M2 → M2 → M2 := fun X Y =>
    match (X 0 0).val, (X 0 1).val, (X 1 0).val, (X 1 1).val,
        (Y 0 0).val, (Y 0 1).val, (Y 1 0).val, (Y 1 1).val with
    | 0, 1, 2, 2, 0, 2, 1, 2 => !![1, 1; 1, 2]
    | 0, 1, 2, 2, 1, 0, 1, 1 => !![1, 0; 1, 1]
    | 0, 1, 2, 2, 1, 2, 0, 1 => !![1, 2; 1, 0]
    | 0, 2, 1, 2, 0, 1, 2, 2 => !![1, 1; 2, 1]
    | 0, 2, 1, 2, 1, 0, 2, 1 => !![1, 0; 2, 2]
    | 0, 2, 1, 2, 1, 1, 0, 1 => !![1, 2; 2, 0]
    | 1, 0, 1, 1, 0, 1, 2, 2 => !![0, 1; 1, 1]
    | 1, 0, 1, 1, 1, 1, 0, 1 => !![0, 1; 1, 0]
    | 1, 0, 1, 1, 2, 1, 2, 0 => !![0, 1; 1, 2]
    | 1, 0, 2, 1, 0, 2, 1, 2 => !![0, 1; 2, 2]
    | 1, 0, 2, 1, 1, 2, 0, 1 => !![0, 1; 2, 0]
    | 1, 0, 2, 1, 2, 2, 1, 0 => !![0, 1; 2, 1]
    | 1, 1, 0, 1, 0, 2, 1, 2 => !![1, 2; 0, 1]
    | 1, 1, 0, 1, 1, 0, 1, 1 => !![1, 0; 0, 1]
    | 1, 1, 0, 1, 2, 2, 1, 0 => !![1, 1; 0, 1]
    | 1, 2, 0, 1, 0, 1, 2, 2 => !![1, 2; 0, 2]
    | 1, 2, 0, 1, 1, 0, 2, 1 => !![1, 0; 0, 2]
    | 1, 2, 0, 1, 2, 1, 2, 0 => !![1, 1; 0, 2]
    | 2, 1, 2, 0, 1, 0, 1, 1 => !![1, 0; 2, 1]
    | 2, 1, 2, 0, 1, 2, 0, 1 => !![1, 1; 2, 0]
    | 2, 1, 2, 0, 2, 2, 1, 0 => !![1, 2; 2, 2]
    | 2, 2, 1, 0, 1, 0, 2, 1 => !![1, 0; 1, 2]
    | 2, 2, 1, 0, 1, 1, 0, 1 => !![1, 1; 1, 0]
    | 2, 2, 1, 0, 2, 1, 2, 0 => !![1, 2; 1, 1]
    | _, _, _, _, _, _, _, _ => 1
  let mat : Fin 81 → M2 := fun n =>
    !![((n.val / 27 : ℕ) : ZMod 3), ((n.val / 9 % 3 : ℕ) : ZMod 3);
       ((n.val / 3 % 3 : ℕ) : ZMod 3), ((n.val % 3 : ℕ) : ZMod 3)]
  let code : M2 → Fin 81 := fun A =>
    ⟨(27 * (A 0 0).val + 9 * (A 0 1).val + 3 * (A 1 0).val + (A 1 1).val) % 81,
      Nat.mod_lt _ (by decide)⟩
  have reify : ∀ A : M2, mat (code A) = A := by
    dsimp only [mat, code]
    decide +kernel
  have checked : ∀ x : Fin 81,
      let X := mat x
      X * X * X = 1 → ∀ y : Fin 81,
        let Y := mat y
        Y * Y * Y = 1 →
        (Y * Y) * (X * X) * Y * (X * X) * (Y * Y) * X = 1 →
        X * Y * (X * Y) = -1 →
        (conjFor X Y).det ≠ 0 ∧
          (∀ i j : Fin 2, (conjFor X Y * mx) i j = (X * conjFor X Y) i j) ∧
          (∀ i j : Fin 2, (conjFor X Y * my) i j = (Y * conjFor X Y) i j) := by
    dsimp only [conjFor, mat]
    simp only [mx_eq, my_eq]
    decide +kernel
  intro X Y hX hY hrel hxy
  have checkedX := checked (code X)
  rw [reify X] at checkedX
  have checkedXY := checkedX hX (code Y)
  rw [reify Y] at checkedXY
  obtain ⟨hg, hx, hy⟩ := checkedXY hY hrel hxy
  refine ⟨conjFor X Y, hg, ?_, ?_⟩
  · funext i j
    exact hx i j
  · funext i j
    exact hy i j

theorem msig_mul_mx_mul_msig : msig * mx * msig = mxi := by rw [msig_eq, mx_eq, mxi_eq]; decide +kernel

theorem msig_mul_my_mul_msig : msig * my * msig = myi := by rw [msig_eq, my_eq, myi_eq]; decide +kernel

theorem gap2_det_pm : ∀ d : ZMod 3, d ≠ 0 → d = 1 ∨ d = -1 := by decide

theorem gap2_det_conj {g g' : M2} (h1 : g * g' = 1) (M : M2) :
    (g * M * g').det = M.det := by
  have hdd : g.det * g'.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc g.det * M.det * g'.det = M.det * (g.det * g'.det) := by ring
    _ = M.det := by rw [hdd, mul_one]

end CFSG.GH74.QTGen4.Recog.G23
