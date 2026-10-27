module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks

variable {k p m : ℕ}

theorem scale_mul_transl_mul_inv (i : Fin k) (r : (ZMod p)ˣ) (f : Fin k → ZMod p) :
    scale i r * transl f * (scale i r)⁻¹ =
      transl (fun j => if j = i then (r : ZMod p) * f j else f j) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Equiv.ext fun x => ?_
  obtain ⟨j, y⟩ := x
  by_cases h : j = i
  · simp [h, mul_add, Equiv.Perm.mul_apply]
  · simp [h, Equiv.Perm.mul_apply]

theorem swapB_mul_transl_mul_inv (i j : Fin k) (f : Fin k → ZMod p) :
    swapB i j * transl f * (swapB i j)⁻¹ = transl (f ∘ Equiv.swap i j) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Equiv.ext fun x => ?_
  obtain ⟨a, y⟩ := x
  simp [Equiv.Perm.mul_apply]

theorem blockPerm_mul_baseHom_mul_inv (π : Equiv.Perm (Fin k × ZMod p)) (f : Fin k → ZMod p)
    (g : Fin k → ZMod p) (h : π * transl f * π⁻¹ = transl g) :
    blockPerm (m := m) π * baseHom (Multiplicative.ofAdd f) * (blockPerm π)⁻¹ =
      baseHom (Multiplicative.ofAdd g) := by
  change blockPermHom (m := m) π * blockPermHom (m := m) (transl f) *
      (blockPermHom (m := m) π)⁻¹ = blockPermHom (m := m) (transl g)
  rw [← h, map_mul, map_mul, map_inv]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks
