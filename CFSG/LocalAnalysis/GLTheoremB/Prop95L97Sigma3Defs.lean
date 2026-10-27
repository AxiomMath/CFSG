module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3

variable {𝔄 : Type*} [Group 𝔄]

structure IsSigma3Family (I : Finset (Subgroup 𝔄)) : Prop where
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  indep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  sigma3 : ∀ L ∈ I, Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))

@[expose] def conjBy (g : 𝔄) (L : Subgroup 𝔄) : Subgroup 𝔄 :=
  L.map (MulAut.conj g).toMonoidHom

theorem mem_conjBy {g x : 𝔄} {L : Subgroup 𝔄} : x ∈ conjBy g L ↔ g⁻¹ * x * g ∈ L := by
  unfold conjBy
  rw [Subgroup.mem_map_equiv]
  simp

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3
