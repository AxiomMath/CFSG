module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.SL2Pair
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

section Closure

variable {G : Type*} [Group G] {X : Type} [Field X]

@[expose] def threeB_entryAut (δ : X ≃+* X) : MulAut (SL(2, X)) where
  toFun := Matrix.SpecialLinearGroup.map δ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map δ.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp
  right_inv A := by
    apply Subtype.ext
    ext i j
    simp
  map_mul' := map_mul (Matrix.SpecialLinearGroup.map δ.toRingHom)

theorem threeB_aut_pow_apply {H : Type*} [Group H] (ι : H →* G) (φ : MulAut H) (ψ : MulAut G)
    (h : ∀ A, ι (φ A) = ψ (ι A)) (n : ℕ) (A : H) : ι ((φ ^ n) A) = (ψ ^ n) (ι A) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply, h]

theorem threeB_range_le_closure [Finite X] (hX : ringChar X ≠ 2)
    (ι : SL(2, X) →* G) (hι : Function.Injective ι)
    (δ : X ≃+* X) (hδ : orderOf δ = 3) {F : Subfield X} (hF : ∀ x, x ∈ F ↔ δ x = x)
    (hF5 : 5 ≤ Nat.card F)
    (e : MulAut G) (he : e ^ 3 = 1) (b : G) (hb : (e * MulAut.conj b) ^ 3 = 1)
    (N₁ Nb : GL (Fin 2) X)
    (hN₁ : ∀ A, e (ι A) = ι (glConjSL N₁ (Matrix.SpecialLinearGroup.map δ.toRingHom A)))
    (hNb : ∀ A, b * ι A * b⁻¹ = ι (glConjSL Nb A))
    (hnsc : ¬ ∃ c : X, (Nb : Matrix (Fin 2) (Fin 2) X) = Matrix.scalar (Fin 2) c) :
    ι.range ≤ Subgroup.closure ({l | l ∈ ι.range ∧ e l = l} ∪
      {l | l ∈ ι.range ∧ (e * MulAut.conj b) l = l}) := by
  let θ₁ : MulAut SL(2, X) := (threeB_entryAut δ).trans (sl2Conj N₁)
  let β : MulAut SL(2, X) := sl2Conj Nb
  let θ₂ : MulAut SL(2, X) := θ₁ * β
  have hθ₁ι : ∀ A, ι (θ₁ A) = e (ι A) := fun A => (hN₁ A).symm
  have hβι : ∀ A, ι (β A) = MulAut.conj b (ι A) := fun A => by
    rw [MulAut.conj_apply]
    exact (hNb A).symm
  have hθ₂ι : ∀ A, ι (θ₂ A) = (e * MulAut.conj b) (ι A) := fun A => by
    show ι (θ₁ (β A)) = e (MulAut.conj b (ι A))
    rw [hθ₁ι, hβι]
  have h₁ : θ₁ ^ 3 = 1 := by
    refine MulEquiv.ext fun A => hι ?_
    rw [threeB_aut_pow_apply ι θ₁ e hθ₁ι 3 A, he]
    rfl
  have h₂ : θ₂ ^ 3 = 1 := by
    refine MulEquiv.ext fun A => hι ?_
    rw [threeB_aut_pow_apply ι θ₂ (e * MulAut.conj b) hθ₂ι 3 A, hb]
    rfl
  have hclos := sl2_closure_fixed_pair hX δ hδ hF hF5 θ₁ θ₂ β N₁ Nb
    (fun A => rfl) (fun A => rfl) rfl hnsc h₁ h₂
  have hr : ι.range = Subgroup.closure (ι '' ({A | θ₁ A = A} ∪ {A | θ₂ A = A})) := by
    rw [MonoidHom.range_eq_map, ← hclos, MonoidHom.map_closure]
  refine le_trans (le_of_eq hr) (Subgroup.closure_mono ?_)
  rintro _ ⟨A, hA, rfl⟩
  rcases hA with hA | hA
  · left
    exact ⟨⟨A, rfl⟩, by rw [← hθ₁ι A]; exact congrArg ι hA⟩
  · right
    exact ⟨⟨A, rfl⟩, by rw [← hθ₂ι A]; exact congrArg ι hA⟩

end Closure

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
