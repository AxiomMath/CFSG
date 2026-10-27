module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open Matrix CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped MatrixGroups

theorem card_le_three_of_faithful_plane {K : Type} [Field K] [Finite K] [CharP K 2]
    (hP3 : ∀ d : K, d ^ 3 = 1 → d = 1) {X : Type} [AddCommGroup X] [Module K X]
    (hX : Module.finrank K X = 2) {E : Type} [Group E] (hE3 : ∀ y : E, y ^ 3 = 1)
    (hcomm : ∀ a b : E, a * b = b * a) (σ : E →* Module.End K X) (hσ : Function.Injective σ) :
    Nat.card E ≤ 3 := by
  classical
  haveI : Module.Finite K X := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) K X := Module.finBasisOfFinrankEq K X hX
  let M : Module.End K X ≃ₐ[K] Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrixAlgEquiv b
  have hdet : ∀ y : E, (M (σ y)).det = 1 := by
    intro y
    apply hP3
    rw [← Matrix.det_pow, ← map_pow, ← map_pow, hE3 y, map_one, map_one, Matrix.det_one]
  let Φ : E →* SL(2, K) :=
    { toFun := fun y => ⟨M (σ y), hdet y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show M (σ (x * y)) = M (σ x) * M (σ y)
        rw [map_mul, map_mul] }
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have h1 : M (σ x) = M (σ y) := congrArg Subtype.val hxy
    exact hσ (M.injective h1)
  have hcommA : IsMulCommutative Φ.range := by
    refine ⟨⟨fun u v => ?_⟩⟩
    obtain ⟨u, x, rfl⟩ := u
    obtain ⟨v, y, rfl⟩ := v
    apply Subtype.ext
    show Φ x * Φ y = Φ y * Φ x
    rw [← map_mul, ← map_mul, hcomm]
  have hA3 : ∀ x ∈ Φ.range, x ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, hE3 y, map_one]
  have hle := SL2Char2.sl2_card_le_three Φ.range hcommA hA3
  have hcard : Nat.card E = Nat.card Φ.range :=
    Nat.card_congr (Equiv.ofInjective Φ hΦinj)
  rw [hcard]
  exact hle

end CFSG.LocalAnalysis.GLTheoremA.HDesc
