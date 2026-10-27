module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.GraphOdd
public import CFSG.LieType.SpecialLinear.Stage.ChainEven

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Matrix Module Representation
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LieType.SpecialLinear
open CFSG.Quasithin.SmithCurtis
open scoped MonoidAlgebra TensorProduct

theorem graph_even_false (j : ℕ) {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : 4 ≤ Fintype.card K)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (2 * j + 6)) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ g, ρ g ≠ 1)
    (D : Subgroup (W ≃ₗ[ZMod 2] W)) (hDel : CFSG.IsElementaryAbelian 2 ↥D)
    (hquad : ∀ a ∈ D, ∀ b ∈ D, ∀ w, b (a w - w) = a w - w)
    (hcomm : ∀ d ∈ D, ∀ f : W →ₗ[ZMod 2] W, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) →
      (d : W →ₗ[ZMod 2] W) ∘ₗ f = f ∘ₗ (d : W →ₗ[ZMod 2] W))
    (hcompat : ∀ d ∈ D, ∃ B : GL (Fin (2 * j + 6)) K, IsUpperGL B ∧
      ∃ (τ : K ≃+* K) (ε : ℕ), ∀ g w,
        d (ρ g w) = ρ (borelStd (2 * j + 6) K B τ ε g) (d w))
    (hgraph : ∃ d ∈ D, ∃ B : GL (Fin (2 * j + 6)) K, IsUpperGL B ∧ ∃ τ : K ≃+* K, ∀ g w,
      d (ρ g w) = ρ (borelStd (2 * j + 6) K B τ 1 g) (d w))
    (hered : ∀ Z : Submodule (ZMod 2) W,
      (∀ d : ↥D, ∀ z ∈ Z, (d : W ≃ₗ[ZMod 2] W) z ∈ Z) → IsOffenderOn (tautRep D) ⊤ Z) :
    False := by
  classical
  have hirr' := hirr
  have hDfin : Finite ↥D := Subtype.finite
  have hDel' := hDel
  let E := End (ZMod 2)[Matrix.SpecialLinearGroup (Fin (2 * j + 6)) K] ρ.asModule
  let k := AlgebraicClosure E
  have hAlgebra : Algebra (ZMod 2) E := ZMod.algebra E 2
  have hTower := IsScalarTower.of_algebraMap_smul (R := ZMod 2) (A := E) (M := ρ.asModule)
    (fun a x => by
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
      · rw [map_zero, zero_smul, zero_smul]
      · rw [map_one, one_smul, one_smul])
  have hKalg : Algebra K k :=
    (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
      (K := E) (F₀ := K) (p := 2)).some.toAlgebra
  have hkchar : CharP k 2 :=
    charP_of_injective_algebraMap (algebraMap E k).injective 2
  have hD2W : ∀ d ∈ D, d * d = 1 := by
    intro d hd
    have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := D) d hd
    simpa [pow_two] using h
  obtain ⟨y, χ, J, ht, hJ⟩ := top_exists_type (n := 2 * j + 5) ρ hne
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k
      (CFSG.endFieldRep ρ)) := top_isSimpleRep (n := 2 * j + 5) ρ
  exact CFSG.LieType.SpecialLinear.stage_even_false (j := j) (F := K) hK
    (E := E) (k := k) (D := ↥D) (X := ρ.asModule)
    (CFSG.endFieldRep ρ) hsimp ht hJ (topActor ρ D)
    (topActor_smul ρ D hcomm) (topActor_isPGroup D hD2W)
    (topActor_mul_self ρ D hD2W) (topActor_quadratic ρ D hquad)
    (topActor_compat ρ D hcompat) (topActor_graph ρ D hgraph)
    (topActor_isOffenderOn ρ D (tautRep D) (fun d w => rfl) hD2W hered)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL