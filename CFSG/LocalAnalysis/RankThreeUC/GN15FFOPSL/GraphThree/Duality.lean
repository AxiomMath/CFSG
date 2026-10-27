module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.GraphThree.Frobenius
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open scoped MatrixGroups Matrix

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.K1
  CFSG.QuasithinUnique.Setup.X7a

theorem nonempty_equiv_dual_of_graph {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ f) {U : Type} [AddCommGroup U]
    [Module (ZMod 2) U] [Finite U] (ρ : Representation (ZMod 2) SL(3, F) U)
    (hirr : ρ.IsIrreducible) (b : U ≃ₗ[ZMod 2] U) (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hb : ∀ x u, b (ρ x u) = ρ (CFSG.QuasithinUnique.K1.stdAut A σ 1 x) (b u)) :
    Nonempty (ρ.Equiv ρ.dual) := by
  obtain ⟨j, hσ⟩ := exists_frobPow_eq σ
  let α : SL(3, F) →* SL(3, F) :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A).toMonoidHom.comp
      ((CFSG.QuasithinUnique.Setup.X7a.tauSL F).comp
        (CFSG.QuasithinUnique.Setup.X7a.frobPow F j))
  have hα : ∀ x : SL(3, F), CFSG.QuasithinUnique.K1.stdAut A σ 1 x = α x :=
    fun x => stdAut_one_apply_eq A σ hσ x
  have hbα : ∀ x u, b (ρ x u) = ρ (α x) (b u) := by
    intro x u
    rw [← hα x]
    exact hb x u
  let e₀ : ρ.Equiv (ρ.comp α) :=
    Representation.Equiv.mk b (fun x => by
      refine LinearMap.ext fun u => ?_
      exact hbα x u)
  obtain ⟨e₁⟩ := (CFSG.QuasithinUnique.Setup.X7a.graphFieldTwistsDual f F hf hF U ρ hirr A j).2
  exact ⟨e₀.trans e₁⟩

theorem ne_refl_of_graph {F : Type} [Field F] [CharP F 2] {U : Type} [AddCommGroup U]
    [Module (ZMod 2) U] (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F) (b : U ≃ₗ[ZMod 2] U)
    (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hb : ∀ x u, b (ρ x u) = ρ (CFSG.QuasithinUnique.K1.stdAut A σ 1 x) (b u)) :
    b ≠ LinearEquiv.refl (ZMod 2) U := by
  intro hb1
  have hfix : ∀ {i j : Fin 3} (hij : i < j) (t : F),
      CFSG.QuasithinUnique.K1.stdAut A σ 1
          (Matrix.SpecialLinearGroup.transvection hij.ne t) =
        Matrix.SpecialLinearGroup.transvection hij.ne t := by
    intro i j hij t
    set x : SL(3, F) := Matrix.SpecialLinearGroup.transvection hij.ne t with hx
    have hrepr : ρ (CFSG.QuasithinUnique.K1.stdAut A σ 1 x) = ρ x := by
      refine DFunLike.ext _ _ fun u => ?_
      have h := hb x u
      rw [hb1] at h
      exact h.symm
    have hmem : CFSG.QuasithinUnique.K1.stdAut A σ 1 x * x⁻¹ ∈ scalars 3 F := by
      apply hker
      rw [map_mul, hrepr, ← map_mul, mul_inv_cancel, map_one]
    have hproj : proj 3 F (CFSG.QuasithinUnique.K1.stdAut A σ 1 x) = proj 3 F x := by
      have hq : proj 3 F (CFSG.QuasithinUnique.K1.stdAut A σ 1 x * x⁻¹) = 1 := by
        rw [proj_eq_one_iff]
        exact hmem
      rw [map_mul, map_inv] at hq
      calc proj 3 F (CFSG.QuasithinUnique.K1.stdAut A σ 1 x)
          = proj 3 F (CFSG.QuasithinUnique.K1.stdAut A σ 1 x) * (proj 3 F x)⁻¹ *
              proj 3 F x := by group
        _ = 1 * proj 3 F x := by rw [hq]
        _ = proj 3 F x := one_mul _
    have hxsq : x * x = 1 := by
      rw [hx]
      exact transvection_mul_self_of_charTwo hij.ne t
    have hsq : CFSG.QuasithinUnique.K1.stdAut A σ 1 x *
        CFSG.QuasithinUnique.K1.stdAut A σ 1 x = 1 := by
      rw [← map_mul, hxsq, map_one]
    exact CFSG.QuasithinUnique.K1.eq_of_proj_eq_of_mul_self_eq_one (n := 3) (by norm_num)
      hsq hxsq hproj
  exact CFSG.QuasithinUnique.K1.false_of_fixes_one (n := 3) (by norm_num) A σ hfix

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
