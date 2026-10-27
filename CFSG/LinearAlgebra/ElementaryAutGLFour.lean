module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenGL
public import CFSG.GH74.QTGen4.GL4.Embed

public section

namespace CFSG.LinearAlgebra.ElementaryAutGLFour

open scoped IsMulCommutative

theorem exists_hom_glFour_ker_le {p : ℕ} [Fact p.Prime] {V : Type*} [Group V] [Finite V]
    [IsMulCommutative V] (hpow : ∀ v : V, v ^ p = 1) (hcard : Nat.card V ≤ p ^ 4)
    {Y : Type*} [Group Y] (ρ : Y →* MulAut V) :
    ∃ ρ' : Y →* GL (Fin 4) (ZMod p), ρ'.ker ≤ ρ.ker := by
  letI : CFSG.IsElementaryAbelian p V :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  obtain ⟨ψ, hψ⟩ := CFSG.AGLEmbedding.ThompsonGen.exists_hom_gl (p := p) ρ
  haveI : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
  let d := Module.finrank (ZMod p) (Additive V)
  have hd : d ≤ 4 := by
    have h1 : Nat.card (Additive V) = p ^ d := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V), Nat.card_zmod]
    have h2 : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
    rw [h2] at h1
    rw [h1] at hcard
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard
  let e : Fin 4 ≃ Fin d ⊕ Fin (4 - d) :=
    CFSG.GH74.QTGen4.splitFour (by omega : d + (4 - d) = 4)
  refine ⟨(CFSG.GH74.QTGen4.blockGL (R := ZMod p) e).comp ψ, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ (CFSG.GH74.QTGen4.blockGL_injective e)]
  exact hψ

end CFSG.LinearAlgebra.ElementaryAutGLFour
