module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLinGeom
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Lin

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.StandardType CFSG.StandardType.LinearFieldFix

theorem card_gl_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    Nat.card (GL (Fin 2) k) = 6 := by
  haveI := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  rw [Matrix.card_GL_field, hk', Fin.prod_univ_two]
  norm_num

variable {K : Type} [Field K] [Finite K]

theorem fixAlt_l2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ p)
    {σ : K ≃+* K} (hσ : orderOf σ = p)
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))} (hf : Induced σ f) :
    FixAlt p (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ) f := by
  classical
  refine Or.inr fun E hE hEx => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hKok : SLOK 2 K := slOK_of_two_pow (m := p) (by omega) hK
  obtain ⟨-, hcard⟩ := card_fixedPoints_field (m := p) (by omega) hK σ
  have hk : Nat.card (fixF σ) = 2 := by
    rw [card_fixF, hcard, hσ, Nat.div_self hp.pos, pow_one]
  have hB : ∀ φ : E, ∃ B : GL (Fin 2) (fixF σ),
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K))
        (fun h h' => (h' : GL (Fin 2) K) =
          Matrix.GeneralLinearGroup.map (fixF σ).subtype B * h *
            (Matrix.GeneralLinearGroup.map (fixF σ).subtype B)⁻¹) (φ : MulAut _) := by
    intro φ
    obtain ⟨⟨A, -, hA⟩, hc⟩ := hEx φ φ.2
    obtain ⟨μ, B, hdesc⟩ := exists_descend_of_commute' (d := 2) le_rfl hKok hf hA hc
    have hBmap : Matrix.GeneralLinearGroup.map (fixF σ).subtype B =
        Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A := by
      apply Units.ext
      rw [hdesc, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    refine ⟨B, fun h h' hh' => hA h h' ?_⟩
    have hh'' : (h' : GL (Fin 2) K) = Matrix.GeneralLinearGroup.map (fixF σ).subtype B *
        (h : GL (Fin 2) K) * (Matrix.GeneralLinearGroup.map (fixF σ).subtype B)⁻¹ := hh'
    show (h' : GL (Fin 2) K) = A * (h : GL (Fin 2) K) * A⁻¹
    rw [hh'', hBmap]
    calc Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A * (h : GL (Fin 2) K) *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A)⁻¹
        = Matrix.GeneralLinearGroup.scalar (Fin 2) μ * (A * (h : GL (Fin 2) K) * A⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) μ)⁻¹ := by
          rw [mul_inv_rev]
          group
      _ = (A * (h : GL (Fin 2) K) * A⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) μ *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) μ)⁻¹ := by
          rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = A * (h : GL (Fin 2) K) * A⁻¹ := by group
  choose g hg using hB
  have hinj : Function.Injective g := by
    intro φ ψ hφψ
    apply Subtype.ext
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ) * (x : GL (Fin 2) K) *
        (Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ))⁻¹ ∈
          LargeEvenSLGroup (Fin 2) K := by
      rw [TypeA.mem_largeEvenSLGroup_iff]
      have hx : Matrix.GeneralLinearGroup.det (x : GL (Fin 2) K) = 1 := by
        apply Units.ext
        rw [Units.val_one]
        exact TypeA.mem_largeEvenSLGroup_iff.mp x.2
      have hdet : Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ) * (x : GL (Fin 2) K) *
            (Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ))⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hx]
        group
      change ((Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ) * (x : GL (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ))⁻¹) : Kˣ) : K) = 1
      rw [hdet]
      exact Units.val_one
    have h1 := hg φ x ⟨_, hmem⟩ rfl
    have h2 := hg ψ x ⟨_, hmem⟩ (by
      show Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ) * (x : GL (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map (fixF σ).subtype (g φ))⁻¹ =
        Matrix.GeneralLinearGroup.map (fixF σ).subtype (g ψ) * (x : GL (Fin 2) K) *
          (Matrix.GeneralLinearGroup.map (fixF σ).subtype (g ψ))⁻¹
      rw [hφψ])
    change (φ : MulAut _) (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) x) =
      (ψ : MulAut _) (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) x)
    rw [h1, h2]
  haveI : Finite E := Finite.of_injective g hinj
  have hle : Nat.card E ≤ 6 := by
    rw [← card_gl_two hk]
    exact Nat.card_le_card_of_injective g hinj
  have hpg : IsPGroup p E := fun φ => ⟨1, by
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, hE.2 φ φ.2, Subgroup.coe_one]⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hpg
  rw [hr] at hle ⊢
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · interval_cases r
    · rw [pow_zero]
      exact hp.one_lt.le
    · rw [pow_one]
  · exfalso
    have h9 : 3 ^ 2 ≤ p ^ r :=
      calc 3 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr2
    omega

end CFSG.LocalAnalysis.GLTheoremA.T156.Lin

end
