module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUb

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank StabU DiagU
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut (unitaryConjHom coe_unitaryConjHom)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_one_or_neg_one_of_unitary {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {c : K}
    (hAc : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = c • 1) :
    c = 1 ∨ c = -1 := by
  set Am := (A : Matrix (Fin 4) (Fin 4) K) with hAm
  set Ab := Am.map h.bar with hAb
  have hAt : Abᵀ * Am = 1 := hAu
  have h1 : Ab = c • Abᵀ := by
    calc Ab = (Abᵀ * Am) * Ab := by rw [hAt, Matrix.one_mul]
      _ = Abᵀ * (Am * Ab) := Matrix.mul_assoc _ _ _
      _ = c • Abᵀ := by rw [hAc, Matrix.mul_smul, Matrix.mul_one]
  have h2 : Abᵀ = c • Ab := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h1
    rw [h1, Matrix.transpose_zero, Matrix.zero_mul] at hAt
    exact zero_ne_one hAt
  have h3 : Am * Ab = (c * c) • (Am * Ab) := by
    conv_lhs => rw [h1, h2, smul_smul]
    rw [Matrix.mul_smul]
  rw [hAc, smul_smul] at h3
  have h4 := congrFun (congrFun h3 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
  have h5 : c * (c * c) = c * 1 := by rw [mul_one, ← mul_assoc]; exact h4.symm
  exact mul_self_eq_one_iff.mp (mul_left_cancel₀ hc0 h5)

theorem exists_lift_U4 (hp2 : p ≠ 2) (β : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (hβ : ∀ x, β (β x) = x) :
    ∃ (A : GL (Fin 4) K) (ψ : unitarySU p f K 4 →* unitarySU p f K 4),
      uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (ψ g)) ∧
      ((∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∨
        ((∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (A : Matrix (Fin 4) (Fin 4) K) *
            ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
          ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 ∨
            (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1))) := by
  classical
  have : Finite K := h.finite
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 4) (by norm_num) θ hθ hker β
  obtain ⟨hφ, hcomp⟩ := hinv hβ
  set ψ := unitaryConjHom A φ hA with hψdef
  have hcomp' : ∀ g : unitarySU p f K 4, ψ (ψ g) = g := fun g =>
    congrArg (fun F : unitarySU p f K 4 →* unitarySU p f K 4 => F g) hcomp
  refine ⟨A, ψ, hAu, fun g => (hlift g).symm, ?_⟩
  rcases hφ with hφ1 | hφb
  · left
    subst hφ1
    have hgl1 : ∀ Y : GL (Fin 4) K, glAut (RingEquiv.refl K) Y = Y := fun Y => by
      change glAut 1 Y = Y
      rw [map_one]
      rfl
    intro g
    rw [hψdef, coe_unitaryConjHom, hgl1, Units.val_mul, Units.val_mul]
  · right
    have hφb' : (φ : K → K) = h.bar := funext hφb
    have hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun g => by
      rw [hψdef, coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut, hφb']
    refine ⟨hψv, ?_⟩
    have hφφ : φ * φ = 1 := RingEquiv.ext fun c => by
      change φ (φ c) = c
      rw [hφb, hφb, h.bar_bar]
    have hglφ : ∀ Y : GL (Fin 4) K, glAut φ (glAut φ Y) = Y := fun Y => by
      have := congrArg (fun χ : MulAut (GL (Fin 4) K) => χ Y)
        (show glAut φ * glAut φ = 1 by rw [← map_mul, hφφ, map_one])
      exact this
    set Bm : GL (Fin 4) K := A * glAut φ A with hBm
    have hBv : (Bm : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar := by
      rw [hBm, Units.val_mul, coe_glAut, hφb']
    have hB1 : IsCU h Bm 1 := by
      refine ⟨mul_mem hAu (glAut_mem_uMat h φ hAu), fun g g' hg' => ?_⟩
      rw [MulAut.one_apply]
      congr 1
      have e1 := congrArg (fun Y : unitarySU p f K 4 => (Y : GL (Fin 4) K)) (hcomp' g)
      simp only [hψdef, coe_unitaryConjHom, map_mul, map_inv, hglφ] at e1
      apply Subtype.ext
      rw [hg', hBm]
      symm
      calc A * glAut φ A * (g : GL (Fin 4) K) * (A * glAut φ A)⁻¹ =
          A * (glAut φ A * (g : GL (Fin 4) K) * (glAut φ A)⁻¹) * A⁻¹ := by group
        _ = g := e1
    obtain ⟨c, hc⟩ := eq_smul_one_of_isCU_one h hp2 hB1
    rw [hBv] at hc
    rcases eq_one_or_neg_one_of_unitary h hAu hc with rfl | rfl
    · left
      rw [hc, one_smul]
    · right
      rw [hc, neg_smul, one_smul]

end CFSG.ComponentClassification.GSThmB.P211
