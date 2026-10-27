module

public import CFSG.LieType.SeitzGeneration.HeisLinearFourier
public import CFSG.LieType.SeitzGeneration.NonabLift

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

theorem heisGen_conj_mul {F : Type*} [Field F] {p : ℕ} (P : GL (Fin p) F)
    (a b : Matrix (Fin p) (Fin p) F) :
    ((P : Matrix (Fin p) (Fin p) F) * a * ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)) *
      ((P : Matrix (Fin p) (Fin p) F) * b * ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)) =
      (P : Matrix (Fin p) (Fin p) F) * (a * b) *
        ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

theorem heisGen_eq_conj_of_inv_conj {F : Type*} [Field F] {p : ℕ} (P : GL (Fin p) F)
    {a b : Matrix (Fin p) (Fin p) F}
    (h : ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * a *
      (P : Matrix (Fin p) (Fin p) F) = b) :
    a = (P : Matrix (Fin p) (Fin p) F) * b *
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  subst h
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]

theorem heisGen_diag_comm {F : Type*} [Field F] {p : ℕ} (s t : Fin p → F) :
    Matrix.diagonal s * Matrix.diagonal t = Matrix.diagonal t * Matrix.diagonal s := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem heisGen_conjUnit_conjUnit_inv {F : Type*} [Field F] {p : ℕ} (P : GL (Fin p) F)
    (g : SpecialLinearGroup (Fin p) F) : conjUnit P (conjUnit P⁻¹ g) = g := by
  apply Subtype.ext
  simp only [conjUnit_coe, Matrix.mul_assoc, inv_inv, Units.mul_inv, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem heisGen_comm_shift {F : Type*} [Field F] {p : ℕ} [NeZero p] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {g : Matrix (Fin p) (Fin p) F} {t : Fin p → F}
    (hg : g * heisFourierMat ζ = heisFourierMat ζ * Matrix.diagonal t) :
    g * heisShiftMat F p = heisShiftMat F p * g := by
  have hU : IsUnit (heisFourierMat ζ : Matrix (Fin p) (Fin p) F) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_heisFourierMat_ne_zero hζ))
  have hS := heisShiftMat_mul_heisFourierMat (F := F) hζ.pow_eq_one
  have hD := heisGen_diag_comm (F := F) t (fun j : Fin p => ζ ^ (j : ℕ))
  apply hU.mul_right_cancel
  calc g * heisShiftMat F p * heisFourierMat ζ
      = g * (heisShiftMat F p * heisFourierMat ζ) := by rw [Matrix.mul_assoc]
    _ = g * (heisFourierMat ζ * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ))) := by
        rw [hS]
    _ = (g * heisFourierMat ζ) * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ)) := by
        rw [Matrix.mul_assoc]
    _ = (heisFourierMat ζ * Matrix.diagonal t) *
          Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ)) := by
        rw [hg]
    _ = heisFourierMat ζ *
          (Matrix.diagonal t * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ))) := by
        rw [Matrix.mul_assoc]
    _ = heisFourierMat ζ *
          (Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ)) * Matrix.diagonal t) := by
        rw [hD]
    _ = (heisFourierMat ζ * Matrix.diagonal (fun j : Fin p => ζ ^ (j : ℕ))) *
          Matrix.diagonal t := by
        rw [Matrix.mul_assoc]
    _ = (heisShiftMat F p * heisFourierMat ζ) * Matrix.diagonal t := by
        rw [hS]
    _ = heisShiftMat F p * (heisFourierMat ζ * Matrix.diagonal t) := by
        rw [Matrix.mul_assoc]
    _ = heisShiftMat F p * (g * heisFourierMat ζ) := by
        rw [hg]
    _ = heisShiftMat F p * g * heisFourierMat ζ := by
        rw [Matrix.mul_assoc]

theorem closure_centralizers_psl_of_heisenberg_p {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hG : TorusFourierGen F p)
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin p) F)}
    {x y : SpecialLinearGroup (Fin p) F} (hxE : toPSL x ∈ E) (hyE : toPSL y ∈ E)
    (hxZ : x ∉ Subgroup.center (SpecialLinearGroup (Fin p) F))
    (hyZ : y ∉ Subgroup.center (SpecialLinearGroup (Fin p) F))
    {P : GL (Fin p) F} {ω ξ : F} (hω : IsPrimitiveRoot ω p) (hξ : ξ ^ p = 1)
    (hy : ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (y : Matrix (Fin p) (Fin p) F) *
        (P : Matrix (Fin p) (Fin p) F) = ξ • heisDiagMat ω)
    (hx : ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (x : Matrix (Fin p) (Fin p) F) *
        (P : Matrix (Fin p) (Fin p) F) = heisShiftMat F p) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin p) F |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set C := Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin p) F |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} with hC
  set K : Subgroup (SpecialLinearGroup (Fin p) F) := C.comap toPSL with hK
  have hyne : toPSL y ≠ 1 := fun h => hyZ (mem_center_iff_toPSL_eq_one.2 h)
  have hxne : toPSL x ≠ 1 := fun h => hxZ (mem_center_iff_toPSL_eq_one.2 h)
  have hYm := heisGen_eq_conj_of_inv_conj P hy
  have hXm := heisGen_eq_conj_of_inv_conj P hx
  have hdiag : ∀ g : SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = Matrix.diagonal t) →
        conjUnit P g ∈ K := by
    rintro g ⟨t, ht⟩
    have hcomm : (g : Matrix (Fin p) (Fin p) F) * (ξ • heisDiagMat ω) =
        (ξ • heisDiagMat ω) * (g : Matrix (Fin p) (Fin p) F) := by
      rw [ht, heisDiagMat, ← Matrix.diagonal_smul]
      exact heisGen_diag_comm _ _
    show toPSL (conjUnit P g) ∈ C
    refine Subgroup.subset_closure ⟨toPSL y, hyE, hyne, ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, conjUnit_coe]
    rw [hYm, heisGen_conj_mul, heisGen_conj_mul, hcomm]
  have hfour : ∀ g : SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) * heisFourierMat ω =
        heisFourierMat ω * Matrix.diagonal t) → conjUnit P g ∈ K := by
    rintro g ⟨t, ht⟩
    show toPSL (conjUnit P g) ∈ C
    refine Subgroup.subset_closure ⟨toPSL x, hxE, hxne, ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, conjUnit_coe]
    rw [hXm, heisGen_conj_mul, heisGen_conj_mul, heisGen_comm_shift hω ht]
  have htop : K.comap (conjUnit P) = ⊤ :=
    hG ω hω (K.comap (conjUnit P)) (fun g hg => Subgroup.mem_comap.2 (hdiag g hg))
      (fun g hg => Subgroup.mem_comap.2 (hfour g hg))
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have h1 : conjUnit P⁻¹ g ∈ K.comap (conjUnit P) := htop ▸ Subgroup.mem_top _
    rwa [Subgroup.mem_comap, heisGen_conjUnit_conjUnit_inv] at h1
  rw [eq_top_iff]
  intro k _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ k
  have : g ∈ K := hKtop ▸ Subgroup.mem_top g
  exact this

end CFSG.LieType.SeitzGeneration

end
