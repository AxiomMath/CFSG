module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.Cube
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Transport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (monomGL)
open scoped MatrixGroups

variable {F : Type} [Field F]

structure HeisHyp (σ : F ≃+* F) (lam ω : Fˣ) : Prop where
  ord : orderOf σ = 3
  ω3 : ω ^ 3 = 1
  fixl : σ (lam : F) = lam
  fixω : σ (ω : F) = ω

theorem HeisHyp.pow3 {σ : F ≃+* F} {lam ω : Fˣ} (h : HeisHyp σ lam ω) : σ ^ 3 = 1 :=
  h.ord ▸ pow_orderOf_eq_one σ

@[expose] def hyperFix (σ : F ≃+* F) (lam ω : Fˣ) : Set (projectiveSL 3 F) :=
  {x | ∃ H : Subgroup (MulAut (projectiveSL 3 F)), H ≤ heisCube σ lam ω ∧
    H.relIndex (heisCube σ lam ω) = 3 ∧ ∀ b ∈ H, b x = x}

theorem modelHyperGen_iff (σ : F ≃+* F) (lam ω : Fˣ) :
    ModelHyperGen 3 (heisCube σ lam ω) ↔ Subgroup.closure (hyperFix σ lam ω) = ⊤ := Iff.rfl

section Orbit

variable [Finite F] {σ : F ≃+* F} {lam ω : Fˣ}

theorem mem_hyperFix_of_orbit (h : HeisHyp σ lam ω) {x : projectiveSL 3 F}
    (horb : (MulAction.orbit (heisCube σ lam ω) x).ncard ≤ 3) : x ∈ hyperFix σ lam ω := by
  have : Finite (MulAut (projectiveSL 3 F)) := MulEquiv.finite_left
  obtain ⟨s, hs, hcard⟩ := card_heisCube h.ord h.ω3 h.fixl h.fixω
  obtain ⟨H, hHB, hHi, hHx⟩ :=
    CFSG.HardMathSupport.Foote.ModuleExclusions.exists_hyperplane_of_orbit_le _ hs hcard x horb
  exact ⟨H, hHB, hHi, fun b hb => hHx b hb⟩

theorem smul_eq_apply (b : MulAut (projectiveSL 3 F)) (x : projectiveSL 3 F) : b • x = b x := rfl

theorem mem_hyperFix_of_fS_cD (h : HeisHyp σ lam ω) {x : projectiveSL 3 F} (hf : fS σ x = x)
    (hd : cD ω x = x) : x ∈ hyperFix σ lam ω := by
  refine mem_hyperFix_of_orbit h (ncard_orbit_le_three _ x (cX lam) (cX_pow_three lam) ?_)
  intro b hb
  obtain ⟨i, j, k, rfl⟩ := exists_of_mem_heisCube h.pow3 h.ω3 h.fixl h.fixω hb
  refine ⟨k, ?_⟩
  have hc : Commute (fS σ ^ i * cD ω ^ j) (cX lam ^ k) :=
    (((commute_fS_cX h.fixl).pow_left i).pow_right k).mul_left
      (((commute_cD_cX h.ω3 lam).pow_left j).pow_right k)
  rw [hc.eq, mul_smul, mul_smul, pow_smul_eq_self (g := cD ω) hd j,
    pow_smul_eq_self (g := fS σ) hf i]

theorem mem_hyperFix_of_fS_cX (h : HeisHyp σ lam ω) {x : projectiveSL 3 F} (hf : fS σ x = x)
    (hx : cX lam x = x) : x ∈ hyperFix σ lam ω := by
  refine mem_hyperFix_of_orbit h (ncard_orbit_le_three _ x (cD ω) (cD_pow_three h.ω3) ?_)
  intro b hb
  obtain ⟨i, j, k, rfl⟩ := exists_of_mem_heisCube h.pow3 h.ω3 h.fixl h.fixω hb
  refine ⟨j, ?_⟩
  have hc : fS σ ^ i * cD ω ^ j * cX lam ^ k = cD ω ^ j * (fS σ ^ i * cX lam ^ k) := by
    rw [(((commute_fS_cD h.fixω).pow_left i).pow_right j).eq, mul_assoc]
  rw [hc, mul_smul, mul_smul, pow_smul_eq_self (g := cX lam) hx k,
    pow_smul_eq_self (g := fS σ) hf i]

theorem mem_hyperFix_of_cD_fScX (h : HeisHyp σ lam ω) {x : projectiveSL 3 F} (hd : cD ω x = x)
    (hfx : (fS σ * cX lam) x = x) : x ∈ hyperFix σ lam ω := by
  refine mem_hyperFix_of_orbit h (ncard_orbit_le_three _ x (cX lam) (cX_pow_three lam) ?_)
  intro b hb
  obtain ⟨i, j, k, rfl⟩ := exists_of_mem_heisCube h.pow3 h.ω3 h.fixl h.fixω hb
  have hstep : ∀ m : ℕ, fS σ • (cX lam ^ m • x) = cX lam ^ (m + 2) • x := by
    intro m
    have hfs : fS σ = (fS σ * cX lam) * cX lam ^ 2 := by
      rw [mul_assoc, ← pow_succ', cX_pow_three, mul_one]
    have hcm : Commute (fS σ * cX lam) (cX lam ^ (m + 2)) :=
      ((commute_fS_cX h.fixl).mul_left (Commute.refl _)).pow_right _
    have e1 : fS σ • (cX lam ^ m • x) = (fS σ * cX lam) • (cX lam ^ (m + 2) • x) := by
      conv_lhs => rw [hfs]
      rw [mul_smul, ← mul_smul (cX lam ^ 2), ← pow_add, add_comm 2 m]
    have e2 : (fS σ * cX lam) • (cX lam ^ (m + 2) • x) = cX lam ^ (m + 2) • x := by
      rw [← mul_smul, hcm.eq, mul_smul, smul_eq_apply (fS σ * cX lam) x, hfx]
    rw [e1, e2]
  have hiter : ∀ n m : ℕ, fS σ ^ n • (cX lam ^ m • x) = cX lam ^ (m + 2 * n) • x := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih =>
      intro m
      rw [pow_succ', mul_smul, ih, hstep, show m + 2 * n + 2 = m + 2 * (n + 1) by ring]
  refine ⟨k + 2 * i, ?_⟩
  have hc : fS σ ^ i * cD ω ^ j * cX lam ^ k = fS σ ^ i * (cX lam ^ k * cD ω ^ j) := by
    rw [mul_assoc, (((commute_cD_cX h.ω3 lam).pow_left j).pow_right k).eq]
  rw [hc, mul_smul, mul_smul, pow_smul_eq_self (g := cD ω) hd j, hiter]

end Orbit

section Proj

theorem proj_eq_of_val_eq_smul {A B : SL(3, F)} {c : Fˣ} (hc : c ^ 3 = 1)
    (h : (B : Matrix (Fin 3) (Fin 3) F) = (c : F) • (A : Matrix (Fin 3) (Fin 3) F)) :
    proj 3 F B = proj 3 F A := by
  rw [proj_eq_proj_iff, mem_scalars]
  refine ⟨c⁻¹, by rw [inv_pow, hc, inv_one], ?_⟩
  have key : (A : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) ((c⁻¹ : Fˣ) : F) := by
    ext i j
    rw [h, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    have hc0 : (c : F) ≠ 0 := c.ne_zero
    rw [Units.val_inv_eq_inv_val, mul_comm (c : F), mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, key, ← Matrix.mul_assoc,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mul]

theorem fS_proj_eq_of_fixed (σ : F ≃+* F) (A : SL(3, F))
    (h : ∀ i j, σ ((A : Matrix (Fin 3) (Fin 3) F) i j) = (A : Matrix (Fin 3) (Fin 3) F) i j) :
    fS σ (proj 3 F A) = proj 3 F A := by
  change fieldAut 3 F σ (proj 3 F A) = _
  rw [fieldAut_proj]
  congr 1
  ext i j
  exact h i j

theorem Dω_eq (ω : Fˣ) :
    Dω ω = CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL ![1, ω, ω ^ 2] := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dω, CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL,
      CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL]

theorem cD_proj_diag [Finite F] (ω : Fˣ) (A : SL(3, F))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    cD ω (proj 3 F A) = proj 3 F A := by
  change conjAut 3 F (Dω ω) (proj 3 F A) = _
  rw [Dω_eq]
  exact CFSG.HardMathSupport.Foote.ModuleExclusions.conjAut_diagGL_proj_diag _ A hA

end Proj

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis
