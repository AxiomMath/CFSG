module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpTorus
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpFrame
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalance

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.ClassicalInvolution.Balance
open scoped Matrix MatrixGroups

variable {F : Type} [Field F] {X : Type} [Group X]

theorem commute_of_sq_commute {d w : X} (hodd : Odd (orderOf d)) (h : d * d * w = w * (d * d)) :
    d * w = w * d := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : d ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one d
  have h2 : (d * d) ^ (k + 1) = d := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, pow_succ, h1, one_mul]
  have hc : Commute ((d * d) ^ (k + 1)) w := Commute.pow_left h (k + 1)
  rw [h2] at hc
  exact hc

theorem reflM_mul_self (p r : F) :
    reflM p r * reflM p r = (p ^ 2 + r ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem mul_eq_conjSp (A : gsp 2 F) (y : StatedSp 2 F) :
    simMat A * mat 2 F y = mat 2 F (conjSp 2 F A y) * simMat A := by
  rw [mat_conjSp, Matrix.mul_assoc, simInv_mul, Matrix.mul_one]

theorem iLemma_std [Finite F] [Finite X] (hodd : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F)
    (ψ : StatedSp 2 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hnorm : ψ.range.Normal) {f : X}
    (hf : ∀ y, f * ψ y * f⁻¹ = ψ (xSw * y * xSw⁻¹)) {d : X}
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) :
    ∀ s : StatedSp 2 F, s * xSw = xSw * s → ∀ y,
      d * ψ (s * y * s⁻¹) * d⁻¹ = ψ s * (d * ψ y * d⁻¹) * (ψ s)⁻¹ := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hsub : CFSG.Open.IsSubnormal ψ.range ⊤ :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  have hcomm : ∀ s ∈ (Δsl (F := F)).range, d * ψ s = ψ s * d := by
    intro s hs
    have hQ := isComponentOf_range_Δsl h2 h4
    have hmain := isComponentOf_map_centralizer hker 1 f (MulAut.conj xSw)
      (fun y => by simpa using hf y) hQ
    have e : (MulAut.conj (1 : StatedSp 2 F)).toMonoidHom = MonoidHom.id _ := by
      ext
      simp
    rw [e, MonoidHom.comp_id] at hmain
    have hle := le_centralizerLayer_of_isComponentOf hsub hmain
    exact commute_of_mem_involutionOddCore_of_mem_centralizerLayer hd (hle ⟨s, hs, rfl⟩)
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear_lift_conj hodd h4 ψ hker hnorm d
  have hfix : ∀ s ∈ (Δsl (F := F)).range, conjSp 2 F A (fieldSp 2 F σ s) = s := by
    intro s hs
    have : Group.IsPerfect (Δsl (F := F)).range := ⟨(isQuasisimple_range_Δsl h4).1⟩
    have key := hom_eq_of_central_ker ψ hker
      (((conjSp 2 F A).toMonoidHom.comp (fieldSp 2 F σ).toMonoidHom).comp
        (Δsl (F := F)).range.subtype)
      (Δsl (F := F)).range.subtype (fun l => by
        have h1 := hAσ l
        have h2' : d * ψ l * d⁻¹ = ψ l := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hcomm l l.2
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
        rw [← h1, h2'])
    have h := MonoidHom.ext_iff.mp key ⟨s, hs⟩
    exact h
  have hΔ : ∀ h : SL(2, F), simMat A * (tens (h : Matrix (Fin 2) (Fin 2) F) 1).map σ =
      tens (h : Matrix (Fin 2) (Fin 2) F) 1 * simMat A := fun h => by
    have := mul_eq_of_conjSp_eq A σ (hfix _ ⟨h, rfl⟩)
    rwa [mat_Δsl] at this
  obtain ⟨hσ, P, hP⟩ := rigid_Δsl σ (simInv_mul A) hΔ
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hsim : (tens 1 P)ᵀ * gram F 2 * tens 1 P = (μ : F) • gram F 2 := by
    rw [← hP]
    exact hμ
  have hPP := transpose_mul_eq hsim
  have e1 : ∀ z, d * ψ z * d⁻¹ = ψ (conjSp 2 F A z) := fun z => by
    rw [hAσ z, fieldSp_eq_self hσ]
  rcases classify_orthogonal μ.ne_zero hPP with ⟨p, r, hB⟩ | ⟨p, r, hB, hpr⟩
  · intro s hs y
    have hAmat : simMat A = p • 1 + r • mat 2 F xSw := by
      rw [hP, hB, tens_add_right, tens_smul_right, tens_smul_right, tens_one_one, mat_xSw]
    have hs' : mat 2 F s * mat 2 F xSw = mat 2 F xSw * mat 2 F s := by
      rw [← map_mul, ← map_mul, hs]
    have hAs : conjSp 2 F A s = s := by
      refine conjSp_eq_of_mul_eq A ?_
      rw [hAmat, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hs']
    rw [e1 (s * y * s⁻¹), e1 y]
    simp only [map_mul, map_inv, hAs]
  · exfalso
    have hAmat : simMat A = tens 1 (reflM p r) := by rw [hP, hB]
    have hsq : simMat A * simMat A = (μ : F) • 1 := by
      rw [hAmat, tens_mul, one_mul, reflM_mul_self, hpr, tens_smul_right, tens_one_one]
    have hinv : ∀ y, conjSp 2 F A (conjSp 2 F A y) = y := by
      intro y
      refine conjSp_eq_of_mul_eq A ?_
      have h1 := mul_eq_conjSp A y
      have e : (simMat A * simMat A) * mat 2 F y * simMat A =
          simMat A * mat 2 F (conjSp 2 F A y) * (simMat A * simMat A) := by
        calc (simMat A * simMat A) * mat 2 F y * simMat A
            = simMat A * (simMat A * mat 2 F y) * simMat A := by simp only [Matrix.mul_assoc]
          _ = simMat A * (mat 2 F (conjSp 2 F A y) * simMat A) * simMat A := by rw [h1]
          _ = simMat A * mat 2 F (conjSp 2 F A y) * (simMat A * simMat A) := by
            simp only [Matrix.mul_assoc]
      rw [hsq, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
        Matrix.mul_one] at e
      exact (smul_right_injective _ μ.ne_zero e).symm
    have hd2 : ∀ y, d * d * ψ y = ψ y * (d * d) := fun y => by
      have e : d * d * ψ y * (d * d)⁻¹ = ψ y := by
        calc d * d * ψ y * (d * d)⁻¹ = d * (d * ψ y * d⁻¹) * d⁻¹ := by group
          _ = d * ψ (conjSp 2 F A y) * d⁻¹ := by rw [e1 y]
          _ = ψ (conjSp 2 F A (conjSp 2 F A y)) := e1 _
          _ = ψ y := by rw [hinv]
      rwa [mul_inv_eq_iff_eq_mul] at e
    have hd1 : ∀ y, d * ψ y = ψ y * d := fun y =>
      commute_of_sq_commute (odd_orderOf_of_mem_involutionOddCore hd) (hd2 y)
    obtain ⟨Y, hY1, hY2⟩ := exists_moved_of_reflection h2 μ.ne_zero hpr
    have hψY : ψ (conjSp 2 F A Y) = ψ Y := by
      rw [← e1 Y, mul_inv_eq_iff_eq_mul]
      exact hd1 Y
    have hmem : conjSp 2 F A Y * Y⁻¹ ∈ Subgroup.center (StatedSp 2 F) :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψY, mul_inv_cancel])
    rcases mem_center_iff.mp hmem with h | h
    · have hY : conjSp 2 F A Y = Y := mul_inv_eq_one.mp h
      apply hY1
      rw [← hAmat, mul_eq_conjSp A Y, hY]
    · have hY : conjSp 2 F A Y = negOne * Y := by
        rwa [mul_inv_eq_iff_eq_mul] at h
      apply hY2
      rw [← hAmat, mul_eq_conjSp A Y, hY, map_mul, mat_negOne, Matrix.neg_mul, Matrix.neg_mul,
        Matrix.one_mul]


theorem iLemma [Finite F] [Finite X] (hodd : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F)
    (ψ : StatedSp 2 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hnorm : ψ.range.Normal) {x : StatedSp 2 F} (hx : x * x = negOne) {f : X}
    (hf : ∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) {d : X}
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) :
    ∀ s : StatedSp 2 F, s * x = x * s → ∀ y,
      d * ψ (s * y * s⁻¹) * d⁻¹ = ψ s * (d * ψ y * d⁻¹) * (ψ s)⁻¹ := by
  obtain ⟨g, hg⟩ := exists_conj_xSw hodd hx
  have hx' : x = g * xSw * g⁻¹ := by rw [← hg]; group
  set Ψ : StatedSp 2 F →* X := ψ.comp (MulAut.conj g).toMonoidHom with hΨdef
  have hΨ : ∀ y, Ψ y = ψ (g * y * g⁻¹) := fun y => rfl
  have hrange : Ψ.range = ψ.range := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨g⁻¹ * y * g, by rw [hΨ]; congr 1; group⟩
  have hkerΨ : Ψ.ker ≤ Subgroup.center (StatedSp 2 F) := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ Subgroup.center (StatedSp 2 F) := hker (by simpa [hΨ] using hy)
    have h2 := Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center _).Normal) _ h1 g⁻¹
    have e1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e1] at h2
  have hnormΨ : Ψ.range.Normal := by rw [hrange]; exact hnorm
  have hfΨ : ∀ y, f * Ψ y * f⁻¹ = Ψ (xSw * y * xSw⁻¹) := by
    intro y
    rw [hΨ, hΨ, hf, hx']
    congr 1
    group
  have key := iLemma_std hodd h4 Ψ hkerΨ hnormΨ hfΨ hd
  intro s hs y
  have hs' : (g⁻¹ * s * g) * xSw = xSw * (g⁻¹ * s * g) := by
    rw [← hg]
    calc g⁻¹ * s * g * (g⁻¹ * x * g) = g⁻¹ * (s * x) * g := by group
      _ = g⁻¹ * (x * s) * g := by rw [hs]
      _ = g⁻¹ * x * g * (g⁻¹ * s * g) := by group
  have := key (g⁻¹ * s * g) hs' (g⁻¹ * y * g)
  simp only [hΨ] at this
  have e1 : g * (g⁻¹ * s * g * (g⁻¹ * y * g) * (g⁻¹ * s * g)⁻¹) * g⁻¹ = s * y * s⁻¹ := by group
  have e2 : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
  have e3 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [e1, e2, e3] at this
  exact this

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
