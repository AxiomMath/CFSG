module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDPlane

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Frame

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {K : Type}
  [Field K]

omit [Fintype κ] [DecidableEq κ] in
theorem pd_matrix_ext_mulVec' {A B : Matrix κ ι K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h1

@[expose] def IsPDFramePlane (M : Matrix κ ι K) (R : Matrix ι κ K) (Qg : QuadraticForm K (κ → K))
    (Qm : QuadraticForm K (ι → K)) (a b : κ → K) : Prop :=
  R * M = 1 ∧ (∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x)) ∧
    R *ᵥ a = 0 ∧ R *ᵥ b = 0 ∧ (∀ z, R *ᵥ z = 0 → ∃ p q : K, z = p • a + q • b) ∧
    Qg a = 1 ∧ Qg b = 1 ∧ polar Qg a b = 1

variable {M : Matrix κ ι K} {R : Matrix ι κ K} {Qg : QuadraticForm K (κ → K)}
  {Qm : QuadraticForm K (ι → K)} {a b : κ → K}

namespace IsPDFramePlane

variable (hF : IsPDFramePlane M R Qg Qm a b)
include hF

omit [DecidableEq κ] in
theorem hker [CharP K 2] :
    ∀ z, R *ᵥ z = 0 → (∀ x, R *ᵥ x = 0 → polar Qg z x = 0) → z = 0 := by
  obtain ⟨-, -, ha0, hb0, hspan, -, -, hab⟩ := hF
  intro z hz h
  obtain ⟨p, q, rfl⟩ := hspan z hz
  obtain ⟨h1, h2⟩ := pd_plane_polar hab p q
  have hp : p = 0 := by rw [← h1]; exact h _ hb0
  have hq : q = 0 := by rw [← h2]; exact h _ ha0
  rw [hp, hq, zero_smul, zero_smul, add_zero]

theorem ext_fix (h : Matrix ι ι K) :
    pcExtMat M R h *ᵥ a = a ∧ pcExtMat M R h *ᵥ b = b :=
  ⟨pcExtMat_mulVec_of_proj h hF.2.2.1, pcExtMat_mulVec_of_proj h hF.2.2.2.1⟩

theorem exists_eq_of_fix [Finite K] [CharP K 2] (hndg : Qg.polarBilin.Nondegenerate)
    (hndm : Qm.polarBilin.Nondegenerate)
    (hTm : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Qm x = 0) {g : GL κ K}
    (hg : g ∈ StatedOmega ⇑Qg) (hga : (g : Matrix κ κ K) *ᵥ a = a)
    (hgb : (g : Matrix κ κ K) *ᵥ b = b) :
    ∃ h : GL ι K, h ∈ StatedOmega ⇑Qm ∧ pcExtMat M R (h : Matrix ι ι K) = g := by
  refine exists_pcExtMat_eq_of_fix hF.1 hF.2.1 hF.hker hndg hndm hTm hg fun x hx => ?_
  obtain ⟨p, q, rfl⟩ := hF.2.2.2.2.1 x hx
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hga, hgb]

theorem rot_mul_M [CharP K 2] : pdRotMat Qg a b * M = M := by
  obtain ⟨-, hQ, ha0, hb0, -, -, -, -⟩ := hF
  refine pd_matrix_ext_mulVec' fun y => ?_
  rw [← Matrix.mulVec_mulVec]
  refine pdRotMat_mulVec_of_polar ?_ ?_
  · rw [polar_comm, pcExt_polar hQ, ha0, polar_zero_left]
  · rw [polar_comm, pcExt_polar hQ, hb0, polar_zero_left]

theorem R_mul_rot [CharP K 2] : R * pdRotMat Qg a b = R := by
  obtain ⟨-, -, ha0, hb0, -, -, -, -⟩ := hF
  refine pd_matrix_ext_mulVec' fun x => ?_
  rw [← Matrix.mulVec_mulVec, pdRotMat_mulVec, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add, ha0, hb0]
  simp

theorem rot_commute [CharP K 2] (h : Matrix ι ι K) :
    pdRotMat Qg a b * pcExtMat M R h = pcExtMat M R h * pdRotMat Qg a b :=
  pcExtMat_commute hF.rot_mul_M hF.R_mul_rot h

theorem fix_of_perfect [CharP K 2] {H : Subgroup (GL κ K)} {P : Subgroup H} (hP : ⁅P, P⁆ = P)
    (hcH : pdRotGL hF.2.2.2.2.2.2.2 ∈ H)
    (hPc : P ≤ centralizer {(⟨pdRotGL hF.2.2.2.2.2.2.2, hcH⟩ : H)}) {g : H} (hg : g ∈ P) :
    ((g : GL κ K) : Matrix κ κ K) *ᵥ a = a ∧ ((g : GL κ K) : Matrix κ κ K) *ᵥ b = b := by
  set hab := hF.2.2.2.2.2.2.2
  let F : Subgroup H :=
    { carrier := {x | ((x : GL κ K) : Matrix κ κ K) *ᵥ a = a ∧
        ((x : GL κ K) : Matrix κ κ K) *ᵥ b = b}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨?_, ?_⟩
        · rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hy.1, hx.1]
        · rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hy.2, hx.2]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        have hinv : ∀ w, ((x : GL κ K) : Matrix κ κ K) *ᵥ w = w →
            (((x⁻¹ : H) : GL κ K) : Matrix κ κ K) *ᵥ w = w := fun w hw => by
          conv_lhs => rw [← hw]
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
            Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
        exact ⟨hinv a hx.1, hinv b hx.2⟩ }
  have hle : ⁅P, P⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hcx := mem_centralizer_singleton_iff.1 (hPc hx)
    have hcy := mem_centralizer_singleton_iff.1 (hPc hy)
    have hcx' : (x : GL κ K) * pdRotGL hab = pdRotGL hab * x := congrArg Subtype.val hcx
    have hcy' : (y : GL κ K) * pdRotGL hab = pdRotGL hab * y := congrArg Subtype.val hcy
    have h := pdRot_commutator_fix hab hcx' hcy'
    refine ⟨?_, ?_⟩
    · have e : ((⁅x, y⁆ : H) : GL κ K) = ⁅(x : GL κ K), (y : GL κ K)⁆ := by
        simp [commutatorElement_def]
      rw [e]
      exact h.1
    · have e : ((⁅x, y⁆ : H) : GL κ K) = ⁅(x : GL κ K), (y : GL κ K)⁆ := by
        simp [commutatorElement_def]
      rw [e]
      exact h.2
  rw [← hP] at hg
  exact hle hg

end IsPDFramePlane

omit [DecidableEq ι] [DecidableEq κ] in
theorem pcExt_polar_vec {Qg : QuadraticForm K (κ → K)} {Qm : QuadraticForm K (ι → K)}
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x)) {vm : ι → K}
    {v : κ → K} (hMv : M *ᵥ vm = v) (x : κ → K) : polar Qg v x = polar Qm vm (R *ᵥ x) := by
  rw [polar_comm, ← hMv, pcExt_polar hQ, polar_comm]

theorem pcExtMat_sym_conj [CharP K 2] (hRM : R * M = 1) {Qg : QuadraticForm K (κ → K)}
    {Qm : QuadraticForm K (ι → K)}
    (hQ : ∀ x y, Qg (x + M *ᵥ y) - Qg x = Qm (R *ᵥ x + y) - Qm (R *ᵥ x)) {vm : ι → K}
    {v : κ → K} (hMv : M *ᵥ vm = v) (hvm : Qm vm = 1) (hv : Qg v = 1) (h : Matrix ι ι K) :
    pcExtMat M R ((pdSym Qm vm : Matrix ι ι K) * h * (pdSym Qm vm : Matrix ι ι K)) =
      (pdSym Qg v : Matrix κ κ K) * pcExtMat M R h * (pdSym Qg v : Matrix κ κ K) := by
  have hRv : R *ᵥ v = vm := by rw [← hMv, Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec]
  have hSM : (pdSym Qg v : Matrix κ κ K) * M = M * (pdSym Qm vm : Matrix ι ι K) := by
    refine pd_matrix_ext_mulVec' fun y => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pdSym_mulVec_of_charTwo hv,
      pdSym_mulVec_of_charTwo hvm, Matrix.mulVec_add, Matrix.mulVec_smul, hMv,
      pcExt_polar_vec hQ hMv, Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec]
  have hRS : R * (pdSym Qg v : Matrix κ κ K) = (pdSym Qm vm : Matrix ι ι K) * R := by
    refine pd_matrix_ext_mulVec' fun x => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pdSym_mulVec_of_charTwo hv,
      pdSym_mulVec_of_charTwo hvm, Matrix.mulVec_add, Matrix.mulVec_smul, hRv,
      pcExt_polar_vec hQ hMv]
  have hS : (pdSym Qg v : Matrix κ κ K) * (pdSym Qg v : Matrix κ κ K) = 1 := by
    rw [← Units.val_mul, pdSym_mul_self, Units.val_one]
  have hs : (pdSym Qm vm : Matrix ι ι K) * (pdSym Qm vm : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, pdSym_mul_self, Units.val_one]
  exact pcExtMat_conj_eq hSM hRS hS hs h

end Frame

end CFSG.SeitzReduction.SymplecticPilot
