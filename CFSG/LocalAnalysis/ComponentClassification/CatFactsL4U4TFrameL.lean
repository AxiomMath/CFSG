module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TBlocks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Core

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace TBlocks

open Matrix HBlocks

variable {F : Type} [Field F]

theorem isCompl_ker_of_sq {V : Type*} [AddCommGroup V] [Module F V] (h2 : (2 : F) ≠ 0)
    {T : Module.End F V} (hT : ∀ v, T (T v) = v) :
    IsCompl (LinearMap.ker (T - 1)) (LinearMap.ker (T + 1)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hw
    rw [hv] at hw
    have : (2 : F) • v = 0 := by rw [two_smul]; exact hw
    exact (smul_eq_zero.1 this).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v = (2 : F)⁻¹ • (v + T v) + (2 : F)⁻¹ • (v - T v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hT,
        add_comm (T v), sub_self]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hT,
        ← smul_add, sub_add_sub_cancel', sub_self, smul_zero]

theorem exists_frame_t2_L4 (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 4) (Fin 4) F} (hXX : X * X = 1)
    (hdet : X.det = 1) (h1 : X ≠ 1) (hm1 : X ≠ -1) :
    ∃ P : GL (Fin 4) F,
      X * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * X1 (1 : F) := by
  classical
  set T := Matrix.toLin' X with hT
  have hTT : ∀ v, T (T v) = v := fun v => by
    rw [hT, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hXX,
      Matrix.one_mulVec]
  have hc := isCompl_ker_of_sq h2 hTT
  obtain ⟨Vp, hVp⟩ : ∃ V : Submodule F (Fin 4 → F), V = LinearMap.ker (T - 1) := ⟨_, rfl⟩
  obtain ⟨Vm, hVm⟩ : ∃ V : Submodule F (Fin 4 → F), V = LinearMap.ker (T + 1) := ⟨_, rfl⟩
  rw [← hVp, ← hVm] at hc
  have hTp : ∀ v ∈ Vp, T v = (1 : F) • v := fun v hv => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [one_smul, hv]
  have hTm : ∀ v ∈ Vm, T v = (-1 : F) • v := fun v hv => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hv
    rw [neg_one_smul, hv]
  have hdetT := det_eq_of_isCompl_smul hc hTp hTm
  have hdX : LinearMap.det T = 1 := by rw [hT, LinearMap.det_toLin', hdet]
  rw [hdX, one_pow, one_mul] at hdetT
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun] at hsum
  have hXv : ∀ v, X *ᵥ v = T v := fun v => by rw [hT, Matrix.toLin'_apply]
  have hdp : Module.finrank F Vp ≠ 0 := by
    intro h0
    apply hm1
    have hbot : Vp = ⊥ := Submodule.finrank_eq_zero.1 h0
    have htop : Vm = ⊤ := by
      have := hc.sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    have hall : ∀ v, X *ᵥ v = -v := fun v => by
      rw [hXv, hTm v (by rw [htop]; exact Submodule.mem_top), neg_one_smul]
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.neg_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hdm : Module.finrank F Vm ≠ 0 := by
    intro h0
    apply h1
    have hbot : Vm = ⊥ := Submodule.finrank_eq_zero.1 h0
    have htop : Vp = ⊤ := by
      have := hc.sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    have hall : ∀ v, X *ᵥ v = v := fun v => by
      rw [hXv, hTp v (by rw [htop]; exact Submodule.mem_top), one_smul]
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hm2 : Module.finrank F Vm = 2 := by
    rcases Nat.even_or_odd (Module.finrank F Vm) with he | ho
    · obtain ⟨k, hk⟩ := he
      omega
    · exfalso
      rw [ho.neg_one_pow] at hdetT
      apply h2
      linear_combination hdetT
  have hp2 : Module.finrank F Vp = 2 := by omega
  set bp := Module.finBasisOfFinrankEq F Vp hp2 with hbp
  set bm := Module.finBasisOfFinrankEq F Vm hm2 with hbm
  set col : Fin 4 → Fin 4 → F := ![bp 0, bp 1, bm 0, bm 1] with hcol
  set Pm : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => col j i with hPm
  have hPv : ∀ v : Fin 4 → F, Pm *ᵥ v = ((v 0 • bp 0 + v 1 • bp 1 : Vp) : Fin 4 → F) +
      ((v 2 • bm 0 + v 3 • bm 1 : Vm) : Fin 4 → F) := by
    intro v
    ext i
    simp [hPm, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  have hinj : Function.Injective Pm.mulVec := by
    intro v w hvw
    have hd : Pm *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
    rw [hPv] at hd
    set a := v - w with ha
    have hp : (a 0 • bp 0 + a 1 • bp 1 : Vp) = 0 := by
      have hmem : ((a 0 • bp 0 + a 1 • bp 1 : Vp) : Fin 4 → F) ∈ Vm := by
        rw [eq_neg_of_add_eq_zero_left hd]
        exact Vm.neg_mem (Subtype.mem _)
      exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _ (Subtype.mem _) hmem)
    have hm : (a 2 • bm 0 + a 3 • bm 1 : Vm) = 0 := by
      have hmem : ((a 2 • bm 0 + a 3 • bm 1 : Vm) : Fin 4 → F) ∈ Vp := by
        rw [eq_neg_of_add_eq_zero_right hd]
        exact Vp.neg_mem (Subtype.mem _)
      exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _ hmem (Subtype.mem _))
    have hp' := Fintype.linearIndependent_iff.mp bp.linearIndependent ![a 0, a 1]
      (by simpa [Fin.sum_univ_two] using hp)
    have hm' := Fintype.linearIndependent_iff.mp bm.linearIndependent ![a 2, a 3]
      (by simpa [Fin.sum_univ_two] using hm)
    have h0 : a = 0 := by
      ext k
      fin_cases k
      · simpa using hp' 0
      · simpa using hp' 1
      · simpa using hm' 0
      · simpa using hm' 1
    exact sub_eq_zero.1 h0
  have hdetP : Pm.det ≠ 0 := by
    have := (Matrix.mulVec_injective_iff_isUnit.1 hinj)
    exact ((Matrix.isUnit_iff_isUnit_det Pm).1 this).ne_zero
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Pm hdetP, ?_⟩
  rw [GeneralLinearGroup.val_mkOfDetNeZero]
  have hXp : ∀ k, X *ᵥ (bp k : Fin 4 → F) = bp k := fun k => by
    rw [hXv, hTp _ (bp k).2, one_smul]
  have hXm : ∀ k, X *ᵥ (bm k : Fin 4 → F) = -(bm k : Fin 4 → F) := fun k => by
    rw [hXv, hTm _ (bm k).2, neg_one_smul]
  ext i j
  have key : (X * Pm) i j = (X *ᵥ col j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hPm]
  rw [key]
  fin_cases j <;> simp [hcol, hXp, hXm, X1, Matrix.mul_apply, Fin.sum_univ_four, hPm]

end TBlocks

end CFSG.ComponentClassification.CatFactsL4U4
