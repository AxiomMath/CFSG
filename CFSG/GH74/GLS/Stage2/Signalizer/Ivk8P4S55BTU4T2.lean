module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4T

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher BS4 BL4
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem mem_flag_of_smul {d : ℕ} {N : Submodule K (HypIndex 2 0 → K)} {g : hypSU h 2 0}
    (hg : g • hypFlag h 2 0 d = N) {w : HypIndex 2 0 → K} (hw : w ∈ N) :
    (((g : GL (HypIndex 2 0) K)⁻¹ : GL (HypIndex 2 0) K) : MH K) *ᵥ w ∈ hypFlag h 2 0 d := by
  replace hg := (hypSU_smul_eq_map g (hypFlag h 2 0 d)).symm.trans hg
  rw [← hg] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  show (((g : GL (HypIndex 2 0) K)⁻¹ : GL (HypIndex 2 0) K) : MH K) *ᵥ
    (((g : GL (HypIndex 2 0) K) : MH K) *ᵥ u) ∈ hypFlag h 2 0 d
  rw [mulVec_mulVec, gi_mul_g, one_mulVec]
  exact hu

theorem cv_bl {N : Submodule K (HypIndex 2 0 → K)} {g : hypSU h 2 0}
    (hg : g • hypFlag h 2 0 2 = N) {M : MH K} (hM : ∀ v ∈ N, M *ᵥ v ∈ N) :
    (cv (g : GL (HypIndex 2 0) K) M).toBlocks₂₁ = 0 := by
  rw [cv]
  apply toBlocks₂₁_rv_of_stab2 h
  intro v hv
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact stab_conj h hg hM v hv

theorem cv_e0 {N : Submodule K (HypIndex 2 0 → K)} {g : hypSU h 2 0}
    (hg : g • hypFlag h 2 0 1 = N) {M : MH K} (hM : ∀ v ∈ N, M *ᵥ v ∈ N) :
    ∃ c : K, cv (g : GL (HypIndex 2 0) K) M *ᵥ e0 = c • e0 := by
  rw [cv]
  refine ⟨_, mulVec_e0_rv_of_stab1 h fun v hv => ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact stab_conj h hg hM v hv

theorem sv_bl {N : Submodule K (HypIndex 2 0 → K)} {g : hypSU h 2 0}
    (hg : g • hypFlag h 2 0 2 = N) {A : MH K}
    (hA : ∀ v ∈ N, A *ᵥ (fun a => h.bar (v a)) ∈ N) :
    (sv h (g : GL (HypIndex 2 0) K) A).toBlocks₂₁ = 0 := by
  rw [sv]
  apply toBlocks₂₁_rv_of_stab2 h
  intro v hv
  have hF := hypFlag_eq_posFlag (r := 2) (ε := 0) h (by norm_num) (i := 2) (by norm_num)
  have hv' : (fun a => h.bar (v a)) ∈ hypFlag h 2 0 2 := by
    rw [hF, mem_posFlag] at hv ⊢
    intro a ha
    simp [hv a ha]
  have hgv : ((g : GL (HypIndex 2 0) K) : MH K) *ᵥ (fun a => h.bar (v a)) ∈ N := by
    rw [← (hypSU_smul_eq_map g (hypFlag h 2 0 2)).symm.trans hg]
    exact ⟨_, hv', rfl⟩
  have e : ((g : GL (HypIndex 2 0) K) : MH K).map h.bar *ᵥ v =
      fun a => h.bar ((((g : GL (HypIndex 2 0) K) : MH K) *ᵥ (fun b => h.bar (v b))) a) := by
    funext a
    simp [mulVec, dotProduct, h.bar_bar]
  rw [← mulVec_mulVec, ← mulVec_mulVec, e]
  exact mem_flag_of_smul hg (hA _ hgv)

theorem cv_scalar (G : GL (HypIndex 2 0) K) (c : Kˣ) :
    cv G ((GeneralLinearGroup.scalar (HypIndex 2 0) c : GL (HypIndex 2 0) K) : MH K) =
      (c : K) • 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal, cv_smul,
    cv_one]

@[expose] noncomputable def ψU (h : UnitaryFieldData p f K) (G : GL (HypIndex 2 0) K) :
    hypSU h 2 0 →* GL (Fin 2 ⊕ Fin 2) K :=
  rvGL.comp ((MulAut.conj G⁻¹).toMonoidHom.comp (hypSU h 2 0).subtype)

theorem coe_ψU (G : GL (HypIndex 2 0) K) (s : hypSU h 2 0) :
    ((ψU h G s : GL (Fin 2 ⊕ Fin 2) K) : MB K) = cv G ((s : GL (HypIndex 2 0) K) : MH K) := by
  simp only [ψU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    Subgroup.coe_subtype, coe_rvGL, Units.val_mul, cv]

theorem ψU_injective (G : GL (HypIndex 2 0) K) : Function.Injective (ψU h G) :=
  rvGL_injective.comp ((MulAut.conj G⁻¹).injective.comp Subtype.val_injective)

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
