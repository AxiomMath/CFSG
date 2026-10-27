module

public import CFSG.GF2Type.SmithTypeE.L6.IdGramRel
public import CFSG.GF2Type.SmithTypeE.L6.IdPhi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.GF2Type.SmithTypeE.LMod
open CFSG.LargeExtraspecial.SMod20 (V exists_linear_of_gram)
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] def IsModelPhi
    (S : Setting G) (ψ : Mbar0 S ≃* T6) (φ : S.Qt ≃ₗ[ZMod 2] V) : Prop :=
  ∀ i : Fin 1395, φ (xcl S ψ i) = wtV i

section Phi


theorem planeHom_of_mem (ψ : Mbar0 S ≃* T6) (m : Mbar0 S) (i : Fin 1395) :
    planeHom S ψ (m : S.Mbar) i = ψ m • i := by
  rw [planeHom_eq_iff, piM_of_mem]
  exact image_wPlane_smul (ψ m) i

variable [IsSimpleGroup G] (I : Inputs10) (ψ : Mbar0 S ≃* T6)

include I in
theorem span_xcl (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    Submodule.span (ZMod 2) (Set.range fun i : Fin 1395 => xcl S ψ i) = ⊤ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hli := linearIndependent_of_gram_opp S.q.polarBilin (xcl S ψ) fun i j hi hj => by
    rw [polarBilin_apply_apply]
    exact gram_eq_opp I ψ hw haQ hne hi hj
  have htop := hli.span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, S.finrank_Qt_eq_two_mul_width, hw])
  rw [eq_top_iff, ← htop]
  refine Submodule.span_mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨_, spanIdx_lt s⟩, rfl⟩

include I in
theorem exists_isModelPhi (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : ∃ φ : S.Qt ≃ₗ[ZMod 2] V, IsModelPhi S ψ φ := by
  have hG : ∀ i j : Fin 1395, fModel (wtV i) (wtV j) = S.q.polarBilin (xcl S ψ i) (xcl S ψ j) :=
    fun i j => by
      rw [fModel_wtV i.2 j.2, polarBilin_apply_apply, gram_eq_opp I ψ hw haQ hne i.2 j.2]
  obtain ⟨L, hL⟩ := exists_linear_of_gram (K := ZMod 2) (ι := Fin 1395) S.q.polarBilin fModel
    (span_xcl I ψ hw haQ hne) span_wtV (fun _ hv => fModel_nondegenerate hv) hG
  obtain ⟨L', hL'⟩ := exists_linear_of_gram (K := ZMod 2) (ι := Fin 1395) fModel S.q.polarBilin
    span_wtV (span_xcl I ψ hw haQ hne) (fun v hv => S.q_nondegenerate.1 v hv)
    (fun i j => (hG i j).symm)
  have h1 : L'.comp L = LinearMap.id :=
    LinearMap.ext_on_range (span_xcl I ψ hw haQ hne) fun i => by
      rw [LinearMap.comp_apply, hL, hL', LinearMap.id_apply]
  have h2 : L.comp L' = LinearMap.id :=
    LinearMap.ext_on_range span_wtV fun i => by
      rw [LinearMap.comp_apply, hL', hL, LinearMap.id_apply]
  exact ⟨LinearEquiv.ofLinearMap L L' h2 h1, hL⟩

variable {ψ} {φ : S.Qt ≃ₗ[ZMod 2] V}

include I in
theorem IsModelPhi.cl (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {h : G}
    (hbQ : h * S.z * h⁻¹ ∈ S.QG) (hbne : h * S.z * h⁻¹ ≠ S.z) :
    φ (S.cl (h * S.z * h⁻¹)) = wtV (planeOf S ψ h) := by
  rw [cl_eq_xcl I ψ hw hbQ hbne, hφ]

theorem IsModelPhi.symm_wtV (hφ : IsModelPhi S ψ φ) (i : Fin 1395) :
    φ.symm (wtV i) = xcl S ψ i := by
  rw [← hφ i, LinearEquiv.symm_apply_apply]

include I in
theorem IsModelPhi.isometry (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (u v : S.Qt) :
    fModel (φ u) (φ v) = polar S.q u v := by
  have key : fModel.compl₁₂ (φ : S.Qt →ₗ[ZMod 2] V) (φ : S.Qt →ₗ[ZMod 2] V) =
      S.q.polarBilin := by
    refine LinearMap.ext_on_range (span_xcl I ψ hw haQ hne) fun i => ?_
    refine LinearMap.ext_on_range (span_xcl I ψ hw haQ hne) fun j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, polarBilin_apply_apply]
    rw [hφ i, hφ j, fModel_wtV i.2 j.2, gram_eq_opp I ψ hw haQ hne i.2 j.2]
  have := congrArg (fun B : LinearMap.BilinForm (ZMod 2) S.Qt => B u v) key
  simpa using this

include I in
theorem IsModelPhi.Phi_wtV (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (m : S.M) (i : Fin 1395) :
    Phi S φ m (wtV i) = wtV (planeHom S ψ (rhoM S m) i) := by
  rw [Phi_apply, hφ.symm_wtV, ρ_xcl I ψ hw haQ hne m i, hφ]

include I in
theorem IsModelPhi.Phi_eq_rhoMod (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (m : S.M)
    (h0 : rhoM S m ∈ Mbar0 S) : Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩) := by
  apply LinearEquiv.toLinearMap_injective
  refine ext_wtV fun i => ?_
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, hφ.Phi_wtV I hw haQ hne m i, rhoMod_wtV]
  exact congrArg (fun j : Fin 1395 => wtV j.val) (planeHom_of_mem ψ ⟨rhoM S m, h0⟩ i)

omit
  [IsSimpleGroup G] in
theorem exists_rhoM_mem_Mbar0 (ψ : Mbar0 S ≃* T6) (t : T6) :
    ∃ m : S.M, ∃ h0 : rhoM S m ∈ Mbar0 S, ψ ⟨rhoM S m, h0⟩ = t := by
  obtain ⟨m, hm⟩ := exists_rhoM_eq ((ψ.symm t : Mbar0 S) : S.Mbar)
  refine ⟨m, hm ▸ (ψ.symm t).2, ?_⟩
  have e : (⟨rhoM S m, hm ▸ (ψ.symm t).2⟩ : Mbar0 S) = ψ.symm t := Subtype.ext hm
  rw [e, MulEquiv.apply_symm_apply]

include I in
theorem IsModelPhi.exists_Phi_eq_tvEquiv (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {k : ℕ} (hk : k < 1953) :
    ∃ m : S.M, Phi S φ m = tvEquiv k := by
  obtain ⟨m, h0, hm⟩ := exists_rhoM_mem_Mbar0 ψ ⟨tvP ⟨k, hk⟩, tvP_mem _⟩
  exact ⟨m, by rw [hφ.Phi_eq_rhoMod I hw haQ hne m h0, hm, rhoMod_tvP]⟩

end Phi

end CFSG.GF2Type.SmithTypeE.L6
