module

public import CFSG.GF2Type.SmithTypeE.E7.IdGramRel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.GF2Type.SmithTypeE.DMod
open CFSG.SmithD6
open CFSG.LargeExtraspecial.SMod20 (exists_linear_of_gram)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Phi


theorem span_xcl [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16) (ψ : S.Mbar ≃* TD6)
    {g : G} (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    Submodule.span (ZMod 2) (Set.range fun i : Fin 75735 => xcl S ψ g i.val) = ⊤ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hFP : ∀ (s : Fin 32) (j : Fin 75735), fModel (wtV spanIdx[s.val]!) (wtV j.val) =
      S.q.polarBilin (xcl S ψ g spanIdx[s.val]!) (xcl S ψ g j.val) := by
    intro s j
    rw [fModel_wtV (spanIdx_lt s) j.2, polarBilin_apply_apply,
      gram_eq_opp I hw ψ hψ haQ hne (spanIdx_lt s) j.2]
  have hli : LinearIndependent (ZMod 2) fun s : Fin 32 => xcl S ψ g spanIdx[s.val]! := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hB : ∀ j : Fin 75735, ∑ s : Fin 32,
        c s * S.q.polarBilin (xcl S ψ g spanIdx[s.val]!) (xcl S ψ g j.val) = 0 := by
      intro j
      have h := congrArg (fun x => S.q.polarBilin x (xcl S ψ g j.val)) hc
      simpa [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h
    have key : fModel (∑ s : Fin 32, c s • wtV spanIdx[s.val]!) = 0 := by
      refine LinearMap.ext_on_range span_wtV fun j => ?_
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply]
      simp only [hFP]
      exact hB j
    have h0 : ∑ s : Fin 32, c s • wtV spanIdx[s.val]! = 0 :=
      fModel_nondegenerate fun w => by rw [key, LinearMap.zero_apply]
    exact (Fintype.linearIndependent_iff.mp linearIndependent_spanIdx) c h0
  have hcard : Fintype.card (Fin 32) = Module.finrank (ZMod 2) S.Qt := by
    rw [Fintype.card_fin, S.finrank_Qt_eq_two_mul_width, hw]
  have htop := hli.span_eq_top_of_card_eq_finrank' hcard
  rw [eq_top_iff, ← htop]
  refine Submodule.span_mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨_, spanIdx_lt s⟩, rfl⟩

theorem exists_isModelPhi [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (ψ : S.Mbar ≃* TD6) {g : G}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2), ∀ m : S.M,
      Phi S φ m = rhoMod (ψ (rhoM S m)) := by
  have hG : ∀ i j : Fin 75735, fModel (wtV i.val) (wtV j.val) =
      S.q.polarBilin (xcl S ψ g i.val) (xcl S ψ g j.val) := fun i j => by
    rw [fModel_wtV i.2 j.2, polarBilin_apply_apply, gram_eq_opp I hw ψ hψ haQ hne i.2 j.2]
  obtain ⟨L, hL⟩ := exists_linear_of_gram (K := ZMod 2) (ι := Fin 75735) S.q.polarBilin fModel
    (span_xcl I hw ψ hψ haQ hne) span_wtV (fun _ hv => fModel_nondegenerate hv) hG
  obtain ⟨L', hL'⟩ := exists_linear_of_gram (K := ZMod 2) (ι := Fin 75735) fModel S.q.polarBilin
    span_wtV (span_xcl I hw ψ hψ haQ hne) (fun v hv => S.q_nondegenerate.1 v hv)
    (fun i j => (hG i j).symm)
  have h1 : L'.comp L = LinearMap.id :=
    LinearMap.ext_on_range (span_xcl I hw ψ hψ haQ hne) fun i => by
      rw [LinearMap.comp_apply, hL, hL', LinearMap.id_apply]
  have h2 : L.comp L' = LinearMap.id :=
    LinearMap.ext_on_range span_wtV fun i => by
      rw [LinearMap.comp_apply, hL', hL, LinearMap.id_apply]
  obtain ⟨φ, hφL⟩ : ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2), ∀ u, φ u = L u :=
    ⟨LinearEquiv.ofLinear L L' h2 h1, fun u => rfl⟩
  have hφ : ∀ i : Fin 75735, φ (xcl S ψ g i.val) = wtV i.val := fun i => (hφL _).trans (hL i)
  refine ⟨φ, fun m => ?_⟩
  apply LinearEquiv.toLinearMap_injective
  refine ext_wtV fun i => ?_
  have hsymm : φ.symm (wtV i.val) = xcl S ψ g i.val := by
    rw [← hφ i, LinearEquiv.symm_apply_apply]
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, Phi_apply, hsymm,
    xcl_smul I hw ψ hψ haQ hne m i, hφ, rhoMod_wtV]

end Phi

end CFSG.GF2Type.SmithTypeE.E7
