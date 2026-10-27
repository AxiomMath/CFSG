module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapTypeOffender

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.Quasithin

variable {G : Type} [Group G] {S M : Subgroup G}

theorem map_thompsonJ_eq_iSup (hSM : S ≤ M) {Ω : Type*} (θ : ↥M →* Perm Ω) :
    ((thompsonJ S).subgroupOf M).map θ =
      ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian S A), (A.subgroupOf M).map θ := by
  have hAM : ∀ A : Subgroup G, IsMaxElemAbelian S A → A ≤ M := fun A hA => hA.1.trans hSM
  have hJ : (thompsonJ S).subgroupOf M = ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian S A),
      A.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    have hJM : thompsonJ S ≤ M := by
      refine iSup_le fun A => iSup_le fun hA => hAM A hA
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJM]
    show thompsonJ S = _
    rw [Subgroup.map_iSup]
    unfold thompsonJ
    refine iSup_congr fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_congr fun hA => ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hAM A hA)]
  rw [hJ, Subgroup.map_iSup]
  refine iSup_congr fun A => ?_
  rw [Subgroup.map_iSup]

theorem exists_omegaEquiv_Wr_of_offenders_swapType (hS2 : IsPGroup 2 S) (hSM : S ≤ M)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (θ : ↥M →* Perm Ω)
    (hsw : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.SwapType ((A.subgroupOf M).map θ)) :
    ∃ (r s : ℕ) (e : Ω ≃ OmegaE r s),
      (((thompsonJ S).subgroupOf M).map θ).map e.permCongrHom.toMonoidHom = Wr r s := by
  have hP : IsPGroup 2 ((S.subgroupOf M).map θ) := (hS2.comap_subtype (K := M)).map θ
  have h := Offender.exists_omegaEquiv_Wr_of_swapType hP
    (fun A : {A : Subgroup G // IsMaxElemAbelian S A} => (A.1.subgroupOf M).map θ)
    (fun A => Subgroup.map_mono (Subgroup.comap_mono A.2.1)) (fun A => hsw A.1 A.2)
  rw [map_thompsonJ_eq_iSup hSM θ]
  obtain ⟨r, s, e, he⟩ := h
  refine ⟨r, s, e, ?_⟩
  rw [← he]
  congr 1
  apply le_antisymm
  · exact iSup_le fun A => iSup_le fun hA =>
      le_iSup (fun A : {A : Subgroup G // IsMaxElemAbelian S A} => (A.1.subgroupOf M).map θ) ⟨A, hA⟩
  · exact iSup_le fun A => le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) =>
      (A.subgroupOf M).map θ) A.1 A.2

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
