module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)
open E8Neighbour

section Conj

variable {H : Type*} [Group H]

theorem map_conj_inf_centralizer_subgroup (n : H) (M Y : Subgroup H) :
    (M ⊓ centralizer (Y : Set H)).map (MulAut.conj n).toMonoidHom =
      M.map (MulAut.conj n).toMonoidHom ⊓
        centralizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup H) : Set H) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective, F4Pilot.map_centralizer_mulEquiv]

theorem map_conj_inv_map_conj_self (n : H) (M : Subgroup H) :
    (M.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = M := by
  rw [Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id M]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, MonoidHom.id_apply, inv_inv]
  group

theorem map_conj_map_conj_inv_self (n : H) (M : Subgroup H) :
    (M.map (MulAut.conj n⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom = M := by
  have h := map_conj_inv_map_conj_self n⁻¹ M
  rwa [inv_inv] at h

end Conj

section Reduction

variable (K : Type) [Field K]

@[expose] def E8TwoLeviOverlapInput : Prop :=
  ∀ γ : Fin (Tag.rank .E8) → ℤ, γ ∈ orthRoots (highRoot .E8) →
    ∀ A' : Subgroup (adjointGroup .E8 K),
      A' ≤ (rootSubgroup .E8 K γ ⊔ rootSubgroup .E8 K (-γ)).subgroupOf (adjointGroup .E8 K) →
      IsCyclic A' → Nat.card A' = Nat.card K + 1 →
      perfectCore (e7Levi K ⊓ centralizer (A' : Set (adjointGroup .E8 K))) =
          (rootSpan .E8 K (orthRoots (highRoot .E8) ∩ orthRoots γ)).subgroupOf
            (adjointGroup .E8 K) ∧
        IsSimpleGroup ((rootSpan .E8 K (orthRoots (highRoot .E8) ∩ orthRoots γ)).subgroupOf
          (adjointGroup .E8 K)) ∧
        center ((rootSpan .E8 K (orthRoots (highRoot .E8) ∩ orthRoots γ)).subgroupOf
          (adjointGroup .E8 K)) = ⊥

variable {K}

theorem map_conj_rep_rootPair (N : E8Neighbour) {δ : Fin (Tag.rank .E8) → ℤ}
    (hδ : IsRoot .E8 δ) :
    ((rootSubgroup .E8 K δ ⊔ rootSubgroup .E8 K (-δ)).subgroupOf (adjointGroup .E8 K)).map
        (MulAut.conj (N.rep K)).toMonoidHom =
      (rootSubgroup .E8 K (N.weyl • δ) ⊔ rootSubgroup .E8 K (-(N.weyl • δ))).subgroupOf
        (adjointGroup .E8 K) := by
  have hle : ∀ γ : Fin (Tag.rank .E8) → ℤ,
      rootSubgroup .E8 K γ ⊔ rootSubgroup .E8 K (-γ) ≤ adjointGroup .E8 K :=
    fun γ => sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  apply Subgroup.map_injective (adjointGroup .E8 K).subtype_injective
  rw [map_conj_map_subtype_E8, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (hle _), inf_of_le_left (hle _), Subgroup.map_sup,
    map_conj_rep_rootSubgroup N hδ, map_conj_rep_rootSubgroup N (IsRoot.neg hδ), smul_neg]

theorem image_smul_orthRoots_inter (w : WeylGroup .E8) (a b : Fin (Tag.rank .E8) → ℤ) :
    (fun α => w • α) '' (orthRoots a ∩ orthRoots b) = orthRoots (w • a) ∩ orthRoots (w • b) := by
  rw [Set.image_inter (MulAction.injective w), image_smul_orthRoots, image_smul_orthRoots]

theorem e8TwoOverlapInput_of_levi [Finite K] (h : E8TwoLeviOverlapInput K) :
    E8TwoOverlapInput K := by
  intro A hAJ hcyc hA N N' hNN'
  have : Finite (adjointGroup .E8 K) := by
    have : Finite (ModGL Tag.E8 K) := finite_modGL
    infer_instance
  set ρ := N.rep K with hρ
  set δ : Fin (Tag.rank .E8) → ℤ := N.weyl⁻¹ • N'.root with hδdef
  have hδroot : IsRoot .E8 δ := IsRoot.smul N'.isRoot_root _
  have hδ : δ ∈ orthRoots (highRoot .E8) := by
    refine ⟨hδroot, ?_⟩
    rw [← iform_smul N.weyl, hδdef, smul_inv_smul, weyl_smul_highRoot,
      iform_root_root_eq_zero hNN']
  have hwδ : N.weyl • δ = N'.root := by rw [hδdef, smul_inv_smul]
  set A' := (A.map (MulAut.conj (N'.rep K)).toMonoidHom).map (MulAut.conj ρ⁻¹).toMonoidHom
    with hA'def
  have hA'J : A' ≤ (rootSubgroup .E8 K δ ⊔ rootSubgroup .E8 K (-δ)).subgroupOf
      (adjointGroup .E8 K) := by
    have h1 : A.map (MulAut.conj (N'.rep K)).toMonoidHom ≤
        (rootSubgroup .E8 K N'.root ⊔ rootSubgroup .E8 K (-N'.root)).subgroupOf
          (adjointGroup .E8 K) :=
      (Subgroup.map_mono hAJ).trans (map_conj_rep_rootSL2 N').le
    have h2 := map_conj_rep_rootPair (K := K) N hδroot
    rw [hwδ] at h2
    rw [hA'def, ← map_conj_inv_map_conj_self ρ ((rootSubgroup .E8 K δ ⊔
      rootSubgroup .E8 K (-δ)).subgroupOf (adjointGroup .E8 K)), h2]
    exact Subgroup.map_mono h1
  have hcyc' : IsCyclic A' := by
    have e : A ≃* A' := (A.equivMapOfInjective _ (MulAut.conj (N'.rep K)).injective).trans
      ((A.map (MulAut.conj (N'.rep K)).toMonoidHom).equivMapOfInjective _
        (MulAut.conj ρ⁻¹).injective)
    exact isCyclic_of_surjective e e.surjective
  have hcard' : Nat.card A' = Nat.card K + 1 := by
    rw [hA'def, Subgroup.card_map_of_injective (MulAut.conj ρ⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.conj (N'.rep K)).injective, hA]
  obtain ⟨h1, h2, h3⟩ := h δ hδ A' hA'J hcyc' hcard'
  have hA'ρ : A'.map (MulAut.conj ρ).toMonoidHom = A.map (MulAut.conj (N'.rep K)).toMonoidHom :=
    map_conj_map_conj_inv_self ρ _
  have hinter : N.levi K ⊓ centralizer ((A.map (MulAut.conj (N'.rep K)).toMonoidHom :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) =
      (e7Levi K ⊓ centralizer (A' : Set (adjointGroup .E8 K))).map
        (MulAut.conj ρ).toMonoidHom := by
    rw [map_conj_inf_centralizer_subgroup, hA'ρ, hρ, map_conj_rep_e7Levi]
  have hspan : overlapSpan K N N' =
      ((rootSpan .E8 K (orthRoots (highRoot .E8) ∩ orthRoots δ)).subgroupOf
        (adjointGroup .E8 K)).map (MulAut.conj ρ).toMonoidHom := by
    rw [hρ, map_conj_rep_subgroupOf_rootSpan N (fun α hα => hα.1.1),
      image_smul_orthRoots_inter, weyl_smul_highRoot, hwδ]
    rfl
  set S := (rootSpan .E8 K (orthRoots (highRoot .E8) ∩ orthRoots δ)).subgroupOf
    (adjointGroup .E8 K) with hS
  have eS : S ≃* S.map (MulAut.conj ρ).toMonoidHom :=
    S.equivMapOfInjective _ (MulAut.conj ρ).injective
  refine ⟨?_, ?_, ?_⟩
  · rw [hinter, ← CFSG.Quasithin.map_perfectCore, h1, hspan]
  · rw [hspan]
    exact eS.symm.isSimpleGroup
  · rw [hspan]
    exact F4Pilot.center_eq_bot_congr eS h3

end Reduction

end CFSG.SeitzReduction.E8Pilot
