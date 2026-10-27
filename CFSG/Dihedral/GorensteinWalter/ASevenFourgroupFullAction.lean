module

public import CFSG.Dihedral.GorensteinWalter.ASevenFourgroupFullActionInputs
public import Certificates.Certificate112

import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenDistinctInvertedConjugate
public import CFSG.Dihedral.BlueprintDefs
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.GorensteinWalter

open DihedralBlueprint

local instance : DecidablePred (fun x : ASevenCertificateGroup => x ∈ a7V) :=
  fun x => by
    change Decidable (x = 1 ∨ x = a7t ∨ x = a7u ∨ x = a7t * a7u)
    infer_instance

local instance : Fintype a7V := Subtype.fintype _

local instance : Fintype (Equiv.Perm a7V) := inferInstance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem a7V_permutation_normalizer_certificate :
    ∀ a : Equiv.Perm a7V, a 1 = 1 → ∃ x : ASevenCertificateGroup,
      (x * a7a * x⁻¹ = a7a ∨ x * a7a * x⁻¹ = a7a ^ 2) ∧
      ∀ v : a7V, (a v : ASevenCertificateGroup) = x * (v : ASevenCertificateGroup) * x⁻¹ := by
  exact Certificates.certificate112

theorem a7V_fullAutomorphismImage :
    FullAutomorphismImage (Subgroup.normalizer (a7U : Set ASevenCertificateGroup) ⊓
      Subgroup.normalizer (a7V : Set ASevenCertificateGroup)) a7V := by
  intro a
  obtain ⟨x, hx, ha⟩ := a7V_permutation_normalizer_certificate a.toEquiv (a.map_one)
  change ∀ v : a7V, (a v : ASevenCertificateGroup) =
    x * (v : ASevenCertificateGroup) * x⁻¹ at ha
  have hxU : x ∈ Subgroup.normalizer (a7U : Set ASevenCertificateGroup) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have heq : a7U = Subgroup.zpowers a7a := by
      apply le_antisymm
      · intro y hy
        change y = 1 ∨ y = a7a ∨ y = a7a ^ 2 at hy
        rcases hy with rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
        · exact (Subgroup.zpowers a7a).pow_mem (Subgroup.mem_zpowers _) _
      · exact Subgroup.zpowers_le.mpr (by
          change a7a = 1 ∨ a7a = a7a ∨ a7a = a7a ^ 2
          exact Or.inr (Or.inl rfl))
    rw [heq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (x * a7a * x⁻¹) = Subgroup.zpowers a7a
    rcases hx with h | h
    · rw [h]
    · rw [h, show a7a ^ 2 = a7a⁻¹ by decide, Subgroup.zpowers_inv]
  have hxV : x ∈ Subgroup.normalizer (a7V : Set ASevenCertificateGroup) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have h := ha ⟨v, hv⟩
      rw [← h]
      exact (a ⟨v, hv⟩).property
    · intro hv
      let w : a7V := ⟨x * v * x⁻¹, hv⟩
      have h := ha (a.symm w)
      have heq : x * (a.symm w : ASevenCertificateGroup) * x⁻¹ = x * v * x⁻¹ := by
        simpa only [MulEquiv.apply_symm_apply] using h.symm
      have heq' : (a.symm w : ASevenCertificateGroup) = v := (MulAut.conj x).injective heq
      rw [← heq']
      exact (a.symm w).property
  exact ⟨x, ⟨hxU, hxV⟩, ha⟩

theorem a7U_fourgroup_fullAutomorphismImage (V : Subgroup ASevenCertificateGroup)
    (hV : IsKleinFour V) (hcent : V ≤ Subgroup.centralizer (a7U : Set ASevenCertificateGroup)) :
    FullAutomorphismImage (Subgroup.normalizer (a7U : Set ASevenCertificateGroup) ⊓
      Subgroup.normalizer (V : Set ASevenCertificateGroup)) V := by
  rw [kleinFour_eq_a7V_of_centralizes_a7U V hV hcent]
  exact a7V_fullAutomorphismImage

end CFSG.GorensteinWalter
