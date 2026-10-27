module

public import CFSG.LargeExtraspecial.S14SMELocal
public import Certificates.Certificate38682
public import CFSG.GF2Type.SmithTypeE.L6.IdGramPhi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.LMod CFSG.SmithL6
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 mem_cMbar)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem trDist2Check_holds : trChkDist2 = true :=
  Certificates.certificate38682

theorem ncard_meetCard_one {i : ℕ} (hi : i < 1395) :
    {j : Fin 1395 | meetCard i j.val = 1}.ncard = 784 := by
  have h := trDist2Check_holds
  simp only [trChkDist2, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hi' := h i hi
  have e : (Finset.univ.filter fun j : Fin 1395 => meetCard i j.val = 1).map Fin.valEmbedding =
      (Finset.range 1395).filter fun j => meetCard i j = 1 := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨hj, hj1⟩
      exact ⟨⟨j, hj⟩, hj1, rfl⟩
  have e2 : ((Finset.range 1395).filter fun j => meetCard i j = 1).card =
      ((List.range 1395).filter fun j => meetCard i j == 1).length := by
    simp only [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    congr 1
  rw [show {j : Fin 1395 | meetCard i j.val = 1} =
      ↑(Finset.univ.filter fun j : Fin 1395 => meetCard i j.val = 1) by ext; simp,
    Set.ncard_coe_finset, ← Finset.card_map Fin.valEmbedding, e, e2, hi']

theorem exists_commute_rhoM_eq (S : Setting G) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (m : S.M)
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) =
      S.cl (h * S.z * h⁻¹)) :
    ∃ c : S.M, Commute (c : G) (h * S.z * h⁻¹) ∧ rhoM S c = rhoM S m := by
  set a := h * S.z * h⁻¹ with ha
  rw [S.ρ_cl m haQ] at hm
  rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG m.2 haQ)).mp hm.symm with h1 | h1
  · refine ⟨m, ?_, rfl⟩
    show (m : G) * a = a * m
    calc (m : G) * a = (m : G) * a * (m : G)⁻¹ * m := by group
      _ = a * m := by rw [h1]
  · have ha1 : a ≠ 1 := SME.ne_one_of_isConj S (isConj_iff.mpr ⟨h, rfl⟩)
    obtain ⟨q, hq, hqa⟩ := SME.exists_conj_eq_mul_z S haQ ha1 hne
    have hqM : q⁻¹ ∈ S.M := S.QG_le_M (S.QG.inv_mem hq)
    refine ⟨⟨q⁻¹, hqM⟩ * m, ?_, ?_⟩
    · have e1 : q⁻¹ * (a * S.z) * q = a := by rw [← hqa]; group
      show q⁻¹ * (m : G) * a = a * (q⁻¹ * m)
      calc q⁻¹ * (m : G) * a = q⁻¹ * ((m : G) * a * (m : G)⁻¹) * q * (q⁻¹ * m) := by group
        _ = q⁻¹ * (a * S.z) * q * (q⁻¹ * m) := by rw [h1]
        _ = a * (q⁻¹ * m) := by rw [e1]
    · have h1' : rhoM S ⟨q⁻¹, hqM⟩ = 1 :=
        Subtype.ext ((S.ρ_eq_one_iff _).mpr (S.QG.inv_mem hq))
      rw [map_mul, h1', one_mul]


section Planes

variable
  (ψ : Mbar0 S ≃* T6)

theorem meetCard_planeHom (m : S.Mbar) (i j : Fin 1395) :
    meetCard (planeHom S ψ m i) (planeHom S ψ m j) = meetCard i j := by
  rw [← ncard_wPlane_inter (planeHom S ψ m i).2 (planeHom S ψ m j).2,
    ← ncard_wPlane_inter i.2 j.2, ← image_wPlane_piM ψ m i, ← image_wPlane_piM ψ m j,
    ← Set.image_inter (piM S ψ m).injective, Set.ncard_image_of_injective _ (piM S ψ m).injective]

theorem planeHom_planeOf_of_commute (hw : S.width = 10) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (c : S.M) (hc : Commute (c : G) (h * S.z * h⁻¹)) :
    planeHom S ψ (rhoM S c) (planeOf S ψ h) = planeOf S ψ h := by
  rw [← planeOf_mul ψ hw haQ hne c]
  refine planeOf_congr ψ (S.Lbar_eq_of_conj_eq ?_)
  calc (c : G) * h * S.z * ((c : G) * h)⁻¹ = (c : G) * (h * S.z * h⁻¹) * (c : G)⁻¹ := by group
    _ = h * S.z * h⁻¹ * (c : G) * (c : G)⁻¹ := by rw [hc.eq]
    _ = h * S.z * h⁻¹ := by group

theorem exists_commute_planeHom [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 10) {h : G}
    (haQ : h * S.z * h⁻¹ ∈ S.QG) (hne : h * S.z * h⁻¹ ≠ S.z) {j j' : Fin 1395}
    (hjj : meetCard (planeOf S ψ h) j = meetCard (planeOf S ψ h) j') :
    ∃ c : S.M, Commute (c : G) (h * S.z * h⁻¹) ∧ planeHom S ψ (rhoM S c) j = j' := by
  have hW := (planeOf S ψ h).2
  obtain ⟨g, hg, hgj⟩ := exists_PA_image hW j.2 j'.2 (by
    rw [ncard_wPlane_inter hW j.2, ncard_wPlane_inter hW j'.2, hjj])
  obtain ⟨m, h0, hm⟩ := exists_rhoM_mem_Mbar0 ψ ⟨g, (mem_PA.1 hg).1⟩
  have hst := (stab_eq I ψ hw haQ hne ⟨rhoM S m, h0⟩).mpr (by rw [hm]; exact hg)
  have hfix := (mem_cMbar.mp hst).2
  obtain ⟨c, hc, hcm⟩ := exists_commute_rhoM_eq S haQ hne m hfix
  refine ⟨c, hc, ?_⟩
  rw [hcm, planeHom_eq_iff]
  have e : piM S ψ (rhoM S m) = g := by
    have := piM_of_mem ψ ⟨rhoM S m, h0⟩
    rw [hm] at this
    exact this
  rw [e]
  exact hgj

end Planes

end CFSG.GF2Type.SmithTypeE.L6
