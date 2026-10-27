module

public import Certificates.Certificate786001
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SuzModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.GSThmB.CF23L34
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

private theorem sY2_mem_suzL : sY2 ∈ suzL :=
  ⟨PresentedGroup.of 1, by rw [lam_of]; simp [sGen]⟩

theorem sup_suzL_map_conj_sMm_eq_suzM :
    suzL ⊔ suzL.map (MulAut.conj sMm).toMonoidHom = suzM := by
  have hMle : suzM ≤ Subgroup.closure {sY1, sY2, sMm * sY1 * sMm⁻¹, sMm * sY2 * sMm⁻¹} :=
    Certificates.certificate786001
  have hLM : suzL ≤ suzM := fun x hx => (suzL_le_centM hx).2
  have hHmem : {sY1, sY2, sMm * sY1 * sMm⁻¹, sMm * sY2 * sMm⁻¹} ⊆
      ((suzL ⊔ suzL.map (MulAut.conj sMm).toMonoidHom : Subgroup (Equiv.Perm (Fin 1782))) :
        Set (Equiv.Perm (Fin 1782))) := by
    intro g hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left sY1_mem
    · exact Subgroup.mem_sup_left sY2_mem_suzL
    · exact Subgroup.mem_sup_right (Subgroup.mem_map.2 ⟨sY1, sY1_mem, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.mem_map.2 ⟨sY2, sY2_mem_suzL, rfl⟩)
  have hMH : suzM ≤ suzL ⊔ suzL.map (MulAut.conj sMm).toMonoidHom :=
    le_trans hMle ((Subgroup.closure_le _).2 hHmem)
  have hHle : suzL ⊔ suzL.map (MulAut.conj sMm).toMonoidHom ≤ suzM := by
    refine sup_le hLM ?_
    rintro y ⟨x, hx, rfl⟩
    exact suzM.mul_mem (suzM.mul_mem sMm_mem (hLM hx)) (suzM.inv_mem sMm_mem)
  exact le_antisymm hHle hMH

theorem exists_conj_sup_eq_suzM_of_mem_suzL
    {h : Equiv.Perm (Fin 1782)} (hh : h ∈ suzL)
    (hh2 : h * h = 1) (hh1 : h ≠ 1) :
    ∃ a ∈ suzM, a * suzInv 0 * a⁻¹ = suzInv 0 * h ∧
      suzL ⊔ suzL.map (MulAut.conj a).toMonoidHom = suzM := by
  obtain ⟨ℓ, hℓ, hℓy⟩ := exists_conj_suzL sY1_mem hh sY1_mul_self hh2 sY1_ne_one hh1
  have hLM : suzL ≤ suzM := fun x hx => (suzL_le_centM hx).2
  have haM : ℓ * sMm * ℓ⁻¹ ∈ suzM :=
    suzM.mul_mem (suzM.mul_mem (hLM hℓ) sMm_mem) (suzM.inv_mem (hLM hℓ))
  have hℓt : ℓ * suzInv 0 = suzInv 0 * ℓ :=
    Subgroup.mem_centralizer_singleton_iff.1 (suzL_le_centM hℓ).1
  have hℓt' : ℓ⁻¹ * suzInv 0 * ℓ = suzInv 0 := by
    calc ℓ⁻¹ * suzInv 0 * ℓ = ℓ⁻¹ * (suzInv 0 * ℓ) := by rw [mul_assoc]
      _ = ℓ⁻¹ * (ℓ * suzInv 0) := by rw [← hℓt]
      _ = suzInv 0 := by group
  have hconj : ℓ * sMm * ℓ⁻¹ * suzInv 0 * (ℓ * sMm * ℓ⁻¹)⁻¹ = suzInv 0 * h := by
    calc ℓ * sMm * ℓ⁻¹ * suzInv 0 * (ℓ * sMm * ℓ⁻¹)⁻¹
        = ℓ * (sMm * (ℓ⁻¹ * suzInv 0 * ℓ) * sMm⁻¹) * ℓ⁻¹ := by group
      _ = ℓ * (sMm * suzInv 0 * sMm⁻¹) * ℓ⁻¹ := by rw [hℓt']
      _ = ℓ * (suzInv 0 * sY1) * ℓ⁻¹ := by rw [sMm_conj]
      _ = ℓ * suzInv 0 * sY1 * ℓ⁻¹ := by group
      _ = suzInv 0 * (ℓ * sY1 * ℓ⁻¹) := by rw [hℓt]; group
      _ = suzInv 0 * h := by rw [hℓy]
  have hmapℓ : suzL.map (MulAut.conj ℓ).toMonoidHom = suzL := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact suzL.mul_mem (suzL.mul_mem hℓ hx) (suzL.inv_mem hℓ)
    · intro y hy
      refine ⟨ℓ⁻¹ * y * ℓ, suzL.mul_mem (suzL.mul_mem (suzL.inv_mem hℓ) hy) hℓ, ?_⟩
      show ℓ * (ℓ⁻¹ * y * ℓ) * ℓ⁻¹ = y
      group
  have hmapℓ' : suzL.map (MulAut.conj ℓ⁻¹).toMonoidHom = suzL := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact suzL.mul_mem (suzL.mul_mem (suzL.inv_mem hℓ) hx) hℓ
    · intro y hy
      refine ⟨ℓ * y * ℓ⁻¹, suzL.mul_mem (suzL.mul_mem hℓ hy) (suzL.inv_mem hℓ), ?_⟩
      show ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * ℓ = y
      group
  have hmapM : suzM.map (MulAut.conj ℓ).toMonoidHom = suzM := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact suzM.mul_mem (suzM.mul_mem (hLM hℓ) hx) (suzM.inv_mem (hLM hℓ))
    · intro y hy
      refine ⟨ℓ⁻¹ * y * ℓ, suzM.mul_mem (suzM.mul_mem (suzM.inv_mem (hLM hℓ)) hy)
        (hLM hℓ), ?_⟩
      show ℓ * (ℓ⁻¹ * y * ℓ) * ℓ⁻¹ = y
      group
  have hcomp : (MulAut.conj (ℓ * sMm * ℓ⁻¹)).toMonoidHom =
      (MulAut.conj ℓ).toMonoidHom.comp ((MulAut.conj sMm).toMonoidHom.comp
        (MulAut.conj ℓ⁻¹).toMonoidHom) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hsup : suzL ⊔ suzL.map (MulAut.conj (ℓ * sMm * ℓ⁻¹)).toMonoidHom = suzM := by
    calc suzL ⊔ suzL.map (MulAut.conj (ℓ * sMm * ℓ⁻¹)).toMonoidHom
        = suzL.map (MulAut.conj ℓ).toMonoidHom ⊔
            (suzL.map (MulAut.conj sMm).toMonoidHom).map (MulAut.conj ℓ).toMonoidHom := by
          rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, hmapℓ', hmapℓ]
      _ = (suzL ⊔ suzL.map (MulAut.conj sMm).toMonoidHom).map
            (MulAut.conj ℓ).toMonoidHom := by rw [Subgroup.map_sup]
      _ = suzM.map (MulAut.conj ℓ).toMonoidHom := by
          rw [sup_suzL_map_conj_sMm_eq_suzM]
      _ = suzM := hmapM
  exact ⟨ℓ * sMm * ℓ⁻¹, haM, hconj, hsup⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
