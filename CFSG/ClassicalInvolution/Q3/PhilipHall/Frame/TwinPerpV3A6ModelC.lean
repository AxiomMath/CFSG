module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelBasic
public import Certificates.Certificate517502

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.EvenSmallLie.OmegaEight
  Certificates.AE6Model Certificates.S7Twin CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

theorem ae6ModelC3_proved : AE6ModelC3 := by
  intro y hy hyP
  obtain ⟨Y, hY, hYy⟩ := exists_allTables degree_lt wQ_valid (mem_wQ y hy)
  have h : ((allTables (wQ ())).all fun Y => memT 360 (allTables (plQ ())) Y ||
      ((c3Perms ()).map fun h => toTable (h⁻¹ * z0 () * h)).any fun T =>
        tblEq 360 (compT 360 Y Y) T) = true := Certificates.certificate517502.1
  rw [List.all_eq_true] at h
  have h1 := h Y hY
  rw [Bool.or_eq_true, List.any_eq_true] at h1
  rcases h1 with h1 | ⟨T, hT, h2⟩
  · exact absurd (le_ae6ModelP y (mem_of_memT_allTables degree_lt plQ_valid hYy h1)) hyP
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hT
    have hgm : g ∈ omegaT := by
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
      exact evalCodes_mem_omegaT w
    refine ⟨⟨g, hgm⟩, Subtype.ext ?_⟩
    rw [tblEq_iff_eq (Rep.compT hYy hYy) (rep_toTable degree_lt _)] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ae6ModelZ, pow_two]
    exact h2

theorem ae6ModelC1_inv_proved :
    ⨆ (h : AE6Om) (_ : h⁻¹ * ae6ModelZ * h ∈ ae6ModelP), conjSub h⁻¹ ae6ModelP = ⊤ := by
  have h : ((c1iPerms ()).length == 8 && (List.range 8).all fun i =>
      memT 360 (allTables (plQ ())) (toTable (((c1iPerms ()).getD i 1)⁻¹ * z0 () *
        (c1iPerms ()).getD i 1)) &&
      memT 360 (allTables (plQ ())) (toTable ((c1iPerms ()).getD i 1 *
        (curtisPerms ()).getD i 1 * ((c1iPerms ()).getD i 1)⁻¹))) = true :=
    Certificates.certificate517502.2.2
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨-, h⟩ := h
  have h : ∀ i < 8, _ := fun i hi => Bool.and_eq_true _ _ ▸ h i (List.mem_range.mpr hi)
  rw [eq_top_iff, ← A6.closure_curtisGen, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hi := h i.val i.2
  set g := (c1iPerms ()).getD i.val 1 with hgdef
  have hgm : g ∈ omegaT := by
    rw [hgdef, List.getD_eq_getElem?_getD]
    cases hc : (c1iPerms ())[i.val]? with
    | none => exact omegaT.one_mem
    | some c =>
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hc)
      exact evalCodes_mem_omegaT w
  set h' : AE6Om := ⟨g, hgm⟩
  have hz : h'⁻¹ * ae6ModelZ * h' ∈ ae6ModelP := by
    refine le_ae6ModelP _ (mem_of_memT_allTables degree_lt plQ_valid (rep_toTable degree_lt _) ?_)
    simpa [h', coe_ae6ModelZ] using hi.1
  have hc : h' * A6.curtisGen i * h'⁻¹ ∈ ae6ModelP := by
    refine le_ae6ModelP _ (mem_of_memT_allTables degree_lt plQ_valid (rep_toTable degree_lt _) ?_)
    have h2 := hi.2
    rw [curtisPerms_getD i.2] at h2
    have hcg : ((A6.curtisGen i : AE6Om) : Equiv.Perm (Fin 360)) = gen i.val := rfl
    simpa [h', hcg] using h2
  refine Subgroup.mem_iSup_of_mem h' (Subgroup.mem_iSup_of_mem hz ?_)
  rw [mem_conjSub_iff, inv_inv]
  exact hc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
