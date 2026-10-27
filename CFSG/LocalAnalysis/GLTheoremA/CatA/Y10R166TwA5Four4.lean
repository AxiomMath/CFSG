module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open TwA5Four

namespace TwA5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot CFSG.SeitzReduction.LinearPilot
open Matrix

variable {F : Type} [Field F]

@[expose] noncomputable def fiveTorusEvalUnit {h : UnitaryFieldData 2 2 F} :
    unitaryTorusParam h ({0, 1} : Finset (Fin 6)) →* Fˣ where
  toFun c := c.1 5
  map_one' := rfl
  map_mul' c d := rfl

private theorem pow_five_eq_one_of_norm_one {h : UnitaryFieldData 2 2 F} {u : Fˣ}
    (hu : h.norm ((u : Fˣ) : F) = 1) : u ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  rw [h.norm_eq_pow] at hu
  norm_num at hu
  exact hu

private theorem range_fiveTorusEvalUnit {h : UnitaryFieldData 2 2 F} :
    (fiveTorusEvalUnit (h := h)).range = rootsOfUnity 5 F := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [mem_rootsOfUnity]
    exact pow_five_eq_one_of_norm_one (c.2.1 5)
  · intro u hu
    have hu5 : (((u : Fˣ) : F)) ^ 5 = 1 := by
      have := (mem_rootsOfUnity 5 u).1 hu
      simpa [Units.val_pow_eq_pow_val] using congrArg (fun v : Fˣ => (v : F)) this
    have hnormu : h.norm ((u : Fˣ) : F) = 1 := unitaryNorm_eq_one_of_pow_five hu5
    refine ⟨⟨![1, 1, 1, 1, (u : Fˣ)⁻¹, (u : Fˣ)], ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro i
        fin_cases i <;>
          simp [h.norm_eq_pow, hu5, hnormu, Units.val_pow_eq_pow_val,
            CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq h]
      · rw [Fin.prod_univ_six]
        dsimp
        change (1 : Fˣ) * 1 * 1 * 1 * (u : Fˣ)⁻¹ * (u : Fˣ) = 1
        simp
      · intro i hi j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl
    · rfl

private theorem card_ker_fiveTorusEvalUnit {h : UnitaryFieldData 2 2 F} :
    Nat.card ↥(fiveTorusEvalUnit (h := h)).ker = 5 ^ 3 := by
  have hcard := Subgroup.card_ker_mul_card_range (fiveTorusEvalUnit (h := h))
  rw [range_fiveTorusEvalUnit, card_rootsOfUnity_five (h := h),
    card_unitaryTorusParam_two (h := h)] at hcard
  have h5 : Nat.card ↥(fiveTorusEvalUnit (h := h)).ker * 5 = 5 ^ 3 * 5 := by
    calc Nat.card ↥(fiveTorusEvalUnit (h := h)).ker * 5 = 5 ^ 4 := hcard
      _ = 5 ^ 3 * 5 := by norm_num
  exact Nat.mul_right_cancel (by norm_num : 0 < 5) h5

noncomputable def fiveTorusParamIncl {h : UnitaryFieldData 2 2 F} :
    unitaryTorusParam h ({0, 1} : Finset (Fin 6)) →*
      unitaryTorusParam h (∅ : Finset (Fin 6)) :=
  Subgroup.inclusion (unitaryTorusParam_anti h (by simp : (∅ : Finset (Fin 6)) ⊆ {0, 1}))

@[simp]
theorem coe_fiveTorusParamIncl {h : UnitaryFieldData 2 2 F}
    (c : unitaryTorusParam h ({0, 1} : Finset (Fin 6))) :
    (fiveTorusParamIncl c).1 = c.1 := by
  rw [fiveTorusParamIncl, Subgroup.coe_inclusion]

@[expose] noncomputable def fiveLineSubgroup (h : UnitaryFieldData 2 2 F) :
    Subgroup (unitarySU 2 2 F 6) :=
  ((fiveTorusEvalUnit (h := h)).ker.map fiveTorusParamIncl).map (torusDiagSU h)

theorem fiveLineSubgroup_le_fiveTorus (h : UnitaryFieldData 2 2 F) :
    fiveLineSubgroup h ≤ unitaryTorusSU h ({0, 1} : Finset (Fin 6)) := by
  rintro A ⟨c, ⟨c0, -, rfl⟩, rfl⟩
  exact (mem_unitaryTorusSU h).2 ⟨fiveTorusParamIncl c0, c0.2, rfl⟩

theorem card_fiveLineSubgroup (h : UnitaryFieldData 2 2 F) :
    Nat.card (fiveLineSubgroup h) = 5 ^ 3 := by
  have hinj : Function.Injective (fiveTorusParamIncl (h := h)) :=
    Subgroup.inclusion_injective _
  rw [fiveLineSubgroup,
    Subgroup.card_map_of_injective (torusDiagSU_injective h),
    Subgroup.card_map_of_injective hinj]
  exact card_ker_fiveTorusEvalUnit (h := h)

theorem isElemAbelian_fiveLineSubgroup (h : UnitaryFieldData 2 2 F) :
    IsElemAbelian 5 (fiveLineSubgroup h) :=
  (isElemAbelian_unitaryTorusSU_two h).mono (fiveLineSubgroup_le_fiveTorus h)

private theorem fiveLineSubgroup_le_unitaryBlock (h : UnitaryFieldData 2 2 F) :
    fiveLineSubgroup h ≤ unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
  rintro A ⟨c, ⟨c0, hc0, rfl⟩, rfl⟩
  have hc05 : c0.1 5 = 1 := hc0
  have hc05F : (((c0.1 5 : Fˣ) : F)) = 1 :=
    congrArg (fun u : Fˣ => (u : F)) hc05
  have hc05' : ((fiveTorusParamIncl c0).1 5 : F) = 1 := by
    change ((c0.1 5 : Fˣ) : F) = 1
    exact hc05F
  rw [mem_unitaryBlock]
  intro i j hij
  rw [coe_torusDiagSU]
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.diagonal_apply, hc05']

theorem fiveLineSubgroup_eq_inf (h : UnitaryFieldData 2 2 F) :
    fiveLineSubgroup h =
      unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ⊓
        unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
  refine le_antisymm (le_inf (fiveLineSubgroup_le_fiveTorus h) (fiveLineSubgroup_le_unitaryBlock h)) ?_
  rintro A ⟨hAB, hAJ⟩
  obtain ⟨c, hc, hcA⟩ := (mem_unitaryTorusSU h).1 hAB
  have hc5 : c.1 5 = 1 := by
    have h1 := (mem_unitaryBlock h).1 hAJ 5 5 (Or.inl (by simp))
    have hmat : (((torusDiagSU h c : unitarySU 2 2 F 6) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) 5 5 = ((c.1 5 : Fˣ) : F) := by
      rw [coe_torusDiagSU, Matrix.diagonal_apply, if_pos rfl]
    rw [← hcA] at h1
    rw [hmat] at h1
    exact Units.ext h1
  let c0 : unitaryTorusParam h ({0, 1} : Finset (Fin 6)) := ⟨c.1, hc⟩
  have hc0 : c0 ∈ (fiveTorusEvalUnit (h := h)).ker := by
    change (c0.1 5 : Fˣ) = 1
    exact hc5
  refine ⟨fiveTorusParamIncl c0, Subgroup.mem_map_of_mem _ hc0, ?_⟩
  rw [← hcA]
  apply Subtype.ext
  apply Units.ext
  rfl

theorem diagFiveLast_mem_fiveLineSubgroup {h : UnitaryFieldData 2 2 F} {ζu : Fˣ}
    (hζu : orderOf ζu = 5) :
    diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ∈ fiveLineSubgroup h := by
  have hz5 : (((ζu : Fˣ) : F)) ^ 5 = 1 := by
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : Fˣ => (u : F)) (zeta_pow_five hζu)
  have hxJ : diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ∈
      unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
    rw [mem_unitaryBlock]
    intro i j hij
    rw [coe_diagFiveLast]
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.diagonal_apply, diagFiveLastEntries, hz5]
  rw [fiveLineSubgroup_eq_inf]
  exact ⟨diagFiveLast_mem_unitaryTorusSU hζu, hxJ⟩

theorem unitaryBlock_two_le_centralizer_fiveLineSubgroup (h : UnitaryFieldData 2 2 F) :
    unitaryBlock h ({0, 1} : Finset (Fin 6)) ≤
      Subgroup.centralizer (fiveLineSubgroup h : Set (unitarySU 2 2 F 6)) := by
  intro l hl
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro e he
  rcases he with ⟨c, ⟨c0, hc0, rfl⟩, rfl⟩
  have hc0I : (fiveTorusParamIncl c0).1 ∈
      unitaryTorusParam h ({0, 1} : Finset (Fin 6)) := c0.2
  exact torusDiagSU_mul_eq_mul_torusDiagSU h (n := 6) hc0I hl

end TwA5Four

end CFSG.LocalAnalysis.GLTheoremA.Y10F
