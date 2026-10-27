module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Data
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Orbits
import all CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Rows
import all CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Data
import all CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Search
import all CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Orbits
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Set.Card

public section

namespace CFSG.LyonsUnitaryFour

@[expose] def lyonsOrbitMomentList : List LyonsMoments := lyonsOrbitReps.map lyonsOrbitMoments

@[expose] def lyonsConfigurationCounts : List (List ℕ) :=
  LyonsLabel.all.map fun c => lyonsOrbitReps.map (lyonsConfiguration c).count

private theorem lyonsOrbitMomentList_ne_zero :
    ∀ w ∈ lyonsOrbitMomentList, w ≠ LyonsMoments.zero := by
  decide +kernel

private theorem lyonsOrbitReps_getElem? : lyonsOrbitReps[68]? = some principalRow := by
  decide +kernel

private theorem search_check :
    ((lyonsSearch (lyonsLevels lyonsOrbitMomentList) lyonsTargetMoments).all fun ks =>
      decide (ks[68]? = some 0) || lyonsConfigurationCounts.contains ks) = true := by
  decide +kernel

private theorem lyonsConfiguration_admissible :
    ∀ c : LyonsLabel, ∀ r ∈ lyonsConfiguration c, r.Admissible := by
  decide +kernel

private theorem lyonsConfiguration_gramSum :
    ∀ c : LyonsLabel, gramSum (lyonsConfiguration c) = lyonsGram := by
  decide +kernel

private theorem lyonsConfiguration_map_rotate :
    ∀ c : LyonsLabel, (lyonsConfiguration c).map LyonsRow.rotate = lyonsConfiguration c := by
  decide +kernel

private theorem principalRow_mem_lyonsConfiguration :
    ∀ c : LyonsLabel, principalRow ∈ lyonsConfiguration c := by
  decide +kernel

private theorem lyonsConfigurationCounts_nodup : lyonsConfigurationCounts.Nodup := by
  decide +kernel

theorem lyonsConfiguration_conditions (c : LyonsLabel) :
    LyonsColumnConditions (lyonsConfiguration c) ∧ principalRow ∈ lyonsConfiguration c :=
  ⟨⟨lyonsConfiguration_admissible c, lyonsConfiguration_gramSum c,
    lyonsConfiguration_map_rotate c⟩, principalRow_mem_lyonsConfiguration c⟩

theorem mem_lyonsConfigurations_of_conditions {M : Multiset LyonsRow}
    (hM : LyonsColumnConditions M) (hp : principalRow ∈ M) : M ∈ lyonsConfigurations := by
  have hsupp : ∀ x ∈ M, x ∈ lyonsAdmissibleRows := fun x hx =>
    mem_lyonsAdmissibleRows (hM.admissible x hx)
  have hcomb := lyonsMultisetMoments_eq_combination hsupp hM.map_rotate
  rw [lyonsMultisetMoments_eq_target hM] at hcomb
  have hmem := mem_lyonsSearch lyonsOrbitMomentList_ne_zero
    (ks := lyonsOrbitReps.map M.count) (by simp [lyonsOrbitMomentList])
  rw [lyonsOrbitMomentList, ← hcomb] at hmem
  have h := search_check
  rw [List.all_eq_true] at h
  have h' := h _ hmem
  have h68 : (lyonsOrbitReps.map M.count)[68]? = some (M.count principalRow) := by
    rw [List.getElem?_map, lyonsOrbitReps_getElem?]
    rfl
  have hne : M.count principalRow ≠ 0 := Multiset.count_ne_zero.mpr hp
  rw [h68] at h'
  simp only [Option.some.injEq, hne, decide_false, Bool.false_or, List.contains_iff_mem] at h'
  obtain ⟨c, -, hc⟩ := List.mem_map.mp h'
  have hc' := lyonsConfiguration_conditions c
  refine ⟨c, eq_of_map_count_lyonsOrbitReps (fun x hx => mem_lyonsAdmissibleRows
    (hc'.1.admissible x hx)) hsupp hc'.1.map_rotate hM.map_rotate hc⟩

theorem lyonsConfiguration_injective : Function.Injective lyonsConfiguration := by
  intro c c' h
  have hn := lyonsConfigurationCounts_nodup
  rw [lyonsConfigurationCounts] at hn
  exact List.inj_on_of_nodup_map hn (LyonsLabel.mem_all c) (LyonsLabel.mem_all c') (by rw [h])

theorem mem_lyonsConfigurations_iff (M : Multiset LyonsRow) :
    M ∈ lyonsConfigurations ↔ LyonsColumnConditions M ∧ principalRow ∈ M := by
  constructor
  · rintro ⟨c, rfl⟩
    exact lyonsConfiguration_conditions c
  · rintro ⟨hM, hp⟩
    exact mem_lyonsConfigurations_of_conditions hM hp

theorem ncard_lyonsConfigurations : lyonsConfigurations.ncard = 27 := by
  rw [lyonsConfigurations, Set.ncard_range_of_injective lyonsConfiguration_injective,
    Nat.card_eq_fintype_card]
  rfl

theorem lyons_integral_column_exhaustive_enumeration :
    (∀ M : Multiset LyonsRow, LyonsColumnConditions M → principalRow ∈ M →
      M ∈ lyonsConfigurations) ∧
    (∀ M ∈ lyonsConfigurations, LyonsColumnConditions M ∧ principalRow ∈ M) ∧
    Function.Injective lyonsConfiguration ∧ lyonsConfigurations.ncard = 27 :=
  ⟨fun _ hM hp => mem_lyonsConfigurations_of_conditions hM hp,
    fun M hM => (mem_lyonsConfigurations_iff M).mp hM, lyonsConfiguration_injective,
    ncard_lyonsConfigurations⟩

end CFSG.LyonsUnitaryFour
