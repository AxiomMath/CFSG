module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.Triality.HeightLayers
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality

abbrev D4Vec := Fin TwistTag.D4.tag.rank → ℤ

@[expose] def orbA : Finset D4Vec := {![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]}
@[expose] def orbB : Finset D4Vec := {![0, 0, 1, 0]}
@[expose] def orbC : Finset D4Vec := {![1, 0, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 1]}
@[expose] def orbD : Finset D4Vec := {![1, 1, 1, 0], ![0, 1, 1, 1], ![1, 0, 1, 1]}
@[expose] def orbE : Finset D4Vec := {![1, 1, 1, 1]}
@[expose] def orbF : Finset D4Vec := {![1, 1, 2, 1]}

@[expose] def orbitTable (h : ℤ) : Finset (Finset D4Vec) :=
  if h = 1 then {orbA, orbB} else if h = 2 then {orbC} else if h = 3 then {orbD}
    else if h = 4 then {orbE} else if h = 5 then {orbF} else ∅

@[expose] def orbitWeight (O : Finset D4Vec) : ℕ := if O.card = 1 then 1 else 2

theorem orbit_of_root_table : ∀ α ∈ rootFinset TwistTag.D4.tag, 0 < height α →
    TwistTag.D4.diagramOrbit α ∈ orbitTable (height α) := by
  decide +kernel

theorem table_orbit_exists : ∀ h ∈ ({1, 2, 3, 4, 5} : Finset ℤ), ∀ O ∈ orbitTable h,
    ∃ α ∈ rootFinset TwistTag.D4.tag, height α = h ∧ TwistTag.D4.diagramOrbit α = O := by
  decide +kernel

theorem sum_orbitWeight_five :
    ∑ k ∈ Finset.range 5, ∑ O ∈ orbitTable ((k + 1 : ℕ) : ℤ), orbitWeight O = 9 := by
  decide +kernel


theorem orbitsAt_D4_eq (h : ℤ) (hh : 0 < h) :
    orbitsAt TwistTag.D4 h = orbitTable h := by
  ext O
  rw [mem_orbitsAt]
  constructor
  · rintro ⟨α, hα, hαh, rfl⟩
    have hpos : 0 < height α := by rw [hαh]; exact hh
    have := orbit_of_root_table α (mem_rootFinset.2 hα) hpos
    rwa [hαh] at this
  · intro hO
    have h5 : h ∈ ({1, 2, 3, 4, 5} : Finset ℤ) := by
      by_contra hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [orbitTable, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2] at hO
    obtain ⟨α, hα, hαh, hαO⟩ := table_orbit_exists h h5 O hO
    exact ⟨α, mem_rootFinset.1 hα, hαh, hαO⟩

theorem sum_orbitWeight_le (N : ℕ) :
    ∑ k ∈ Finset.range N, ∑ O ∈ orbitTable ((k + 1 : ℕ) : ℤ), orbitWeight O ≤ 9 := by
  have hz : ∀ k, 5 ≤ k → ∑ O ∈ orbitTable ((k + 1 : ℕ) : ℤ), orbitWeight O = 0 := by
    intro k hk
    have : orbitTable ((k + 1 : ℕ) : ℤ) = ∅ := by
      have h1 : ((k + 1 : ℕ) : ℤ) ≠ 1 := by omega
      have h2 : ((k + 1 : ℕ) : ℤ) ≠ 2 := by omega
      have h3 : ((k + 1 : ℕ) : ℤ) ≠ 3 := by omega
      have h4 : ((k + 1 : ℕ) : ℤ) ≠ 4 := by omega
      have h5 : ((k + 1 : ℕ) : ℤ) ≠ 5 := by omega
      rw [orbitTable, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
    rw [this]; rfl
  by_cases hN : N ≤ 5
  · calc ∑ k ∈ Finset.range N, ∑ O ∈ orbitTable ((k + 1 : ℕ) : ℤ), orbitWeight O
        ≤ ∑ k ∈ Finset.range 5, ∑ O ∈ orbitTable ((k + 1 : ℕ) : ℤ), orbitWeight O :=
          Finset.sum_le_sum_of_subset (Finset.range_mono hN)
      _ = 9 := sum_orbitWeight_five
  · obtain ⟨m, rfl⟩ : ∃ m, N = 5 + m := ⟨N - 5, by omega⟩
    rw [Finset.sum_range_add, sum_orbitWeight_five]
    have : ∑ x ∈ Finset.range m, ∑ O ∈ orbitTable ((5 + x + 1 : ℕ) : ℤ), orbitWeight O = 0 :=
      Finset.sum_eq_zero fun x _ => by
        have := hz (5 + x) (by omega)
        simpa using this
    rw [this]

end CFSG.HardMathSupport.Lang.E27Lie
