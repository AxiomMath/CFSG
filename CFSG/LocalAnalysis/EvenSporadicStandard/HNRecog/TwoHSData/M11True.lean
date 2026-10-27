module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Spec2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Sub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import Certificates.Certificate441602
public import CFSG.Sporadic.Bridge.M11CheckInputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.SmallOddCore

theorem m11K_le_P1408 : m11K ≤ P1408 := closure_elemW_le _

theorem elemW_y0_mem : elemW y0Word ∈ m11K := subset_closure ⟨y0Word, by simp, rfl⟩

theorem elemW_v_mem : elemW vWord ∈ m11K := subset_closure ⟨vWord, by simp, rfl⟩

section Cert


theorem orderOf_y0 : orderOf (elemW y0Word) = 11 := Certificates.certificate441602.2.1

theorem isM11Like_m11K : TwoHSData.IsM11Like ↥m11K := by
  obtain ⟨hcard, hy, hv, hnc, -, hord, hi, hiK, hgen2, -⟩ := Certificates.certificate441602
  refine TwoHSData.isM11Like_of_data (y := ⟨elemW y0Word, elemW_y0_mem⟩)
    (v := ⟨elemW vWord, elemW_v_mem⟩) (i := ⟨elemW i0Word, hiK⟩) hcard
    (fun g => by rw [← Subgroup.orderOf_coe]; exact hord g g.2) ?_ ?_
    (closure_pair_subtype_eq_top elemW_y0_mem elemW_v_mem m11K_eq_closure.symm) ?_
    (closure_pair_subtype_eq_top elemW_y0_mem hiK hgen2) ?_
  · rw [Subgroup.orderOf_mk]; exact hy
  · rw [Subgroup.orderOf_mk]; exact hv
  · rw [Subgroup.orderOf_mk]; exact hi
  · exact fun h => hnc (congrArg Subtype.val h)

theorem nonempty_mulEquiv_m11K :
    Nonempty (↥m11K ≃* ↥CFSG.Blueprint.NativeSporadic.M11) := by
  obtain ⟨hcard, -, -, -, hrel, -⟩ := Certificates.certificate441602
  refine nonempty_mulEquiv_native_m11_of_subgroup elemW_y0_mem elemW_v_mem hcard
    m11K_eq_closure.symm ?_
  rw [TauCeti.Sporadic.m11Presentation_relatorLetters]
  exact hrel

theorem m11_classes (hP : Nat.card ↥P1408 = 177408000) :
    elemW n1Word * elemW y0Word * (elemW n1Word)⁻¹ = elemW y0Word ^ 7 ∧
      (∀ g ∈ conjClass P1408 elemZ, m11Prop g) ∧
        ∀ g ∈ conjClass P1408 (elemA * elemZ), m11Prop g := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hn, hz, haz, -⟩ := Certificates.certificate441602
  obtain ⟨⟨hcz, -, -⟩, ⟨hcaz, -, -⟩, -⟩ := invClasses_classSpec hP
  exact ⟨hn, hz hcz, haz hcaz⟩

theorem m11_five :
    orderOf (elemW rho0Word) = 5 ∧ elemW rho0Word ∈ m11K ∧
      (∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ m11K, c * elemW rho0Word * c⁻¹ = elemW rho0Word ^ k) ∧
      elemW cBWord * elemW rho0Word * (elemW cBWord)⁻¹ = elemW fix5B.rep := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h5⟩ := Certificates.certificate441602
  exact h5

end Cert

end CFSG.EvenSporadicStandard.HNRecog
