module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.GorensteinWalter.ASevenNormalizerCosetData

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

@[expose] def a7LocalFourgroup (i : Fin 2) : Subgroup ASevenCertificateGroup :=
  kleinFourOfCommutingInvolutions a7t (a7s * a7v ^ i.val)
    (by decide) (by fin_cases i <;> decide)
    (by change a7t * (a7s * a7v ^ i.val) = (a7s * a7v ^ i.val) * a7t
        fin_cases i <;> decide)

theorem a7LocalFourgroup_isKleinFour (i : Fin 2) : IsKleinFour (a7LocalFourgroup i) := by
  apply isKleinFour_kleinFourOfCommutingInvolutions
  · decide
  · fin_cases i <;> decide
  · fin_cases i <;> decide

@[expose] def a7CyclesBy (x : ASevenCertificateGroup) (i : Fin 2) : Prop :=
  (∀ v : ASevenCertificateGroup, v ∈ a7LocalFourgroup i →
    x * v * x⁻¹ ∈ a7LocalFourgroup i) ∧
  x * a7t * x⁻¹ ≠ a7t ∧
  x * (a7s * a7v ^ i.val) * x⁻¹ ≠ a7s * a7v ^ i.val ∧
  x * (a7t * (a7s * a7v ^ i.val)) * x⁻¹ ≠ a7t * (a7s * a7v ^ i.val)

@[expose] def a7CycleWordOne (x : ASevenCertificateGroup) : ASevenCertificateGroup :=
  x * a7a * a7v * x * x * a7a * x * a7a * x

@[expose] def a7CycleWordTwo (x : ASevenCertificateGroup) : ASevenCertificateGroup :=
  x * a7a * x * a7v * a7a * x * a7a * x

instance a7LocalFourgroup_decidable (i : Fin 2) :
    DecidablePred (fun v : ASevenCertificateGroup => v ∈ a7LocalFourgroup i) := by
  intro v
  change Decidable (v ∈ ({a7t * (a7s * a7v ^ i.val), a7t, a7s * a7v ^ i.val, 1} : Set ASevenCertificateGroup))
  infer_instance

instance a7CyclesBy_decidable (x : ASevenCertificateGroup) (i : Fin 2) :
    Decidable (a7CyclesBy x i) := by
  unfold a7CyclesBy
  infer_instance

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
theorem a7_cycle_words_certificate : ∀ x : ASevenCertificateGroup,
    a7CyclesBy x 0 → a7CyclesBy (a7CycleWordOne x) 1 ∨ a7CyclesBy (a7CycleWordTwo x) 1 := by
  decide +kernel

theorem a7CyclesBy_iff (H : Subgroup ASevenCertificateGroup) (i : Fin 2) :
    Cycles H (a7LocalFourgroup i) ↔ ∃ x ∈ H, a7CyclesBy x i := by
  constructor
  · rintro ⟨x, hxH, hxN, hxmove⟩
    refine ⟨x, hxH, fun v hv => (Subgroup.mem_normalizer_iff.mp hxN v).mp hv, ?_, ?_, ?_⟩
    · apply hxmove
      · change a7t ∈ ({a7t * (a7s * a7v ^ i.val), a7t, a7s * a7v ^ i.val, 1} : Set ASevenCertificateGroup)
        simp
      · decide
    · apply hxmove
      · change a7s * a7v ^ i.val ∈ ({a7t * (a7s * a7v ^ i.val), a7t, a7s * a7v ^ i.val, 1} : Set ASevenCertificateGroup)
        simp
      · fin_cases i <;> decide
    · apply hxmove
      · change a7t * (a7s * a7v ^ i.val) ∈ ({a7t * (a7s * a7v ^ i.val), a7t, a7s * a7v ^ i.val, 1} : Set ASevenCertificateGroup)
        simp
      · fin_cases i <;> decide
  · rintro ⟨x, hxH, hxN, hxt, hxs, hxts⟩
    refine ⟨x, hxH, Subgroup.mem_normalizer_fintype hxN, ?_⟩
    intro v hv hv1
    change v ∈ ({a7t * (a7s * a7v ^ i.val), a7t, a7s * a7v ^ i.val, 1} : Set ASevenCertificateGroup) at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hxts
    · exact hxt
    · exact hxs
    · exact (hv1 rfl).elim

theorem a7_cycle_opposite_of_contains_U (H : Subgroup ASevenCertificateGroup)
    (hSH : a7S ≤ H) (hUH : a7U ≤ H) (hc : Cycles H (a7LocalFourgroup 0)) :
    Cycles H (a7LocalFourgroup 1) := by
  obtain ⟨x, hxH, hx⟩ := (a7CyclesBy_iff H 0).mp hc
  have haH : a7a ∈ H := hUH (by rw [a7U_eq_zpowers]; exact Subgroup.mem_zpowers _)
  have hvH : a7v ∈ H := hSH a7S_mem_v
  have hword1 : a7CycleWordOne x ∈ H := by
    unfold a7CycleWordOne
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem (H.mul_mem (H.mul_mem hxH haH) hvH) hxH) hxH) haH) hxH) haH) hxH
  have hword2 : a7CycleWordTwo x ∈ H := by
    unfold a7CycleWordTwo
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem (H.mul_mem hxH haH) hxH) hvH) haH) hxH) haH) hxH
  apply (a7CyclesBy_iff H 1).mpr
  rcases a7_cycle_words_certificate x hx with h1 | h2
  · exact ⟨a7CycleWordOne x, hword1, h1⟩
  · exact ⟨a7CycleWordTwo x, hword2, h2⟩

end CFSG.DihedralBlueprint
