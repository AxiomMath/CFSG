module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.R0Spec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

section Cert

variable (hP : Nat.card ↥P1408 = 177408000)
  (ι : Multiplicative V6 →* ↥P1408) (hι : ∀ v : V6, ι (Multiplicative.ofAdd v) = iotaFun v)

include hP hι

theorem r0_inter (v : V6) :
    ι (Multiplicative.ofAdd v) ∈ wordSubgroupP nWords1 ↔ bil v (Pi.single 0 1) = 0 := by
  rw [hι v]
  exact (r0Facts hP).r0_inter v

theorem r0_eichler : ∀ r ∈ wordSubgroupP nWords1, ∃ u : V6, bil u (Pi.single 0 1) = 0 ∧
    lam u = 0 ∧ ∀ x : V6, r * ι (Multiplicative.ofAdd x) * r⁻¹ =
      ι (Multiplicative.ofAdd (eichF (Pi.single 0 1) u x)) := by
  intro r hr
  obtain ⟨u, hb, hl, hact⟩ := (r0Facts hP).r0_eichler r hr
  refine ⟨u, hb, hl, fun x => ?_⟩
  rw [hι x, hι (eichF (Pi.single 0 1) u x)]
  exact hact x

theorem r0_surj : ∀ u : V6, bil u (Pi.single 0 1) = 0 → lam u = 0 →
    ∃ r ∈ wordSubgroupP nWords1, ∀ x : V6, r * ι (Multiplicative.ofAdd x) * r⁻¹ =
      ι (Multiplicative.ofAdd (eichF (Pi.single 0 1) u x)) := by
  intro u hbil hlam
  obtain ⟨r, hr, hact⟩ := (r0Facts hP).r0_surj u hbil hlam
  refine ⟨r, hr, fun x => ?_⟩
  rw [hι x, hι (eichF (Pi.single 0 1) u x)]
  exact hact x

theorem r0_le_normalizer : wordSubgroupP nWords1 ≤ normalizer (ι.range : Set ↥P1408) := by
  intro r hr
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · intro hn
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hn
    obtain ⟨u, -, -, hact⟩ := r0_eichler hP ι hι r hr
    rw [← ofAdd_toAdd x] at hx
    have h := hact (Multiplicative.toAdd x)
    rw [hx] at h
    exact MonoidHom.mem_range.2
      ⟨Multiplicative.ofAdd (eichF (Pi.single 0 1) u (Multiplicative.toAdd x)), h.symm⟩
  · intro hn
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hn
    obtain ⟨u, -, -, hact⟩ := r0_eichler hP ι hι r⁻¹ (Subgroup.inv_mem _ hr)
    rw [← ofAdd_toAdd x] at hx
    have h := hact (Multiplicative.toAdd x)
    rw [hx] at h
    refine MonoidHom.mem_range.2
      ⟨Multiplicative.ofAdd (eichF (Pi.single 0 1) u (Multiplicative.toAdd x)), ?_⟩
    rw [← h]
    group

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
