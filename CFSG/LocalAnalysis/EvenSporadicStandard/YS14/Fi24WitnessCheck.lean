module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24WitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.WitnessLemma
public import CFSG.Sporadic.Fi24.OctadAction

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24)
open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction


@[expose] noncomputable def commD24 (r : R) : Set R := {u | u ∈ D24 ∧ r * u = u * r}

theorem mem_commD24 {r u : R} : u ∈ commD24 r ↔ u ∈ D24 ∧ r * u = u * r := Iff.rfl

theorem mul_self_of_mem_D24 {x : R} (hx : x ∈ D24) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  calc c * tR * c⁻¹ * (c * tR * c⁻¹) = c * (tR * tR) * c⁻¹ := by group
    _ = 1 := by rw [CFSG.Sporadic.Fi24.tR_mul_tR, mul_one, mul_inv_cancel]

theorem conj_mem_D24 {x : R} (hx : x ∈ D24) (g : R) : g * x * g⁻¹ ∈ D24 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  refine isConj_iff.2 ⟨g * c, ?_⟩
  group

theorem cls_not_mem_JR (k : Fin 306936) : cls k ∉ JR := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Sporadic.Fi24.cls_mem k)
  apply CFSG.Sporadic.Fi24.tR_not_mem_JR
  have h' := CFSG.Sporadic.Fi24.normal_JR.conj_mem _ h c⁻¹
  rwa [← hc, show c⁻¹ * (c * tR * c⁻¹) * c⁻¹⁻¹ = tR by group] at h'

theorem evenSub_clsSet_le_JR (Q : List (Fin 306936)) : evenSub (clsSet Q) ≤ JR := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨p, ⟨a, -, rfl⟩, q, ⟨b, -, rfl⟩, rfl⟩
  exact (Subgroup.mul_mem_iff_of_index_two CFSG.Sporadic.Fi24.index_JR).2
    (iff_of_false (cls_not_mem_JR a) (cls_not_mem_JR b))

theorem evenSub_clsSet_le_centralizer {r : R} {Q : List (Fin 306936)}
    (h : ∀ q ∈ Q, r * cls q = cls q * r) :
    evenSub (clsSet Q) ≤ Subgroup.centralizer ({r} : Set R) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨p, ⟨a, ha, rfl⟩, q, ⟨b, hb, rfl⟩, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.2
  exact ((show Commute r (cls a) from h a ha).mul_right (show Commute r (cls b) from h b hb)).symm

theorem fourClassesLarge_of_witFacts {r : R} (hW : WitFacts r)
    (hleaf : r * r = 1 → r ≠ 1 → ∀ u ∈ D24, r * u = u * r → r ≠ u →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({u} : Set R)))
    (hleafJ : r ∈ JR → r * r = 1 → r ≠ 1 → ∀ u ∈ D24, r * u = u * r →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set R) ⊓ JR ⊓ Subgroup.centralizer ({u} : Set R))) :
    CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set R)) ∧
      (r ∈ JR → CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set R) ⊓ JR)) := by
  obtain ⟨hrr, hr1, Q, q₀, hq₀, hrQ, hrq, hperf, hcov⟩ := hW
  have hPK := evenSub_clsSet_le_centralizer hrQ
  have hPJ : evenSub (clsSet Q) ≤ Subgroup.centralizer ({r} : Set R) ⊓ JR :=
    le_inf hPK (evenSub_clsSet_le_JR Q)
  have hQC : clsSet Q ⊆ commD24 r := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_commD24.2 ⟨CFSG.Sporadic.Fi24.cls_mem q, hrQ q hq⟩
  have hq0Q : cls q₀ ∈ clsSet Q := ⟨q₀, hq₀, rfl⟩
  have hCsq : ∀ u ∈ commD24 r, u * u = 1 := fun u hu => mul_self_of_mem_D24 (mem_commD24.1 hu).1
  have hCK : ∀ x ∈ Subgroup.centralizer ({r} : Set R), ∀ u ∈ commD24 r,
      x * u * x⁻¹ ∈ commD24 r := by
    intro x hx u hu
    have hxr : r * x = x * r := Subgroup.mem_centralizer_iff.1 hx r rfl
    obtain ⟨hu24, hur⟩ := mem_commD24.1 hu
    refine mem_commD24.2 ⟨conj_mem_D24 hu24 x, ?_⟩
    have hxinv : x⁻¹ * r = r * x⁻¹ := by
      calc x⁻¹ * r = x⁻¹ * (r * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * r) * x⁻¹ := by rw [hxr]
        _ = r * x⁻¹ := by group
    calc r * (x * u * x⁻¹) = (r * x) * u * x⁻¹ := by group
      _ = (x * r) * u * x⁻¹ := by rw [hxr]
      _ = x * (r * u) * x⁻¹ := by group
      _ = x * (u * r) * x⁻¹ := by rw [hur]
      _ = x * u * (r * x⁻¹) := by group
      _ = x * u * (x⁻¹ * r) := by rw [hxinv]
      _ = x * u * x⁻¹ * r := by group
  have hcover : ∀ p ∈ commD24 r, p ≠ cls q₀ →
      ∃ q ∈ clsSet Q, q * cls q₀ * p ∉ commD24 r := by
    intro p hp hpne
    obtain ⟨hpD, hpc⟩ := mem_commD24.1 hp
    obtain ⟨q, hq, hne⟩ := hcov p hpD hpc hpne
    exact ⟨cls q, ⟨q, hq, rfl⟩, fun hmem => hne (hCsq _ hmem)⟩
  have hq₀D := CFSG.Sporadic.Fi24.cls_mem q₀
  refine ⟨?_, fun hrJ => ?_⟩
  · exact fourClassesLarge_of_witness (K := Subgroup.centralizer ({r} : Set R))
      (commD24 r) (clsSet Q) hCsq hCK hQC hPK hperf hq0Q hcover
      (hleaf hrr hr1 (cls q₀) hq₀D (hrQ q₀ hq₀) hrq)
  · exact fourClassesLarge_of_witness (K := Subgroup.centralizer ({r} : Set R) ⊓ JR)
      (commD24 r) (clsSet Q) hCsq (fun x hx => hCK x (Subgroup.mem_inf.1 hx).1) hQC
      hPJ hperf hq0Q hcover (hleafJ hrJ hrr hr1 (cls q₀) hq₀D (hrQ q₀ hq₀))

end CFSG.EvenSporadicStandard.YS14

end
