module

public import CFSG.LocalAnalysis.LargeEvenClassification.PrimeComplementCore

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

@[expose] noncomputable def deltaIntersection {Ambient : Type groupUniverse} [Group Ambient]
    (prime : ℕ) (Plane : Subgroup Ambient) : Subgroup Ambient :=
  ⨅ element : Ambient, ⨅ (_ : element ∈ Plane), ⨅ (_ : element ≠ 1),
    primeComplementCoreOf prime (Subgroup.centralizer {element})

theorem delta_le_element_core {Ambient : Type groupUniverse} [Group Ambient]
    (prime : ℕ) (Plane : Subgroup Ambient) (element : Ambient)
    (helement : element ∈ Plane) (hnonidentity : element ≠ 1) :
    deltaIntersection prime Plane ≤
      primeComplementCoreOf prime (Subgroup.centralizer {element}) :=
  iInf_le_of_le element (iInf_le_of_le helement (iInf_le _ hnonidentity))

theorem delta_le_centralizer {Ambient : Type groupUniverse} [Group Ambient]
    (prime : ℕ) (Plane : Subgroup Ambient) :
    deltaIntersection prime Plane ≤ Subgroup.centralizer (Plane : Set Ambient) := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  by_cases hidentity : other = 1
  · simp [hidentity]
  · have hcentralizes := (primeComplementCoreOf_le prime (Subgroup.centralizer {other}))
      (delta_le_element_core prime Plane other hother hidentity helement)
    exact Subgroup.mem_centralizer_iff.mp hcentralizes other (Set.mem_singleton other)

theorem delta_order {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Plane : Subgroup Ambient) (hnontrivial : Plane ≠ ⊥) :
    ¬prime ∣ Nat.card (deltaIntersection prime Plane) := by
  obtain ⟨element, hnonidentity⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnontrivial
  have hvalueNe : element.val ≠ 1 := fun hvalue => hnonidentity (Subtype.ext hvalue)
  exact fun hdivides => primeComplementCoreOf_order hprime (Subgroup.centralizer {element.val})
    (hdivides.trans (Subgroup.card_dvd_of_le
      (delta_le_element_core prime Plane element.val element.property hvalueNe)))

theorem delta_map_le {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime : ℕ}
    (hprime : prime.Prime) (coordinates : Ambient ≃* Target) (Plane : Subgroup Ambient) :
    (deltaIntersection prime Plane).map coordinates.toMonoidHom ≤
      deltaIntersection prime (Plane.map coordinates.toMonoidHom) := by
  intro mappedElement hmappedElement
  obtain ⟨element, helement, rfl⟩ := hmappedElement
  simp only [deltaIntersection, Subgroup.mem_iInf]
  intro mappedOther hmappedOther hnonidentity
  obtain ⟨other, hother, rfl⟩ := hmappedOther
  have hotherNe : other ≠ 1 := fun hidentity => hnonidentity (by rw [hidentity, map_one])
  have hcore := primeComplementCoreOf_map_mulEquiv hprime coordinates (Subgroup.centralizer {other})
  rw [centralizer_set_map_mulEquiv, Set.image_singleton] at hcore
  change coordinates element ∈ primeComplementCoreOf prime (Subgroup.centralizer {coordinates other})
  rw [← hcore]
  exact ⟨element, delta_le_element_core prime Plane other hother hotherNe helement, rfl⟩

theorem delta_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime : ℕ}
    (hprime : prime.Prime) (coordinates : Ambient ≃* Target) (Plane : Subgroup Ambient) :
    (deltaIntersection prime Plane).map coordinates.toMonoidHom =
      deltaIntersection prime (Plane.map coordinates.toMonoidHom) := by
  apply le_antisymm (delta_map_le hprime coordinates Plane)
  have hinverse := Subgroup.map_mono (f := coordinates.toMonoidHom)
    (delta_map_le hprime coordinates.symm (Plane.map coordinates.toMonoidHom))
  rw [subgroup_map_inverse_mulEquiv, subgroup_map_forward_inverse_mulEquiv] at hinverse
  exact hinverse

theorem delta_normalized_by_plane_normalizer {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Plane : Subgroup Ambient) :
    Subgroup.normalizer (Plane : Set Ambient) ≤
      Subgroup.normalizer (deltaIntersection prime Plane : Set Ambient) := by
  intro conjugator hconjugator
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hplane := Subgroup.mem_normalizer_iff_map_conj_eq.mp hconjugator
  have hdelta := delta_map_mulEquiv hprime (MulAut.conj conjugator) Plane
  simpa only [MulEquiv.toMonoidHom_eq_coe, hplane] using hdelta

theorem abelian_overgroup_normalizes_delta {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Plane Elementary : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hplaneLe : Plane ≤ Elementary) :
    Elementary ≤ Subgroup.normalizer (deltaIntersection prime Plane : Set Ambient) := by
  have hcentralizes : Elementary ≤ Subgroup.centralizer (Plane : Set Ambient) := by
    intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    exact congrArg (fun entry : Elementary => entry.val)
      (@mul_comm' Elementary _ helementary.1 ⟨other, hplaneLe hother⟩ ⟨element, helement⟩)
  exact hcentralizes.trans ((Subgroup.centralizer_le_normalizer (Plane : Set Ambient)).trans
    (delta_normalized_by_plane_normalizer hprime Plane))

theorem commutator_le_of_normalized {Ambient : Type groupUniverse} [Group Ambient]
    (Invariant Acting : Subgroup Ambient)
    (hnormalizes : Acting ≤ Subgroup.normalizer (Invariant : Set Ambient)) :
    ⁅Invariant, Acting⁆ ≤ Invariant := by
  apply Subgroup.commutator_le.mpr
  intro element helement conjugator hconjugator
  rw [commutatorElement_def]
  have hconjugate := (Subgroup.mem_normalizer_iff.mp (hnormalizes hconjugator)
    element⁻¹).mp (Invariant.inv_mem helement)
  simpa only [mul_assoc] using Invariant.mul_mem helement hconjugate

theorem normalizes_commutator_of_normalized {Ambient : Type groupUniverse} [Group Ambient]
    (Invariant Acting : Subgroup Ambient)
    (hnormalizes : Acting ≤ Subgroup.normalizer (Invariant : Set Ambient)) :
    Acting ≤ Subgroup.normalizer ((⁅Invariant, Acting⁆ : Subgroup Ambient) : Set Ambient) := by
  intro conjugator hconjugator
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormalizes hconjugator),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hconjugator)]

end CFSG.LargeEvenClassification.Helpers
