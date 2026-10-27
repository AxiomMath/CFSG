module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaIntersection

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def thetaPlaneIntersection {G : Type u} [Group G] (prime : ℕ)
    (plane : Subgroup G) : Subgroup G :=
  ⨅ (element : G) (_ : element ∈ plane) (_ : element ≠ 1),
    thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))

@[expose] noncomputable def thetaPlaneCommutators {G : Type u} [Group G] (prime : ℕ)
    (plane : Subgroup G) : Subgroup G :=
  ⨆ (element : G) (_ : element ∈ plane) (_ : element ≠ 1),
    ⁅thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)), plane⁆

@[expose] noncomputable def thetaPlaneAlpha {G : Type u} [Group G] (prime : ℕ)
    (plane : Subgroup G) : Subgroup G :=
  thetaPlaneCommutators prime plane ⊔ thetaPlaneIntersection prime plane

theorem normalizer_le_normalizer_thetaCoreOf {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤
      Subgroup.normalizer (thetaCoreOf prime subgroup : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro element hnormalizer other hother
  obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hother
  let automorphism := subgroup.normalizerMonoidHom ⟨element, hnormalizer⟩
  have hfixed := Subgroup.characteristic_iff_map_eq.mp
    (solvablePrimeComplementCore_characteristic subgroup prime hprime) automorphism
  have hmem := Subgroup.mem_map_of_mem automorphism.toMonoidHom hpreimage
  rw [hfixed] at hmem
  apply Subgroup.mem_map.mpr
  refine ⟨automorphism preimage, hmem, ?_⟩
  exact Subgroup.normalizerMonoidHom_apply_apply_coe subgroup ⟨element, hnormalizer⟩ preimage

theorem commutative_plane_le_element_centralizer {G : Type u} [Group G]
    (plane : Subgroup G) (hcomm : IsMulCommutative plane) (element : G) (hmem : element ∈ plane) :
    plane ≤ Subgroup.centralizer ({element} : Set G) := by
  intro other hother
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have heq : member = element := Set.mem_singleton_iff.mp hmember
  subst member
  exact congrArg (fun value : plane => (value : G))
    (isMulCommutative_iff.mp hcomm ⟨element, hmem⟩ ⟨other, hother⟩)

theorem commutative_plane_normalizes_element_theta {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) (hcomm : IsMulCommutative plane)
    (element : G) (hmem : element ∈ plane) :
    plane ≤ Subgroup.normalizer
      (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) : Set G) := by
  exact ((commutative_plane_le_element_centralizer plane hcomm element hmem).trans
    Subgroup.le_normalizer).trans (normalizer_le_normalizer_thetaCoreOf prime hprime _)

theorem normalizes_iInf {G : Type u} [Group G] {index : Sort*}
    (acting : Subgroup G) (family : index → Subgroup G)
    (hnormalizes : ∀ member, acting ≤ Subgroup.normalizer (family member : Set G)) :
    acting ≤ Subgroup.normalizer ((⨅ member, family member : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator element helement
  simp only [Subgroup.mem_iInf] at helement ⊢
  intro member
  exact Subgroup.le_normalizer_iff.mp (hnormalizes member) conjugator hconjugator
    element (helement member)

theorem normalizes_iSup {G : Type u} [Group G] {index : Sort*}
    (acting : Subgroup G) (family : index → Subgroup G)
    (hnormalizes : ∀ member, acting ≤ Subgroup.normalizer (family member : Set G)) :
    acting ≤ Subgroup.normalizer ((⨆ member, family member : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator other hother
  refine Subgroup.iSup_induction family hother
    (C := fun value => conjugator * value * conjugator⁻¹ ∈ ⨆ member, family member) ?_ ?_ ?_
  · intro member value hvalue
    exact Subgroup.mem_iSup_of_mem member
      (Subgroup.le_normalizer_iff.mp (hnormalizes member) conjugator hconjugator value hvalue)
  · simp
  · intro first second hfirst hsecond
    change (MulAut.conj conjugator) (first * second) ∈ _
    rw [map_mul]
    exact (⨆ member, family member).mul_mem hfirst hsecond

theorem thetaPlaneIntersection_normalized {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) (hcomm : IsMulCommutative plane) :
    plane ≤ Subgroup.normalizer (thetaPlaneIntersection prime plane : Set G) := by
  apply normalizes_iInf
  intro element
  apply normalizes_iInf
  intro hmem
  apply normalizes_iInf
  intro _
  exact commutative_plane_normalizes_element_theta prime hprime plane hcomm element hmem

theorem thetaPlaneCommutators_normalized {G : Type u} [Group G]
    (prime : ℕ) (plane : Subgroup G) :
    plane ≤ Subgroup.normalizer (thetaPlaneCommutators prime plane : Set G) := by
  apply normalizes_iSup
  intro element
  apply normalizes_iSup
  intro _
  apply normalizes_iSup
  intro _
  exact Subgroup.normalizer_commutator_ge_right _ plane

theorem thetaPlaneAlpha_normalized {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) (hcomm : IsMulCommutative plane) :
    plane ≤ Subgroup.normalizer (thetaPlaneAlpha prime plane : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator element helement
  have hfirst := thetaPlaneCommutators_normalized prime plane hconjugator
  have hsecond := thetaPlaneIntersection_normalized prime hprime plane hcomm hconjugator
  have hfirstMap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hfirst
  have hsecondMap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hsecond
  have hfixed : (thetaPlaneAlpha prime plane).map (MulAut.conj conjugator).toMonoidHom =
      thetaPlaneAlpha prime plane := by
    rw [thetaPlaneAlpha, Subgroup.map_sup, MulEquiv.toMonoidHom_eq_coe, hfirstMap, hsecondMap]
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj conjugator).toMonoidHom helement
  rw [hfixed] at hmem
  exact hmem

theorem thetaPlaneIntersection_le {G : Type u} [Group G] (prime : ℕ) (plane : Subgroup G)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    thetaPlaneIntersection prime plane ≤ thetaCoreOf prime
      (Subgroup.centralizer ({element} : Set G)) := by
  exact iInf_le_of_le element (iInf_le_of_le hmem (iInf_le_of_le hne le_rfl))

theorem thetaPlaneIntersection_solvable {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    Group.IsSolvable (thetaPlaneIntersection prime plane) := by
  have hle := thetaPlaneIntersection_le prime plane element hmem hne
  have : Group.IsSolvable (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))) :=
    thetaCoreOf_solvable prime hprime _
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem thetaPlaneIntersection_prime_complement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    ¬prime ∣ Nat.card (thetaPlaneIntersection prime plane) := by
  exact fun hdiv => thetaCoreOf_prime_complement prime hprime
    (Subgroup.centralizer ({element} : Set G))
    (hdiv.trans (Subgroup.card_dvd_of_le (thetaPlaneIntersection_le prime plane element hmem hne)))

end CFSG.RankThreeEvenClassification.Helpers
