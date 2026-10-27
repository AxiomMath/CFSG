module

public import CFSG.LocalAnalysis.LargeEvenClassification.InvariantKernel
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeFixedPoints
public import CFSG.LocalAnalysis.LargeEvenClassification.Delta

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem coprime_normalized_fixed_decomposition {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Acting Invariant : Subgroup Ambient)
    (hpacting : IsPGroup prime Acting) (hcoprime : ¬prime ∣ Nat.card Invariant)
    (hnormalizes : Acting ≤ Subgroup.normalizer (Invariant : Set Ambient)) :
    ∀ element : Invariant, ∃ fixed : Invariant,
      fixed.val ∈ Subgroup.centralizer (Acting : Set Ambient) ∧
        ∃ commutator : Invariant,
          commutator.val ∈ (⁅Invariant, Acting⁆ : Subgroup Ambient) ∧ fixed * commutator = element := by
  let Commutators := (⁅Invariant, Acting⁆ : Subgroup Ambient).subgroupOf Invariant
  have hcommutatorsLe : (⁅Invariant, Acting⁆ : Subgroup Ambient) ≤ Invariant :=
    commutator_le_of_normalized Invariant Acting hnormalizes
  let : Commutators.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hcommutatorsLe).mpr
    (Subgroup.normalizer_commutator_ge_left Invariant Acting)
  have hstable : ∀ conjugator : Acting, ∀ element : Ambient, element ∈ Invariant →
      conjugator.val * element * conjugator.val⁻¹ ∈ Invariant := by
    intro conjugator element helement
    exact (Subgroup.mem_normalizer_iff.mp (hnormalizes conjugator.property) element).mp helement
  let action := invariantSubgroupConjugation Acting.subtype Invariant hstable
  let projection := QuotientGroup.mk' Commutators
  have hprojection : ∀ conjugator : Acting, ∀ element : Invariant,
      projection (action conjugator element) = projection element := by
    intro conjugator element
    have hcommutator := Subgroup.commutator_mem_commutator element.property conjugator.property
    have hdifference : (element * (action conjugator element)⁻¹ : Invariant).val =
        ⁅element.val, conjugator.val⁆ := by
      change element.val * (conjugator.val * element.val * conjugator.val⁻¹)⁻¹ = _
      rw [commutatorElement_def]
      group
    have hkernel : element * (action conjugator element)⁻¹ ∈ Commutators := by
      change (element * (action conjugator element)⁻¹ : Invariant).val ∈
        (⁅Invariant, Acting⁆ : Subgroup Ambient)
      rw [hdifference]
      exact hcommutator
    have hzero : projection (element * (action conjugator element)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hkernel
    rw [map_mul, map_inv] at hzero
    exact (mul_inv_eq_one.mp hzero).symm
  intro element
  obtain ⟨fixed, hfixedProjection, hfixed⟩ := coprime_fixed_point_lift hprime hpacting action
    (1 : Acting →* MulAut (Invariant ⧸ Commutators)) projection
    (QuotientGroup.mk'_surjective Commutators) (by
      intro conjugator source
      exact hprojection conjugator source) hcoprime (projection element) (fun _ => rfl)
  obtain ⟨commutator, hcommutator, hequality⟩ :=
    (QuotientGroup.mk'_eq_mk' Commutators).mp hfixedProjection
  refine ⟨fixed, ?_, commutator, hcommutator, hequality⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro conjugator hconjugator
  have hfixedAmbient := congrArg (fun entry : Invariant => entry.val) (hfixed ⟨conjugator, hconjugator⟩)
  change conjugator * fixed.val * conjugator⁻¹ = fixed.val at hfixedAmbient
  exact (mul_inv_eq_iff_eq_mul).mp hfixedAmbient

theorem coprime_normalized_factorization {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Acting Invariant : Subgroup Ambient)
    (hpacting : IsPGroup prime Acting) (hcoprime : ¬prime ∣ Nat.card Invariant)
    (hnormalizes : Acting ≤ Subgroup.normalizer (Invariant : Set Ambient)) :
    Invariant = (Invariant ⊓ Subgroup.centralizer (Acting : Set Ambient)) ⊔
      (⁅Invariant, Acting⁆ : Subgroup Ambient) := by
  apply le_antisymm
  · intro element helement
    obtain ⟨fixed, hfixed, commutator, hcommutator, hequality⟩ :=
      coprime_normalized_fixed_decomposition hprime Acting Invariant hpacting hcoprime hnormalizes
        ⟨element, helement⟩
    have hambientEquality := congrArg (fun entry : Invariant => entry.val) hequality
    change fixed.val * commutator.val = element at hambientEquality
    have hfixedMem : fixed.val ∈ ((Invariant ⊓ Subgroup.centralizer (Acting : Set Ambient)) ⊔
        (⁅Invariant, Acting⁆ : Subgroup Ambient)) :=
      (show Invariant ⊓ Subgroup.centralizer (Acting : Set Ambient) ≤
        (Invariant ⊓ Subgroup.centralizer (Acting : Set Ambient)) ⊔
          (⁅Invariant, Acting⁆ : Subgroup Ambient) from le_sup_left) ⟨fixed.property, hfixed⟩
    have hcommutatorMem : commutator.val ∈ ((Invariant ⊓ Subgroup.centralizer (Acting : Set Ambient)) ⊔
        (⁅Invariant, Acting⁆ : Subgroup Ambient)) :=
      (show (⁅Invariant, Acting⁆ : Subgroup Ambient) ≤
        (Invariant ⊓ Subgroup.centralizer (Acting : Set Ambient)) ⊔
          (⁅Invariant, Acting⁆ : Subgroup Ambient) from le_sup_right) hcommutator
    rw [← hambientEquality]
    exact Subgroup.mul_mem _ hfixedMem hcommutatorMem
  · exact sup_le inf_le_left (commutator_le_of_normalized Invariant Acting hnormalizes)

theorem normalizes_commutator_pair {Ambient : Type groupUniverse} [Group Ambient]
    (Normalizers First Second : Subgroup Ambient)
    (hfirst : Normalizers ≤ Subgroup.normalizer (First : Set Ambient))
    (hsecond : Normalizers ≤ Subgroup.normalizer (Second : Set Ambient)) :
    Normalizers ≤ Subgroup.normalizer ((⁅First, Second⁆ : Subgroup Ambient) : Set Ambient) := by
  intro conjugator hconjugator
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hfirst hconjugator),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hsecond hconjugator)]

theorem coprime_normalized_commutator_idempotent {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Acting Invariant : Subgroup Ambient)
    (hpacting : IsPGroup prime Acting) (hcoprime : ¬prime ∣ Nat.card Invariant)
    (hnormalizes : Acting ≤ Subgroup.normalizer (Invariant : Set Ambient)) :
    (⁅⁅Invariant, Acting⁆, Acting⁆ : Subgroup Ambient) = ⁅Invariant, Acting⁆ := by
  let FirstCommutators := (⁅Invariant, Acting⁆ : Subgroup Ambient)
  let SecondCommutators := (⁅FirstCommutators, Acting⁆ : Subgroup Ambient)
  have hfirstLe : FirstCommutators ≤ Invariant :=
    commutator_le_of_normalized Invariant Acting hnormalizes
  apply le_antisymm (Subgroup.commutator_mono hfirstLe le_rfl)
  apply Subgroup.commutator_le.mpr
  intro element helement actor hactor
  obtain ⟨fixed, hfixed, commutator, hcommutator, hequality⟩ :=
    coprime_normalized_fixed_decomposition hprime Acting Invariant hpacting hcoprime hnormalizes
      ⟨element, helement⟩
  have hfixedNormalizes : fixed.val ∈ Subgroup.normalizer (SecondCommutators : Set Ambient) :=
    normalizes_commutator_pair (Invariant ⊓ Subgroup.centralizer (Acting : Set Ambient))
      FirstCommutators Acting
      (inf_le_left.trans (Subgroup.normalizer_commutator_ge_left Invariant Acting))
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)) ⟨fixed.property, hfixed⟩
  have hcommutatorSecond : ⁅commutator.val, actor⁆ ∈ SecondCommutators :=
    Subgroup.commutator_mem_commutator hcommutator hactor
  have hconjugate := (Subgroup.mem_normalizer_iff.mp hfixedNormalizes
    ⁅commutator.val, actor⁆).mp hcommutatorSecond
  have hambientEquality := congrArg (fun entry : Invariant => entry.val) hequality
  change fixed.val * commutator.val = element at hambientEquality
  have hcommutes : actor * fixed.val = fixed.val * actor :=
    Subgroup.mem_centralizer_iff.mp hfixed actor hactor
  have hidentity : ⁅element, actor⁆ = fixed.val * ⁅commutator.val, actor⁆ * fixed.val⁻¹ := by
    rw [← hambientEquality, commutatorElement_def, commutatorElement_def, mul_inv_rev]
    calc
      fixed.val * commutator.val * actor * (commutator.val⁻¹ * fixed.val⁻¹) * actor⁻¹ =
          fixed.val * commutator.val * actor * commutator.val⁻¹ * actor⁻¹ * fixed.val⁻¹ := by
        have hinverse := congrArg Inv.inv hcommutes
        simp only [mul_inv_rev] at hinverse
        simpa only [mul_assoc] using congrArg
          (fun entry => fixed.val * commutator.val * actor * commutator.val⁻¹ * entry) hinverse
      _ = fixed.val * (commutator.val * actor * commutator.val⁻¹ * actor⁻¹) * fixed.val⁻¹ := by group
  exact hidentity ▸ hconjugate

end CFSG.LargeEvenClassification.Helpers
