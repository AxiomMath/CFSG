module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem left_normal_in_sup_of_normalizes {G : Type u} [Group G]
    (first second : Subgroup G) (hnormalizes : second ≤ Subgroup.normalizer (first : Set G)) :
    (first.subgroupOf (first ⊔ second)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
  exact sup_le Subgroup.le_normalizer hnormalizes

theorem normal_subgroupOf_of_normalizes {G : Type u} [Group G]
    (subgroup acting : Subgroup G) (hnormalizes : acting ≤ Subgroup.normalizer (subgroup : Set G)) :
    (subgroup.subgroupOf acting).Normal := by
  apply Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator element helement
  exact ⟨Subgroup.le_normalizer_iff.mp hnormalizes conjugator hconjugator element helement.1,
    acting.mul_mem (acting.mul_mem hconjugator helement.2) (acting.inv_mem hconjugator)⟩

theorem normalized_sup_solvable {G : Type u} [Group G]
    (first second : Subgroup G) (hnormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (hfirst : Group.IsSolvable first) (hsecond : Group.IsSolvable second) :
    Group.IsSolvable (first ⊔ second : Subgroup G) := by
  have : (first.subgroupOf (first ⊔ second)).Normal := left_normal_in_sup_of_normalizes _ _ hnormalizes
  have : (first.subgroupOf (second ⊔ first)).Normal :=
    normal_subgroupOf_of_normalizes first (second ⊔ first) (sup_le hnormalizes Subgroup.le_normalizer)
  have : (first.subgroupOf second).Normal := normal_subgroupOf_of_normalizes first second hnormalizes
  have : Group.IsSolvable first := hfirst
  have : Group.IsSolvable second := hsecond
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient second first hnormalizes
  rw [sup_comm first second]
  apply (Group.isSolvable_iff_subgroup_quotient (first.subgroupOf (second ⊔ first))).mpr
  constructor
  · let restriction := Subgroup.subgroupOfEquivOfLe (show first ≤ second ⊔ first from le_sup_right)
    exact Group.isSolvable_of_surjective (f := restriction.symm.toMonoidHom) restriction.symm.surjective
  · exact Group.isSolvable_of_surjective (f := equivalence.toMonoidHom) equivalence.surjective

theorem normalized_sup_prime_complement {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (first second : Subgroup G)
    (hnormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (hfirst : ¬prime ∣ Nat.card first) (hsecond : ¬prime ∣ Nat.card second) :
    ¬prime ∣ Nat.card (first ⊔ second : Subgroup G) := by
  have : (first.subgroupOf (first ⊔ second)).Normal := left_normal_in_sup_of_normalizes _ _ hnormalizes
  have : (first.subgroupOf (second ⊔ first)).Normal :=
    normal_subgroupOf_of_normalizes first (second ⊔ first) (sup_le hnormalizes Subgroup.le_normalizer)
  have : (first.subgroupOf second).Normal := normal_subgroupOf_of_normalizes first second hnormalizes
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient second first hnormalizes
  have hquotientCard : Nat.card ((second ⊔ first : Subgroup G) ⧸
      first.subgroupOf (second ⊔ first)) ∣ Nat.card second := by
    rw [← Nat.card_congr equivalence.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hrestrictedCard : Nat.card (first.subgroupOf (second ⊔ first)) = Nat.card first :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show first ≤ second ⊔ first from le_sup_right)).toEquiv
  rw [sup_comm first second,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (first.subgroupOf (second ⊔ first)),
    hrestrictedCard, hprime.dvd_mul]
  exact fun hdiv => hdiv.elim (fun hquotient => hsecond (hquotient.trans hquotientCard)) hfirst

theorem normalized_sup_factorization {G : Type u} [Group G]
    (first second : Subgroup G) (hnormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (element : G) (hmem : element ∈ first ⊔ second) :
    ∃ left ∈ first, ∃ right ∈ second, left * right = element := by
  exact normal_subgroup_sup_factorization (first ⊔ second) first second le_sup_left le_sup_right
    (left_normal_in_sup_of_normalizes first second hnormalizes) rfl element hmem

theorem normalizes_commutator_of_normalizes_both {G : Type u} [Group G]
    (acting first second : Subgroup G)
    (hfirst : acting ≤ Subgroup.normalizer (first : Set G))
    (hsecond : acting ≤ Subgroup.normalizer (second : Set G)) :
    acting ≤ Subgroup.normalizer ((⁅first, second⁆ : Subgroup G) : Set G) := by
  intro element helement
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hfirst helement),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hsecond helement)]

theorem normalizes_centralizer_of_normalizes {G : Type u} [Group G]
    (acting subgroup : Subgroup G) (hnormalizes : acting ≤ Subgroup.normalizer (subgroup : Set G)) :
    acting ≤ Subgroup.normalizer (Subgroup.centralizer (subgroup : Set G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hconjugate := Subgroup.le_normalizer_iff.mp hnormalizes conjugator⁻¹
    (acting.inv_mem hconjugator) member hmember
  simp only [inv_inv] at hconjugate
  have hcommute : Commute (conjugator⁻¹ * member * conjugator) element :=
    (Subgroup.mem_centralizer_iff (s := (subgroup : Set G))).mp helement
      (conjugator⁻¹ * member * conjugator) hconjugate
  have hmapped := hcommute.map (MulAut.conj conjugator).toMonoidHom
  have hresult : Commute member (conjugator * element * conjugator⁻¹) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one] using hmapped
  exact hresult

theorem normalizes_inf_of_normalizes_both {G : Type u} [Group G]
    (acting first second : Subgroup G)
    (hfirst : acting ≤ Subgroup.normalizer (first : Set G))
    (hsecond : acting ≤ Subgroup.normalizer (second : Set G)) :
    acting ≤ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator element helement
  exact ⟨Subgroup.le_normalizer_iff.mp hfirst conjugator hconjugator element helement.1,
    Subgroup.le_normalizer_iff.mp hsecond conjugator hconjugator element helement.2⟩

end CFSG.RankThreeEvenClassification.Helpers
