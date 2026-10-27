module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def thetaActorCommutator {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (element : G) : Subgroup G :=
  ⁅thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)), actor⁆

@[expose] noncomputable def thetaActorFixedCore {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) : Subgroup G :=
  thetaCoreOf prime (Subgroup.centralizer (actor : Set G))

@[expose] noncomputable def thetaActorSignalizer {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (element : G) : Subgroup G :=
  thetaActorCommutator prime actor element ⊔ thetaActorFixedCore prime actor

theorem centralizer_actor_le_element_centralizer {G : Type u} [Group G]
    (actor : Subgroup G) (element : G) (hmem : element ∈ actor) :
    Subgroup.centralizer (actor : Set G) ≤ Subgroup.centralizer ({element} : Set G) := by
  apply Subgroup.centralizer_le
  intro other hother
  exact (Set.mem_singleton_iff.mp hother) ▸ hmem

theorem centralizer_actor_normalizes_element_theta {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (element : G) (hmem : element ∈ actor) :
    Subgroup.centralizer (actor : Set G) ≤ Subgroup.normalizer
      (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) : Set G) := by
  exact ((centralizer_actor_le_element_centralizer actor element hmem).trans
    Subgroup.le_normalizer).trans (normalizer_le_normalizer_thetaCoreOf prime hprime _)

theorem centralizer_actor_normalizes_thetaActorCommutator {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (element : G) (hmem : element ∈ actor) :
    Subgroup.centralizer (actor : Set G) ≤
      Subgroup.normalizer (thetaActorCommutator prime actor element : Set G) := by
  exact normalizes_commutator_of_normalizes_both _ _ _
    (centralizer_actor_normalizes_element_theta prime hprime actor element hmem)
    (Subgroup.centralizer_le_normalizer _)

theorem thetaActorCommutator_le_theta {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    thetaActorCommutator prime actor element ≤
      thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) := by
  exact thetaPlaneCommutator_le_element_theta prime hprime actor hcomm element hmem

theorem thetaActorCommutator_solvable {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    Group.IsSolvable (thetaActorCommutator prime actor element) := by
  have : Group.IsSolvable (thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))) :=
    thetaCoreOf_solvable prime hprime _
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (thetaActorCommutator_le_theta prime hprime actor hcomm element hmem))
    (Subgroup.inclusion_injective _)

theorem thetaActorCommutator_prime_complement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    ¬prime ∣ Nat.card (thetaActorCommutator prime actor element) := by
  exact thetaPlaneCommutator_prime_complement prime hprime actor hcomm element hmem

theorem thetaActorFixedCore_normalizes_commutator {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (element : G) (hmem : element ∈ actor) :
    thetaActorFixedCore prime actor ≤
      Subgroup.normalizer (thetaActorCommutator prime actor element : Set G) := by
  exact (thetaCoreOf_le prime _).trans
    (centralizer_actor_normalizes_thetaActorCommutator prime hprime actor element hmem)

theorem thetaActorSignalizer_le_centralizer {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    thetaActorSignalizer prime actor element ≤ Subgroup.centralizer ({element} : Set G) := by
  exact sup_le ((thetaActorCommutator_le_theta prime hprime actor hcomm element hmem).trans
    (thetaCoreOf_le prime _)) ((thetaCoreOf_le prime _).trans
      (centralizer_actor_le_element_centralizer actor element hmem))

theorem thetaActorSignalizer_solvable {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    Group.IsSolvable (thetaActorSignalizer prime actor element) := by
  exact normalized_sup_solvable _ _
    (thetaActorFixedCore_normalizes_commutator prime hprime actor element hmem)
    (thetaActorCommutator_solvable prime hprime actor hcomm element hmem)
    (thetaCoreOf_solvable prime hprime _)

theorem thetaActorSignalizer_prime_complement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    ¬prime ∣ Nat.card (thetaActorSignalizer prime actor element) := by
  exact normalized_sup_prime_complement prime hprime _ _
    (thetaActorFixedCore_normalizes_commutator prime hprime actor element hmem)
    (thetaActorCommutator_prime_complement prime hprime actor hcomm element hmem)
    (thetaCoreOf_prime_complement prime hprime _)

theorem thetaActorSignalizer_normalized {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (element : G) :
    actor ≤ Subgroup.normalizer (thetaActorSignalizer prime actor element : Set G) := by
  exact (le_inf (Subgroup.normalizer_commutator_ge_right _ actor)
    ((Subgroup.le_centralizer_iff.mpr (thetaCoreOf_le prime _)).trans
      (Subgroup.centralizer_le_normalizer _))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem normalized_sup_centralizer_eq {G : Type u} [Group G]
    (first second acting : Subgroup G)
    (hnormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (hfixed : second ≤ Subgroup.centralizer (acting : Set G)) :
    (first ⊔ second) ⊓ Subgroup.centralizer (acting : Set G) =
      (first ⊓ Subgroup.centralizer (acting : Set G)) ⊔ second := by
  apply le_antisymm
  · intro element helement
    obtain ⟨left, hleft, right, hright, rfl⟩ :=
      normalized_sup_factorization first second hnormalizes element helement.1
    have hleftCentralizer : left ∈ Subgroup.centralizer (acting : Set G) := by
      have hrightInv := (Subgroup.centralizer (acting : Set G)).inv_mem (hfixed hright)
      have hmem := (Subgroup.centralizer (acting : Set G)).mul_mem helement.2 hrightInv
      simpa only [mul_inv_cancel_right] using hmem
    exact Subgroup.mul_mem_sup ⟨hleft, hleftCentralizer⟩ hright
  · exact sup_le (inf_le_inf_right _ le_sup_left)
      (le_inf le_sup_right hfixed)

theorem thetaActorCommutator_fixed_le_core {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    thetaActorCommutator prime actor element ⊓ Subgroup.centralizer (actor : Set G) ≤
      thetaActorFixedCore prime actor := by
  let fixed := thetaActorCommutator prime actor element ⊓ Subgroup.centralizer (actor : Set G)
  have hnormalized : Subgroup.centralizer (actor : Set G) ≤ Subgroup.normalizer (fixed : Set G) :=
    normalizes_inf_of_normalizes_both _ _ _
      (centralizer_actor_normalizes_thetaActorCommutator prime hprime actor element hmem)
      Subgroup.le_normalizer
  have hnormal : (fixed.subgroupOf (Subgroup.centralizer (actor : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnormalized
  have : Group.IsSolvable (thetaActorCommutator prime actor element) :=
    thetaActorCommutator_solvable prime hprime actor hcomm element hmem
  have hsolvable : Group.IsSolvable fixed :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hcomplement : ¬prime ∣ Nat.card fixed := fun hdiv =>
    thetaActorCommutator_prime_complement prime hprime actor hcomm element hmem
      (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact normal_solvable_primeComplement_le_thetaCoreOf prime fixed _ inf_le_right
    hnormal hsolvable hcomplement

theorem thetaActorSignalizer_fixed_eq_core {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (element : G) (hmem : element ∈ actor) :
    thetaActorSignalizer prime actor element ⊓ Subgroup.centralizer (actor : Set G) =
      thetaActorFixedCore prime actor := by
  rw [thetaActorSignalizer, normalized_sup_centralizer_eq _ _ actor
    (thetaActorFixedCore_normalizes_commutator prime hprime actor element hmem) (thetaCoreOf_le prime _)]
  exact sup_eq_right.mpr (thetaActorCommutator_fixed_le_core prime hprime actor hcomm element hmem)

theorem normalized_sup_commutator_eq_of_fixed {G : Type u} [Group G]
    (first second acting : Subgroup G)
    (hnormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (hfixed : second ≤ Subgroup.centralizer (acting : Set G)) :
    ⁅first ⊔ second, acting⁆ = ⁅first, acting⁆ := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro element helement member hmember
    obtain ⟨left, hleft, right, hright, rfl⟩ :=
      normalized_sup_factorization first second hnormalizes element helement
    have hcommute : Commute right member :=
      (Subgroup.mem_centralizer_iff.mp (hfixed hright) member hmember).symm
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hcommute, mul_one, mul_inv_cancel, one_mul]
    exact Subgroup.commutator_mem_commutator hleft hmember
  · exact Subgroup.commutator_mono le_sup_left le_rfl

theorem thetaActorSignalizer_balance {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (hpgroup : IsPGroup prime actor) (first second : G) (hfirst : first ∈ actor) (hsecond : second ∈ actor)
    (hmixed : ⁅Subgroup.centralizer ({second} : Set G) ⊓
      thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
        thetaCoreOf prime (Subgroup.centralizer ({second} : Set G))) :
    thetaActorSignalizer prime actor first ⊓ Subgroup.centralizer ({second} : Set G) ≤
      thetaActorSignalizer prime actor second := by
  let fixed := thetaActorCommutator prime actor first ⊓ Subgroup.centralizer ({second} : Set G)
  let balanced := thetaActorSignalizer prime actor first ⊓ Subgroup.centralizer ({second} : Set G)
  have hcoreFixed : thetaActorFixedCore prime actor ≤ Subgroup.centralizer ({second} : Set G) :=
    (thetaCoreOf_le prime _).trans (centralizer_actor_le_element_centralizer actor second hsecond)
  have hcoreNormalizesFixed : thetaActorFixedCore prime actor ≤ Subgroup.normalizer (fixed : Set G) :=
    normalizes_inf_of_normalizes_both _ _ _
      (thetaActorFixedCore_normalizes_commutator prime hprime actor first hfirst)
      (hcoreFixed.trans Subgroup.le_normalizer)
  have hbalancedEq : balanced = fixed ⊔ thetaActorFixedCore prime actor := by
    simpa only [balanced, fixed, thetaActorSignalizer, Subgroup.centralizer_closure] using
      normalized_sup_centralizer_eq _ _ (Subgroup.closure ({second} : Set G))
      (thetaActorFixedCore_normalizes_commutator prime hprime actor first hfirst)
      (by simpa only [Subgroup.centralizer_closure] using hcoreFixed)
  have hfixedNormalized : actor ≤ Subgroup.normalizer (fixed : Set G) :=
    normalizes_inf_of_normalizes_both _ _ _ (Subgroup.normalizer_commutator_ge_right _ actor)
      ((commutative_plane_le_element_centralizer actor hcomm second hsecond).trans Subgroup.le_normalizer)
  have hbalancedNormalized : actor ≤ Subgroup.normalizer (balanced : Set G) :=
    normalizes_inf_of_normalizes_both _ _ _ (thetaActorSignalizer_normalized prime actor first)
      ((commutative_plane_le_element_centralizer actor hcomm second hsecond).trans Subgroup.le_normalizer)
  have : Group.IsSolvable (thetaActorCommutator prime actor first) :=
    thetaActorCommutator_solvable prime hprime actor hcomm first hfirst
  have hfixedComplement : ¬prime ∣ Nat.card fixed := fun hdiv =>
    thetaActorCommutator_prime_complement prime hprime actor hcomm first hfirst
      (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hbalancedComplement : ¬prime ∣ Nat.card balanced := fun hdiv =>
    thetaActorSignalizer_prime_complement prime hprime actor hcomm first hfirst
      (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hfixedLe : fixed ≤ Subgroup.centralizer ({second} : Set G) ⊓
      thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)) :=
    le_inf inf_le_right (inf_le_left.trans (thetaActorCommutator_le_theta prime hprime actor hcomm first hfirst))
  have hcommutatorLe := (Subgroup.commutator_mono hfixedLe le_rfl).trans hmixed
  have hidempotent := coprime_commutator_idempotent prime hprime actor fixed hpgroup
    hfixedComplement hfixedNormalized
  have hsmall : ⁅fixed, actor⁆ ≤ thetaActorCommutator prime actor second := by
    rw [← hidempotent]
    exact Subgroup.commutator_mono hcommutatorLe le_rfl
  have hfixedCore : balanced ⊓ Subgroup.centralizer (actor : Set G) ≤ thetaActorFixedCore prime actor :=
    (inf_le_inf_right _ inf_le_left).trans (thetaActorSignalizer_fixed_eq_core prime hprime actor hcomm first hfirst).le
  have hcommutatorEq : ⁅balanced, actor⁆ = ⁅fixed, actor⁆ := by
    rw [hbalancedEq]
    exact normalized_sup_commutator_eq_of_fixed fixed (thetaActorFixedCore prime actor) actor
      hcoreNormalizesFixed (thetaCoreOf_le prime _)
  have hfactor := coprime_commutator_centralizer_factorization prime hprime actor balanced hpgroup
    hbalancedComplement hbalancedNormalized
  change balanced ≤ thetaActorSignalizer prime actor second
  rw [hfactor, hcommutatorEq]
  exact sup_le_sup hsmall hfixedCore

theorem thetaActorSignalizer_isSolvableSignalizerFunctor {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hcomm : IsMulCommutative actor)
    (hpgroup : IsPGroup prime actor)
    (hmixed : ∀ first ∈ actor, first ≠ 1 → ∀ second ∈ actor, second ≠ 1 →
      ⁅Subgroup.centralizer ({second} : Set G) ⊓
        thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
          thetaCoreOf prime (Subgroup.centralizer ({second} : Set G))) :
    IsSolvableSignalizerFunctor prime actor (thetaActorSignalizer prime actor) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro element hmem _
    exact thetaActorSignalizer_le_centralizer prime hprime actor hcomm element hmem
  · intro element hmem _
    exact hprime.coprime_iff_not_dvd.mpr
      (thetaActorSignalizer_prime_complement prime hprime actor hcomm element hmem)
  · intro element _ _ conjugator hconjugator
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (thetaActorSignalizer_normalized prime actor element hconjugator)
  · intro first hfirst hfirstNe second hsecond hsecondNe
    exact thetaActorSignalizer_balance prime hprime actor hcomm hpgroup first second hfirst hsecond
      (hmixed first hfirst hfirstNe second hsecond hsecondNe)
  · intro element hmem _
    exact thetaActorSignalizer_solvable prime hprime actor hcomm element hmem

end CFSG.RankThreeEvenClassification.Helpers
