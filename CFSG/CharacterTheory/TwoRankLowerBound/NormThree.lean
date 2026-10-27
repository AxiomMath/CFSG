module

public import CFSG.CharacterTheory.TwoRankLowerBound.InvolutionTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterTerminal
public import CFSG.CharacterTheory.TwoRankLowerBound.RootQuadratic

public section

open scoped BigOperators

namespace CFSG.TwoRankLowerBound.Helpers

theorem integer_norm_three_support (index : Type*) [Fintype index]
    (coefficient : index → ℤ) (principal : index) (hprincipal : coefficient principal = 1)
    (hnorm : ∑ label, coefficient label ^ 2 = 3) :
    ∃ left right : index, left ≠ right ∧ left ≠ principal ∧ right ≠ principal ∧
      (coefficient left = 1 ∨ coefficient left = -1) ∧
      (coefficient right = 1 ∨ coefficient right = -1) ∧
      ∀ label : index, label ≠ principal → label ≠ left → label ≠ right → coefficient label = 0 := by
  classical
  let support := Finset.univ.filter (fun label : index => coefficient label ≠ 0)
  have hbound : ∀ label : index, coefficient label ^ 2 ≤ 3 := by
    intro label
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun label => coefficient label ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ label)
    rwa [hnorm] at hle
  have hvalues : ∀ label : index,
      coefficient label = 0 ∨ coefficient label = 1 ∨ coefficient label = -1 := by
    intro label
    have hle := hbound label
    have hge : -1 ≤ coefficient label := by nlinarith
    have hleone : coefficient label ≤ 1 := by nlinarith
    omega
  have hnormcard : (support.card : ℤ) = 3 := by
    have hsum : ∑ label : index, coefficient label ^ 2 =
        ∑ label : index, if coefficient label ≠ 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro label _
      obtain hzero | hone | hnegative := hvalues label
      · simp [hzero]
      · simp [hone]
      · simp [hnegative]
    rw [hsum, Finset.sum_boole] at hnorm
    exact hnorm
  have hsupportcard : support.card = 3 := by exact_mod_cast hnormcard
  have hprincipalmem : principal ∈ support := by simp [support, hprincipal]
  have herasecard : (support.erase principal).card = 2 := by
    rw [Finset.card_erase_of_mem hprincipalmem, hsupportcard]
  obtain ⟨left, right, hne, hpairs⟩ := Finset.card_eq_two.mp herasecard
  have hleftmem : left ∈ support.erase principal := by rw [hpairs]; simp
  have hrightmem : right ∈ support.erase principal := by rw [hpairs]; simp
  have hleftprincipal : left ≠ principal := (Finset.mem_erase.mp hleftmem).1
  have hrightprincipal : right ≠ principal := (Finset.mem_erase.mp hrightmem).1
  have hleftnonzero : coefficient left ≠ 0 :=
    (Finset.mem_filter.mp (Finset.mem_erase.mp hleftmem).2).2
  have hrightnonzero : coefficient right ≠ 0 :=
    (Finset.mem_filter.mp (Finset.mem_erase.mp hrightmem).2).2
  refine ⟨left, right, hne, hleftprincipal, hrightprincipal,
    (hvalues left).resolve_left hleftnonzero, (hvalues right).resolve_left hrightnonzero, ?_⟩
  intro label hnotprincipal hnotleft hnotright
  by_contra hnonzero
  have hmember : label ∈ support.erase principal := by
    apply Finset.mem_erase.mpr
    exact ⟨hnotprincipal, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonzero⟩⟩
  rw [hpairs] at hmember
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmember
  exact hmember.elim hnotleft hnotright

theorem sum_eq_three_terms_of_support {index : Type*} [Fintype index]
    {target : Type*} [AddCommMonoid target] (function : index → target)
    (principal left right : index) (hleft : left ≠ principal) (hright : right ≠ principal)
    (hne : left ≠ right) (hsupport : ∀ label : index,
      label ≠ principal → label ≠ left → label ≠ right → function label = 0) :
    ∑ label, function label = function principal + function left + function right := by
  classical
  have hsubset : ({principal, left, right} : Finset index) ⊆ Finset.univ := Finset.subset_univ _
  have hequal := Finset.sum_subset (f := function) hsubset (by
    intro label _ hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hsupport label hnot.1 hnot.2.1 hnot.2.2)
  rw [← hequal]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Ne.symm hleft, Ne.symm hright, hne, or_self, not_false_eq_true, Finset.sum_singleton]
  exact (add_assoc _ _ _).symm

theorem integer_norm_three_quadratic_rigidity {index : Type*} [Fintype index]
    (coefficient : index → ℤ) (principal : index) (degree value : index → ℂ)
    (hprincipal : coefficient principal = 1) (hnorm : ∑ label, coefficient label ^ 2 = 3)
    (hprincipaldegree : degree principal = 1) (hprincipalvalue : value principal = 1)
    (hdegrees : ∀ label, degree label ≠ 0)
    (hdegreezero : ∑ label, (coefficient label : ℂ) * degree label = 0)
    (hvaluezero : ∑ label, (coefficient label : ℂ) * value label = 0)
    (hquadratic : ∑ label, (coefficient label : ℂ) * value label ^ 2 / degree label = 0) :
    ∃ label : index, label ≠ principal ∧ coefficient label ≠ 0 ∧ value label = degree label := by
  obtain ⟨left, right, hne, hleftprincipal, hrightprincipal, hleftsign, hrightsign, hsupport⟩ :=
    integer_norm_three_support index coefficient principal hprincipal hnorm
  have hleftnonzero : (coefficient left : ℂ) ≠ 0 := by
    obtain hsign | hsign := hleftsign <;> simp [hsign]
  have hrightnonzero : (coefficient right : ℂ) ≠ 0 := by
    obtain hsign | hsign := hrightsign <;> simp [hsign]
  have hleftsquare : (coefficient left : ℂ) ^ 2 = 1 := by
    obtain hsign | hsign := hleftsign <;> simp [hsign]
  have hrightsquare : (coefficient right : ℂ) ^ 2 = 1 := by
    obtain hsign | hsign := hrightsign <;> simp [hsign]
  have hdegreeterms : 1 + (coefficient left : ℂ) * degree left +
      (coefficient right : ℂ) * degree right = 0 := by
    rw [sum_eq_three_terms_of_support (fun label => (coefficient label : ℂ) * degree label)
      principal left right hleftprincipal hrightprincipal hne] at hdegreezero
    · simpa [hprincipal, hprincipaldegree] using hdegreezero
    · intro label hnotprincipal hnotleft hnotright
      simp [hsupport label hnotprincipal hnotleft hnotright]
  have hvalueterms : 1 + (coefficient left : ℂ) * value left +
      (coefficient right : ℂ) * value right = 0 := by
    rw [sum_eq_three_terms_of_support (fun label => (coefficient label : ℂ) * value label)
      principal left right hleftprincipal hrightprincipal hne] at hvaluezero
    · simpa [hprincipal, hprincipalvalue] using hvaluezero
    · intro label hnotprincipal hnotleft hnotright
      simp [hsupport label hnotprincipal hnotleft hnotright]
  have hquadraticterms : 1 + ((coefficient left : ℂ) * value left) ^ 2 /
      ((coefficient left : ℂ) * degree left) + ((coefficient right : ℂ) * value right) ^ 2 /
      ((coefficient right : ℂ) * degree right) = 0 := by
    rw [sum_eq_three_terms_of_support
      (fun label => (coefficient label : ℂ) * value label ^ 2 / degree label)
      principal left right hleftprincipal hrightprincipal hne] at hquadratic
    · have hleftterm : ((coefficient left : ℂ) * value left) ^ 2 /
          ((coefficient left : ℂ) * degree left) =
          (coefficient left : ℂ) * value left ^ 2 / degree left := by
        field_simp
      have hrightterm : ((coefficient right : ℂ) * value right) ^ 2 /
          ((coefficient right : ℂ) * degree right) =
          (coefficient right : ℂ) * value right ^ 2 / degree right := by
        field_simp
      rw [hleftterm, hrightterm]
      simpa [hprincipal, hprincipalvalue, hprincipaldegree] using hquadratic
    · intro label hnotprincipal hnotleft hnotright
      simp [hsupport label hnotprincipal hnotleft hnotright]
  have hrigidity := three_character_quadratic_rigidity
    ((coefficient left : ℂ) * degree left) ((coefficient right : ℂ) * degree right)
    ((coefficient left : ℂ) * value left) ((coefficient right : ℂ) * value right)
    (mul_ne_zero hleftnonzero (hdegrees left)) (mul_ne_zero hrightnonzero (hdegrees right))
    hdegreeterms hvalueterms hquadraticterms
  refine ⟨left, hleftprincipal, ?_, mul_left_cancel₀ hleftnonzero hrigidity.1⟩
  obtain hsign | hsign := hleftsign <;> omega

theorem rank_one_norm_three_character_witness_contradicts_simple
    {G index : Type*} [Group G] [Fintype G] [IsSimpleGroup G] [Fintype index]
    (hrank : CFSG.Open.twoRank G ≤ 1)
    (involution : G) (horder : orderOf involution = 2)
    (vector : index → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ℂ (vector label)] [∀ label, FiniteDimensional ℂ (vector label)]
    (representation : ∀ label, Representation ℂ G (vector label))
    [∀ label, (representation label).IsIrreducible]
    (coefficient : index → ℤ) (principal : index)
    (hprincipal : coefficient principal = 1) (hnorm : ∑ label, coefficient label ^ 2 = 3)
    (hprincipalcharacter : ∀ element : G, (representation principal).character element = 1)
    (hdegrees : ∀ label, (representation label).character 1 ≠ 0)
    (hnonprincipal : ∀ label, label ≠ principal →
      ∃ element : G, representation label element ≠ 1)
    (hidentity : ∑ label, (coefficient label : ℂ) * (representation label).character 1 = 0)
    (hinvolution : ∑ label,
      (coefficient label : ℂ) * (representation label).character involution = 0)
    (function : Subgroup.centralizer ({involution} : Set G) → ℂ)
    (hsupport : ∀ element : Subgroup.centralizer ({involution} : Set G),
      (element : G) ∉ cyclicRootSet involution → function element = 0)
    (hexpansion : ∀ element : G,
      inducedFunction (Subgroup.centralizer ({involution} : Set G)) function element =
        ∑ label, (coefficient label : ℂ) * (representation label).character element) : False := by
  have hquadratic := root_supported_character_expansion_quadratic_zero involution horder
    (centralizer_unique_involution_of_twoRank_le_one hrank involution horder) function hsupport
    vector representation (fun label => (coefficient label : ℂ)) hdegrees hexpansion
  obtain ⟨label, hnotprincipal, _, hequal⟩ := integer_norm_three_quadratic_rigidity coefficient
    principal (fun label => (representation label).character 1)
    (fun label => (representation label).character involution) hprincipal hnorm
    (hprincipalcharacter 1) (hprincipalcharacter involution) hdegrees hidentity hinvolution
    hquadratic
  exact representation_involution_character_ne_degree_of_simple (representation label)
    (hnonprincipal label hnotprincipal) involution horder hequal

end CFSG.TwoRankLowerBound.Helpers
