module

public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.CentralizerNorm
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes

theorem primeRegular_primeSectionUnion {G : Type*} [Group G] (p : ℕ) :
    primeSectionUnion p {x : G | Nat.Coprime p (orderOf x)} := by
  intro a a' b b' e e' ha ha' hb hb' hab ha'b' hconj
  change Nat.Coprime p (orderOf (a * b)) ↔ Nat.Coprime p (orderOf (a' * b'))
  rw [primary_regular_coprime_iff a b e ha hb hab,
    primary_regular_coprime_iff a' b' e' ha' hb' ha'b']
  constructor
  · rintro rfl
    exact isConj_one_right.mp hconj
  · rintro rfl
    exact isConj_one_left.mp hconj

theorem orderOf_eq_prime_of_mem_of_card_eq {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH : Nat.card H = p) {u : G} (hu : u ∈ H) (hne : u ≠ 1) :
    orderOf u = p := by
  have hdvd : orderOf u ∣ p := by
    have h := orderOf_dvd_natCard (⟨u, hu⟩ : H)
    rwa [hH, Subgroup.orderOf_mk] at h
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

variable {G : Type*} [Group G] [Fintype G]

theorem prime_order_sylow_principal_column_norm (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G)
    (hP : Nat.card P = p) (u : G) (hu : u ∈ (P : Subgroup G)) (hne : u ≠ 1) :
    (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u *
        starRingEnd ℂ ((basis.representation χ).character u)) = p := by
  have hp : p.Prime := Fact.out
  have horder : orderOf u = p := orderOf_eq_prime_of_mem_of_card_eq hP hu hne
  have hGfactor : (Nat.card G).factorization p = 1 := by
    have h := P.card_eq_multiplicity
    rw [hP] at h
    exact Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm)
  have horder' : orderOf (centralizerSelf u) = p := by
    rw [centralizerSelf, Subgroup.orderOf_mk, horder]
  have hCfactor : (Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G))).factorization p =
      1 := by
    have hC0 : Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G)) ≠ 0 :=
      Nat.card_pos.ne'
    have hpC : p ∣ Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G)) :=
      horder' ▸ orderOf_dvd_natCard (centralizerSelf u)
    have hle := (Nat.factorization_le_iff_dvd hC0 Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card _) p
    have hpos := hp.factorization_pos_of_dvd hC0 hpC
    omega
  have hzpowers : IsPGroup p (Subgroup.zpowers (centralizerSelf u)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horder', pow_one])
  obtain ⟨S, hS⟩ := hzpowers.exists_le_sylow
  have hScard : Nat.card S = p := by rw [S.card_eq_multiplicity, hCfactor, pow_one]
  have hSeq : Subgroup.zpowers (centralizerSelf u) = S :=
    Subgroup.eq_of_le_of_card_ge hS (by rw [hScard, Nat.card_zpowers, horder'])
  have hScentral : (S : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) ≤
      CFSG.centerIn (Subgroup.normalizer
        ((S : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) :
          Set (Subgroup.centralizer (Subgroup.zpowers u : Set G)))) := by
    intro s hs
    have hcenter : s ∈ Subgroup.center (Subgroup.centralizer (Subgroup.zpowers u : Set G)) := by
      rw [← hSeq] at hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact Subgroup.zpow_mem _ (centralizerSelf_mem_center u) k
    exact ⟨Subgroup.le_normalizer hs, fun n _ => Subgroup.mem_center_iff.mp hcenter n⟩
  obtain ⟨N, hNormal, hcoprime, hquotient⟩ :=
    CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p S
      hScentral
  obtain ⟨localBasis⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer (Subgroup.zpowers u : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal, -⟩ :=
    CFSG.Wreathed.complete_character_basis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨hcolumn, hdegrees, hsylow⟩ :=
    principal_primary_column_centralizer_norm_of_normal_complement basis ideal p principal
      hprincipal u 1 (by rw [horder, pow_one]) localBasis localPrincipal hlocalPrincipal N hcoprime
      hquotient
  rw [hcolumn, hdegrees, hsylow S, hScard]

theorem prime_order_sylow_principal_column_norm_bounds_constant_singular_characters
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G) (hP : Nat.card P = p) :
    (∀ u ∈ (P : Subgroup G), u ≠ 1 →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ‖(basis.representation χ).character u‖ ^ 2 = (p : ℝ)) ∧
    (∀ (Λ : Finset basis.index) (c : basis.index → ℂ), principal ∉ Λ → (∀ η ∈ Λ, c η ≠ 0) →
      (∀ η ∈ Λ, ∀ x : G, p ∣ orderOf x → (basis.representation η).character x = c η) →
        Λ ⊆ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
          ∑ η ∈ Λ, ‖c η‖ ^ 2 ≤ (p : ℝ) - 1) ∧
    ∀ Λ : Finset basis.index,
      (∀ η ∈ Λ, ∀ x : G, p ∣ orderOf x → (basis.representation η).character x = -1) →
        Λ.card ≤ p - 1 := by
  have hp : p.Prime := Fact.out
  have hnorm : ∀ u ∈ (P : Subgroup G), u ≠ 1 →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ‖(basis.representation χ).character u‖ ^ 2 = (p : ℝ) := by
    intro u hu hne
    have h := prime_order_sylow_principal_column_norm basis ideal p principal hprincipal P hP u hu
      hne
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    exact_mod_cast h
  obtain ⟨u, hu, hne⟩ : ∃ u ∈ (P : Subgroup G), u ≠ 1 := by
    by_contra! hall
    have hbot : (P : Subgroup G) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    have hcard := hP
    rw [hbot, Subgroup.card_bot] at hcard
    exact hp.one_lt.ne hcard
  have horder : orderOf u = p := orderOf_eq_prime_of_mem_of_card_eq hP hu hne
  have hsingular : p ∣ orderOf u := horder ▸ dvd_refl p
  have hbound : ∀ (Λ : Finset basis.index) (c : basis.index → ℂ), principal ∉ Λ →
      (∀ η ∈ Λ, c η ≠ 0) →
      (∀ η ∈ Λ, ∀ x : G, p ∣ orderOf x → (basis.representation η).character x = c η) →
        Λ ⊆ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
          ∑ η ∈ Λ, ‖c η‖ ^ 2 ≤ (p : ℝ) - 1 := by
    intro Λ c hΛ hc hconstant
    have hsubset : Λ ⊆ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
      intro η hη
      by_contra hout
      have hmask : characterFunctionMask {x : G | Nat.Coprime p (orderOf x)}
          ((basis.representation η).character -
            c η • (basis.representation principal).character) =
          (basis.representation η).character -
            c η • (basis.representation principal).character := by
        funext x
        unfold characterFunctionMask
        split_ifs with hx
        · rfl
        · have hdvd : p ∣ orderOf x := by
            by_contra hnot
            exact hx ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot)
          rw [Pi.sub_apply, Pi.smul_apply, hconstant η hη x hdvd, hprincipal, Pi.one_apply,
            smul_eq_mul, mul_one, sub_self]
      have hcommute := coefficientBlock_section_mask_commute basis ideal p principal
        {x : G | Nat.Coprime p (orderOf x)} (primeRegular_primeSectionUnion p)
        ((basis.representation η).character - c η • (basis.representation principal).character)
      rw [hmask] at hcommute
      have hvalue := congrFun hcommute u
      have hregular : u ∉ {x : G | Nat.Coprime p (orderOf x)} := by
        intro hmem
        have hself : Nat.Coprime p p := horder ▸ hmem
        exact hp.one_lt.ne' ((Nat.coprime_self p).mp hself)
      rw [characterFunctionMask, ite_eq_right hregular, map_sub, map_smul,
        characterSubsetProjection_character_not_mem basis _ η hout,
        characterSubsetProjection_character basis _ principal
          (coefficientBlock_self_mem basis _ principal)] at hvalue
      simp only [Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, hprincipal, Pi.one_apply,
        smul_eq_mul, mul_one, zero_sub, neg_eq_zero] at hvalue
      exact hc η hη hvalue
    refine ⟨hsubset, ?_⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.insert_subset (coefficientBlock_self_mem basis _ principal) hsubset)
      (fun χ _ _ => sq_nonneg ‖(basis.representation χ).character u‖)
    rw [hnorm u hu hne, Finset.sum_insert hΛ, hprincipal] at hle
    have hterms : ∑ η ∈ Λ, ‖(basis.representation η).character u‖ ^ 2 = ∑ η ∈ Λ, ‖c η‖ ^ 2 :=
      Finset.sum_congr rfl fun η hη => by rw [hconstant η hη u hsingular]
    rw [hterms, Pi.one_apply, norm_one, one_pow] at hle
    linarith
  refine ⟨hnorm, hbound, fun Λ hΛ => ?_⟩
  have hprincipalNot : principal ∉ Λ := by
    intro hmem
    have h := hΛ principal hmem u hsingular
    rw [hprincipal, Pi.one_apply] at h
    norm_num at h
  obtain ⟨-, hle⟩ := hbound Λ (fun _ => -1) hprincipalNot (fun _ _ => by norm_num) hΛ
  simp only [norm_neg, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hle
  have hcast : (Λ.card : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    exact hle
  exact_mod_cast hcast

end CFSG.Semidihedral.Principal
