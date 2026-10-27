module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryFour
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueSetup

public section

open scoped Classical

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.CentralSL2 CFSG.TwoRankLowerBound.Helpers

theorem mem_of_mem_closure_pair {X : Type*} [Group X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {g : X} (hg : g ∈ Subgroup.closure {a, b}) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  induction hg using Subgroup.closure_induction with
  | mem c hc =>
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul c d _ _ hc hd =>
    rcases hc with rfl | rfl | rfl | rfl
    · simpa using hd
    · rcases hd with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
    · rcases hd with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inr (Or.inr (Or.inr hab.symm))
      · exact Or.inl hb
      · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
    · rcases hd with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul])))
      · exact Or.inr (Or.inl (by rw [mul_assoc, hb, mul_one]))
      · exact Or.inl (by rw [mul_assoc, ← mul_assoc b, ← hab, mul_assoc, hb, mul_one, ha])
  | inv c _ hc =>
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl ha')
    · exact Or.inr (Or.inr (Or.inl hb'))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, ha', hb', hab]

theorem exists_odd_add_one_eq
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f) :
    ∃ k₀ : ℕ, Odd k₀ ∧ p ^ f + 1 = 2 ^ n * k₀ := by
  have htwo := NormalComponentLift.two_pow_eq_two_part (n := n) (hn := hn) (S := S) (e := e)
    hnonab hfour hp hp2 hf hmodel
  have hε : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = -1 := by simp [hq3]
  rw [hε] at htwo
  have hval : (p ^ f + 2 - 1).factorization 2 = n := by
    have hv : padicValInt 2 ((p ^ f : ℕ) - (-1 : ℤ)) = n :=
      (Nat.pow_right_injective (le_refl 2) htwo).symm
    rw [show ((p ^ f : ℕ) : ℤ) - (-1 : ℤ) = ((p ^ f + 2 - 1 : ℕ) : ℤ) by push_cast; ring,
      padicValInt.of_nat, ← Nat.factorization_def _ Nat.prime_two] at hv
    exact hv
  obtain ⟨k₀, hk₀, hqk₀⟩ :=
    SameFieldLinearRecognition.exists_odd_of_two_part (p ^ f + 2) n (by omega) hval
  exact ⟨k₀, hk₀, by rw [← hqk₀]; omega⟩

theorem four_group_involutions
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let z : G := wreathModelHom S e (Original.x2 (2 ^ n))
    ∀ c ∈ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z}, c * c = 1 →
      c = 1 ∨ c = x ∨ c = z ∨ c = x * z := by
  intro x z c hc hcc
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  obtain ⟨hCcomm, hCcard, -⟩ := four_group_centralizer_data hnonab hrec n hn S e hfour p f hp
    hpodd hf hq5 hq3 hmodel hst hcov
  obtain ⟨k₀, hk₀, hqk⟩ := exists_odd_add_one_eq hnonab n hn S e hfour p f hp hp2 hf hq3 hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z} with hC
  set P₂ := CFSG.Semidihedral.UnitaryDValue.commPrimaryPart C hCcomm 2 with hP₂
  have hAodd : Odd (Nat.card ((centralizerOddCore n S e).map
      (involutionCentralizer n S e).subtype)) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact centralizerOddCore_card_odd n S e
  have hP₂card : Nat.card P₂ = 2 ^ (2 * n) := by
    rw [hP₂, CFSG.Semidihedral.UnitaryDValue.card_commPrimaryPart, hCcard, hqk]
    congr 1
    set a := Nat.card ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    have hsplit : 2 ^ n * a * (2 ^ n * k₀) = 2 ^ (2 * n) * (a * k₀) := by ring
    have hodd : Odd (a * k₀) := hAodd.mul hk₀
    rw [hsplit, Nat.factorization_mul (by positivity) (by
        rintro h0; rw [h0] at hodd; exact absurd hodd (by decide)),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr h)), add_zero]
  have hxU : x ∈ modelBase S e := BrauerWong.modelHom_x_mem_modelBase S e
  have hzU : z ∈ modelBase S e := BrauerWong.modelHom_x2_mem_modelBase S e
  have hUC : modelBase S e ≤ C := fun u hu =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (BrauerWong.modelBase_commute S e _ _ hu hxU),
      Subgroup.mem_centralizer_singleton_iff.mpr (BrauerWong.modelBase_commute S e _ _ hu hzU)⟩
  have hUP : modelBase S e ≤ P₂ := by
    intro u hu
    refine ⟨hUC hu, ?_⟩
    have h := AdaptedBaseFusion.pow_modulus_eq_one_of_mem_modelBase S e hu
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
    exact ⟨k, hk⟩
  have hUeq : modelBase S e = P₂ := by
    apply Subgroup.eq_of_le_of_card_ge hUP
    rw [hP₂card, AdaptedBaseFusion.card_modelBase S e, ← pow_mul, mul_comm]
  have hcP : c ∈ P₂ := by
    refine ⟨hc, ?_⟩
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf c ∣ 2 ^ 1 by
      rw [pow_one]; exact h1)
    exact ⟨k, hk⟩
  have hcU : c ∈ modelBase S e := hUeq ▸ hcP
  have hcΩ : c ∈ BrauerWong.modelOmega S e :=
    (BrauerWong.mem_modelOmega_iff S e (by omega) c).mpr ⟨hcU, by rw [pow_two]; exact hcc⟩
  rw [BrauerWong.modelOmega, MonoidHom.map_closure, Set.image_pair] at hcΩ
  have hx2 : x * x = 1 := by
    rw [← pow_two, ← CompatibleFamilies.orderOf_x S e hn, pow_orderOf_eq_one]
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← CompatibleFamilies.orderOf_x2 S e hn, pow_orderOf_eq_one]
  exact mem_of_mem_closure_pair hx2 hz2 (BrauerWong.modelBase_commute S e _ _ hxU hzU) hcΩ

theorem real_odd_degree_of_wreathed
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index)
    (hreal : ∀ g, starRingEnd ℂ ((basis.representation χ).character g) =
      (basis.representation χ).character g)
    (hodd : Odd (Module.finrank ℂ (basis.representation χ).vector)) :
    Module.finrank ℂ (basis.representation χ).vector = 1 ∨
    Module.finrank ℂ (basis.representation χ).vector = (p ^ f) ^ 3 ∨
    Module.finrank ℂ (basis.representation χ).vector = (p ^ f) ^ 2 - p ^ f + 1 ∨
    Module.finrank ℂ (basis.representation χ).vector = p ^ f * ((p ^ f) ^ 2 - p ^ f + 1) := by
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hloc := ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hp2 hf hmodel
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 :=
    (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).2 ideal hmax hmem
  set principal := LinearLocalTwistMoment.principalCharacterLabel basis
  have hprincipal := LinearLocalTwistMoment.principalCharacterLabel_character basis
  have hB := CFSG.Semidihedral.Principal.real_valued_odd_degree_irreducible_mem_principal_two_block
    basis ideal principal hprincipal χ hreal hodd
  obtain ⟨A, B, D, χ', ψ, -, -, -, -, -, -, hdeg, -⟩ := unitary_principal_characters_of_localHyp
    n hn S e p f hp hp2 hf hloc rfl hq3 ideal basis principal hprincipal
  have h := hdeg χ hB
  set d := Module.finrank ℂ (basis.representation χ).vector with hd
  set q := p ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hqodd : Odd q := hpodd.pow
  obtain ⟨c, hc⟩ := hqodd
  have hdodd := hodd
  obtain ⟨k, hk⟩ := hdodd
  simp only at h
  rcases h with h | h | h | h | h | h | h
  · left; exact_mod_cast h
  · right; left; exact_mod_cast h
  · exfalso
    have : (d : ℤ) = 2 * (q * c) := by rw [h]; push_cast [hc]; ring
    omega
  · right; right; left
    zify [hqq]
    exact h
  · right; right; right
    zify [hqq]
    exact h
  · exfalso
    have : (d : ℤ) = 2 * (4 * c ^ 3 + 6 * c ^ 2 + 3 * c + 1) := by rw [h, hc]; push_cast; ring
    omega
  · exfalso
    have : (d : ℤ) = 2 * (c * (4 * c ^ 2 + 2 * c + 1)) := by rw [h, hc]; push_cast; ring
    omega

theorem principal_pair_of_wreathed
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (basis : FiniteIrreducibleCharacterBasis G) :
    ∃ χ₁ ψ : basis.index,
      Module.finrank ℂ (basis.representation χ₁).vector = (p ^ f) ^ 3 ∧
      Module.finrank ℂ (basis.representation ψ).vector = (p ^ f) ^ 3 + 1 ∧
      (basis.representation ψ).character (wreathModelHom S e (Original.x (2 ^ n))) =
        -(((p ^ f : ℕ) : ℂ) + 1) ∧
      ∀ g : G, Odd (orderOf g) →
        (basis.representation ψ).character g = (basis.representation χ₁).character g + 1 := by
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hloc := ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hp2 hf hmodel
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 :=
    (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).2 ideal hmax hmem
  obtain ⟨A, B, D, χ, ψ, hA, -, -, hχ, -, hχx, -, hrel⟩ := unitary_principal_characters_of_localHyp
    n hn S e p f hp hp2 hf hloc rfl hq3 ideal basis
    (LinearLocalTwistMoment.principalCharacterLabel basis)
    (LinearLocalTwistMoment.principalCharacterLabel_character basis)
  refine ⟨A, χ, ?_, ?_, hχx, fun g hg => ?_⟩
  · exact CFSG.BrauerLinearThree.QOne.finrank_eq_of_character_one basis A (by rw [hA]; norm_cast)
  · exact CFSG.BrauerLinearThree.QOne.finrank_eq_of_character_one basis χ (by rw [hχ]; norm_cast)
  · obtain ⟨h1, h2, -⟩ := hrel g hg
    rw [← h2, ← h1, add_comm]

open CFSG.Wreathed.PrimewiseConfinedCentralCore in
theorem character_extend_of_wreathed
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e)
    (θ₀ : ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) →* ℂˣ) :
    ∃ θ : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) →* ℂˣ,
      (∀ c : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G),
        (c : G) ∈ (S : Subgroup G) → θ c = 1) ∧
      ∀ (c : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G))
        (h : (c : G) ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype),
        θ c = θ₀ ⟨c, h⟩ := by
  obtain ⟨-, F, hF, hFfin, b, -, -, Φ, hΦinj, hΦN, hNΦ, hΦR⟩ :=
    exists_centralizer_model hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  set N := involutionCentralizer n S e
  let Φ' := Φ.codRestrict N hΦN
  have hbij : Function.Bijective Φ' := by
    refine ⟨fun a a' h => hΦinj (congrArg Subtype.val h), fun g => ?_⟩
    obtain ⟨z, hz⟩ := hNΦ g g.2
    exact ⟨z, Subtype.ext hz⟩
  let ν := MulEquiv.ofBijective Φ' hbij
  let ρ := Subgroup.equivMapOfInjective (centralizerOddCore n S e) N.subtype N.subtype_injective
  refine ⟨θ₀.comp (ρ.toMonoidHom.comp ((MonoidHom.fst _ _).comp ν.symm.toMonoidHom)), ?_, ?_⟩
  · intro c hc
    let c' : N := c
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨c, hc⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk' : orderOf c' = 2 ^ k := (Subgroup.orderOf_coe c').symm.trans hk
    have h1 : orderOf (ν.symm c').1 ∣ 2 ^ k := by
      rw [← hk', ← MulEquiv.orderOf_eq ν.symm c', Prod.orderOf]
      exact Nat.dvd_lcm_left _ _
    have h2 : orderOf (ν.symm c').1 ∣ Nat.card (centralizerOddCore n S e) := orderOf_dvd_natCard _
    have hodd : Odd (Nat.card (centralizerOddCore n S e)) := centralizerOddCore_card_odd n S e
    have hr1 : (ν.symm c').1 = 1 := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      rcases i with _ | i
      · rwa [pow_zero, orderOf_eq_one_iff] at hi
      · rw [hi, pow_succ] at h2
        exact absurd (dvd_trans (Dvd.intro_left _ rfl) h2) (by
          rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd)
    show θ₀ (ρ (ν.symm c').1) = 1
    rw [hr1, map_one, map_one]
  · intro c hc
    let c' : N := c
    obtain ⟨r, hr, hrc⟩ := id hc
    have hν : ν.symm c' = (⟨r, hr⟩, 1) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show (c : G) = Φ (⟨r, hr⟩, 1)
      rw [hΦR]
      exact hrc.symm
    show θ₀ (ρ (ν.symm c').1) = θ₀ ⟨c, hc⟩
    rw [hν]
    congr 1
    exact Subtype.ext hrc

theorem index_ne_two_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G) : H.index ≠ 2 := by
  intro h
  have hnorm : H.Normal := Subgroup.normal_of_index_eq_two h
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.index_bot] at h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card h
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [ht, Subgroup.index_top] at h
    exact absurd h (by norm_num)

open CFSG.Wreathed.PrimewiseConfinedCentralCore in
theorem exists_dValueData
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    ∃ D : CFSG.Semidihedral.UnitaryDValue.DValueData G, D.p = p ∧ D.f = f ∧ D.m = 2 ^ n ∧
      D.x = wreathModelHom S e (Original.x (2 ^ n)) ∧
      D.z = wreathModelHom S e (Original.x2 (2 ^ n)) ∧ D.S = S ∧
      D.A = (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ∧
      D.CharacterExtend ∧ D.PrincipalPair := by
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hconf :=
    ComponentCoverConfinement.stationarity_and_original_coverage_confine_all_odd_core_elements
      hnonab n hn S e hfour p f hp hpodd hf hq5 hmodel hrec hst hcov
  obtain ⟨-, -, -, -, hRcyc, hRcent, -, -, -, -, hNcard, -⟩ :=
    original_primewise_coverage_and_confinement_give_central_cyclic_odd_core
      hnonab n hn S e hfour p f hp hp2 hf hmodel hcov (fun r hr hr1 => (hconf r hr hr1).1)
  obtain ⟨K, hKcard, -, -, -, -, -, -, Q₀, -, -, -, -, H, -, -, -, -, hGK⟩ :=
    exists_centralizer_data hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  obtain ⟨k₀, hk₀, hqk₀⟩ := exists_odd_add_one_eq hnonab n hn S e hfour p f hp hp2 hf hq3 hmodel
  obtain ⟨hCcomm, hCcard, W, hWC, hWcyc, hWcard, hWA, hyW, hWcent⟩ :=
    four_group_centralizer_data hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  have hCinv := four_group_involutions hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel
    hst hcov
  obtain ⟨hbase, -, hinv, -, -⟩ := simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e
  obtain ⟨Y, -, hYx, hYz, -⟩ := BrauerWong.exists_base_three_cycle hn S e hbase
  obtain ⟨hRq, -⟩ :=
    exists_centralizer_model hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  set x : G := wreathModelHom S e (Original.x (2 ^ n)) with hx
  set z : G := wreathModelHom S e (Original.x2 (2 ^ n)) with hz
  set y : G := wreathModelHom S e (Original.z (2 ^ n)) with hy
  set N := involutionCentralizer n S e with hN
  set R := centralizerOddCore n S e with hR
  set A : Subgroup G := R.map N.subtype with hA
  have hxU : x ∈ modelBase S e := BrauerWong.modelHom_x_mem_modelBase S e
  have hzU : z ∈ modelBase S e := BrauerWong.modelHom_x2_mem_modelBase S e
  have hxz : x * z = z * x := BrauerWong.modelBase_commute S e _ _ hxU hzU
  have hxord : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hAcard : Nat.card A = Nat.card R := Subgroup.card_map_of_injective N.subtype_injective
  have hRodd : Odd (Nat.card R) := centralizerOddCore_card_odd n S e
  have hyS : y ∈ (S : Subgroup G) := BrauerWong.wreathModelHom_mem S e _
  have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, ← TorusSplitting.actual_orderOf_swap S e, pow_orderOf_eq_one])
  have hxy : x * y = y * x := by
    have h := BrauerWong.modelHom_x_central S e hn hyS
    calc x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by rw [h]
  have hyz : y * z * y⁻¹ = x * z := by
    have h := BrauerWong.modelHom_swap_conj_x2 S e
    rw [hyy] at h
    rw [hyy, h, BrauerWong.modelHom_x_mul_x2 S e (by omega)]
  have htx : Y⁻¹ * x * Y⁻¹⁻¹ = z := by rw [inv_inv]; exact hYx
  have htz : Y⁻¹ * z * Y⁻¹⁻¹ = x * z := by
    rw [inv_inv, hYz, BrauerWong.modelHom_x_mul_x2 S e (by omega)]
  have hAcent : ∀ a ∈ A, ∀ g ∈ Subgroup.centralizer ({x} : Set G), g * a = a * g := by
    rintro _ ⟨r, hr, rfl⟩ g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hRcent hr) ⟨g, hg⟩)
  have hAcyc : IsCyclic A := by
    let ρ := Subgroup.equivMapOfInjective R N.subtype N.subtype_injective
    exact isCyclic_of_surjective ρ.toMonoidHom ρ.surjective
  have hAdvd : 2 ^ n * Nat.card A ∣ p ^ f + 1 := by
    rw [hAcard]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hRodd)) ⟨k₀, hqk₀⟩ hRq
  have hGcard :
      Nat.card G = 2 ^ n * Nat.card A * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [hGK, hKcard, hAcard]
    ring
  have hNcard' : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      2 ^ n * Nat.card A * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
    rw [hAcard]
    change Nat.card N = _
    rw [hNcard]
    ring
  let D : CFSG.Semidihedral.UnitaryDValue.DValueData G :=
    { p := p, f := f, m := 2 ^ n, x := x, z := z, y := y, t := Y⁻¹, A := A, W := W, S := S,
      prime_p := hp, ne_two := hp2, one_le_f := hf, five_lt_q := by omega, m_pow := ⟨n, rfl⟩,
      m_dvd := ⟨k₀, hqk₀⟩,
      odd_quot := by rw [hqk₀, Nat.mul_div_cancel_left _ (by positivity)]; exact hk₀,
      index_ne_two := index_ne_two_of_simple hnonab, x_order := hxord,
      involution_conj := fun i hi => hinv i x hi hxord,
      z_order := CompatibleFamilies.orderOf_x2 S e hn, z_comm := hxz,
      z_ne := (BrauerWong.modelHom_x_ne_x2 S e (by omega)).symm,
      A_le := Subgroup.map_subtype_le R, A_central := hAcent, A_cyclic := hAcyc,
      A_odd := hAcard ▸ hRodd, A_dvd := hAdvd, A_confine := fun r hr hr1 => (hconf r hr hr1).2,
      card_G := hGcard, card_N := hNcard', card_C := hCcard, C_comm := hCcomm,
      C_involutions := hCinv, W_cyclic := hWcyc, W_card := hWcard, W_le := hWC, W_inf_A := hWA,
      y_comm := hxy, y_z := hyz, y_W := hyW, t_x := htx, t_z := htz,
      S_le := sylow_le_involutionCentralizer n hn S e, W_centralizer := hWcent,
      real_odd_degree := fun basis χ hreal hodd => real_odd_degree_of_wreathed hnonab n hn S e
        hfour p f hp hpodd hf hq3 hmodel basis χ hreal hodd }
  refine ⟨D, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro θ₀
    exact character_extend_of_wreathed hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel
      hst hcov θ₀
  · intro basis
    obtain ⟨χ₁, ψ, h1, h2, h3, h4⟩ := principal_pair_of_wreathed hnonab n hn S e hfour p f hp hpodd
      hf hq3 hmodel basis
    exact ⟨χ₁, ψ, h1, h2, Or.inr h3, h4⟩

end CFSG.Wreathed.SameFieldUnitary
