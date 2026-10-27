module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterSevenNineOrdersSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.FullPrimePartBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.Semidihedral.Local.DerivedInvolutionsConjugate
public import CFSG.CharacterTheory.BlockBasics.LocalRing

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem local_parameter_seven_rows_of_family {G : Type} [Group G] [Fintype G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 7 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = 7) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hOF : ActualPrincipalOrderFormulas G t (fS (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector)) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    let X : ℕ × ℕ := (Nat.card G, (C t).index)
    n = 5 ∧ Nat.card (C t) = 672 * a₀ * b₀ ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * a₀ ∧ δ₁ = -1 ∧
      ((Module.finrank ℂ (basis.representation χ₁).vector = 55 ∧
          X = (2328480 * a₀ * b₀ ^ 3, 3465 * b₀ ^ 2)) ∨
        (Module.finrank ℂ (basis.representation χ₁).vector = 343 ∧
          X = (1876896 * a₀ * b₀ ^ 3, 2793 * b₀ ^ 2))) := by
  intro CN a₀ b₀ X
  subst hq
  have he7 : e = -1 := by rw [he]; rfl
  subst he7
  have horder := cleared_first_order_formula (by norm_num) hOF
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨h2part, hCcard, hDcard⟩ := actual_layer_centralizer_orders hG n hn S fS t ht hnonab
    hcentral hnc 7 1 (by norm_num) (by decide) le_rfl hmodel
    (fun a _ ha => Nat.dvd_one.mp ha)
  simp only [pow_one] at h2part hCcard hDcard
  rw [ite_eq_right (by norm_num : ¬ 7 % 4 = 1)] at hDcard
  have hn5 : n = 5 := eq_five_of_modulus hn (by
    rw [← h2part, show (7 : ℕ) ^ 2 - 1 = 48 by norm_num, padicValNat_two_fortyEight])
  obtain ⟨hf₁, hf₂, hf₃, ho₁, ho₂, ho₃, hsigns, hsum, hprod, hc₁, hc₂⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal principal hprincipal
      localBasis localPrincipal 7 (by norm_num) (by decide) h2part (-1)
      (fun h => absurd h (by norm_num)) (fun _ => rfl) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg
  have hM : (2 : ℤ) * (modulus n : ℕ) = 32 := by subst hn5; rfl
  rw [hM] at hc₁ hc₂
  have hrows := (seven_nine_signed_degree_product_finite_alternatives).1 ((7 : ℕ) : ℤ) (-1)
    _ _ _ δ₁ δ₂ δ₃ (Or.inl ⟨by norm_num, rfl⟩) hf₁ hf₂ hf₃ ho₁ ho₂ ho₃ hsigns hsum hprod hc₁ hc₂
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hc : Nat.card (C t) = 672 * a₀ * b₀ := by rw [hCcard]; ring
  have hd : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * a₀ := by
    have h : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) = 12 * a₀ := by
      rw [hDcard]
      push_cast
      ring
    exact_mod_cast h
  rcases hrows with ⟨-, hδ, hfs⟩ | ⟨h9, -⟩
  · simp only [Prod.mk.injEq] at hδ
    obtain ⟨rfl, rfl, rfl⟩ := hδ
    refine ⟨hn5, hc, hd, rfl, ?_⟩
    rcases hfs with h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨h1, -, -⟩ := h
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 55 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inl ⟨by exact_mod_cast h1, order_pair_of_identity (C t) ha hb (by norm_num)
        (by norm_num) (by norm_num) hc hd horder (by norm_num) (by norm_num)⟩
    · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 343 := by
        exact_mod_cast h1
      rw [hf1] at horder
      exact Or.inr ⟨by exact_mod_cast h1, order_pair_of_identity (C t) ha hb (by norm_num)
        (by norm_num) (by norm_num) hc hd horder (by norm_num) (by norm_num)⟩
  · norm_num at h9

theorem odd_orderOf_of_prime_dvd_orderOf {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) {ℓ : ℕ} (hC : ¬ ℓ ∣ Nat.card (C t)) (x : G)
    (hx : ℓ ∣ orderOf x) : Odd (orderOf x) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  set v := x ^ (orderOf x / 2) with hv
  set w := x ^ (orderOf x / ℓ) with hw
  have hv2 : orderOf v = 2 := orderOf_pow_orderOf_div hx0 (even_iff_two_dvd.mp hodd)
  have hwℓ : orderOf w = ℓ := orderOf_pow_orderOf_div hx0 hx
  have hvw : Commute v w := Commute.pow_pow_self x _ _
  obtain ⟨-, -, hconj⟩ := CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn
    S fS
  have hvt : IsConj v t := by
    have h := (hconj Group.IsPerfect.commutator_eq_top v).mp hv2
    rw [ht]
    convert h using 1
  obtain ⟨g, hg⟩ := isConj_iff.mp hvt
  have hmem : g * w * g⁻¹ ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have h := hvw.eq
    calc g * w * g⁻¹ * (g * v * g⁻¹) = g * (w * v) * g⁻¹ := by group
      _ = g * (v * w) * g⁻¹ := by rw [h]
      _ = g * v * g⁻¹ * (g * w * g⁻¹) := by group
  have hord : orderOf (g * w * g⁻¹) = ℓ := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hwℓ]
  exact hC (hord ▸ Subgroup.orderOf_dvd_natCard (C t) hmem)

theorem padicValNat_seven_order_identity {a₀ b₀ : ℕ} (ha : 0 < a₀) (hb : 0 < b₀) :
    (padicValNat 7 (1876896 * a₀ * b₀ ^ 3) : ℤ) =
      3 * padicValNat 7 (672 * a₀ * b₀) - 2 * padicValNat 7 (12 * a₀) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 : padicValNat 7 1876896 = 3 := by
    rw [show (1876896 : ℕ) = 7 ^ 3 * 5472 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h2 : padicValNat 7 672 = 1 := by
    rw [show (672 : ℕ) = 7 ^ 1 * 96 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h3 : padicValNat 7 12 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by norm_num) ha.ne',
    padicValNat.pow, padicValNat.mul (by positivity) hb.ne', padicValNat.mul (by norm_num) ha.ne',
    padicValNat.mul (by norm_num) ha.ne', h1, h2, h3]
  push_cast
  ring

theorem perfect_local_parameter_seven_with_five_free_odd_core_is_regular
    {G : Type} [Group G]
    [Fintype G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 7 1)
    (h5 : ¬ 5 ∣ Nat.card (N t)) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    let c := Nat.card (C t)
    let d := Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})
    n = 5 ∧ c = 672 * a₀ * b₀ ∧ d = 12 * a₀ ∧ Nat.card G = 1876896 * a₀ * b₀ ^ 3 ∧
      (C t).index = 2793 * b₀ ^ 2 ∧
      (padicValNat 7 (Nat.card G) : ℤ) = 3 * padicValNat 7 c - 2 * padicValNat 7 d := by
  intro CN a₀ b₀ c d
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg,
      -, hOF⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc 7 1
      (by norm_num) (by decide) le_rfl hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal
  have hq7 : Nat.card F = 7 := by rw [hcard, pow_one]
  obtain ⟨hn5, hc, hd, hδ₁, hrow⟩ := local_parameter_seven_rows_of_family n hn S fS t ht hnonab
    hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal (Nat.card F)
    hq7 _ rfl _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg (hOF S fS hcent)
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hab : a₀ * b₀ = Nat.card (N t) := Subgroup.card_mul_index CN
  have h5a : ¬ 5 ∣ a₀ := fun h => h5 (hab ▸ dvd_mul_of_dvd_left h _)
  have h5b : ¬ 5 ∣ b₀ := fun h => h5 (hab ▸ dvd_mul_of_dvd_right h _)
  have h5c : ¬ 5 ∣ Nat.card (C t) := by
    rw [hc]
    intro h
    rcases (Nat.prime_five.dvd_mul).mp h with h | h
    · rcases (Nat.prime_five.dvd_mul).mp h with h | h
      · norm_num at h
      · exact h5a h
    · exact h5b h
  have hodd5 := odd_orderOf_of_prime_dvd_orderOf hn S fS ht h5c
  rcases hrow with ⟨hf55, hX⟩ | ⟨-, hX⟩
  ·
    exfalso
    have hGc : Nat.card G = 2328480 * a₀ * b₀ ^ 3 := congrArg Prod.fst hX
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hfac : (Nat.card G).factorization 5 = 1 := by
      have h1 : padicValNat 5 2328480 = 1 := by
        rw [show (2328480 : ℕ) = 5 ^ 1 * 465696 by norm_num,
          padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd (by norm_num)]
      rw [Nat.factorization_def _ Nat.prime_five, hGc,
        padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by norm_num) ha.ne',
        padicValNat.pow, h1, padicValNat.eq_zero_of_not_dvd h5a,
        padicValNat.eq_zero_of_not_dvd h5b]
    obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
    have hP : Nat.card P = 5 := by
      have h := Sylow.card_eq_multiplicity P
      rw [hfac, pow_one] at h
      exact h
    obtain ⟨⟨ideal₅, hmax₅, h5mem⟩, hchar₅⟩ :=
      CFSG.BlockBasics.residue_prime_existence 5 Nat.prime_five
    have : ideal₅.IsMaximal := hmax₅
    have : CharP (ComplexAlgebraicIntegers ⧸ ideal₅) 5 := hchar₅ ideal₅ hmax₅ h5mem
    obtain ⟨-, hvan⟩ := full_prime_part_character_degree_singleton_block_singular_vanishing
      basis ideal₅ 5 χ₁ (by rw [hfac, pow_one, hf55]; norm_num)
    obtain ⟨-, -, -, -, -, -, hψinj, hνinj, -, -, hνψ, -, -, -, -, hrel⟩ := hfam
    subst hn5
    let Λ : Finset basis.index := (Finset.Icc 1 (2 ^ (5 - 3) - 1)).image ψ ∪
      (Finset.range (2 ^ (5 - 3))).image ν
    have hΛ : ∀ η ∈ Λ, ∀ x : G, 5 ∣ orderOf x → (basis.representation η).character x = -1 := by
      intro η hη x hx
      obtain ⟨hψx, hνx, -, -⟩ := hrel x (hodd5 x hx)
      rcases Finset.mem_union.mp hη with hη | hη <;> obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hη
      · rw [hψx j hj, hvan x hx, hδ₁]
        push_cast
        ring
      · rw [hνx j hj, hvan x hx, hδ₁]
        push_cast
        ring
    have hΛcard : Λ.card = 7 := by
      rw [Finset.card_union_of_disjoint, Finset.card_image_of_injOn hψinj,
        Finset.card_image_of_injOn hνinj]
      · simp
      · rw [Finset.disjoint_left]
        intro a ha' hb'
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha'
        obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hb'
        exact hνψ i hi j hj hij
    have hbound :=
      (prime_order_sylow_principal_column_norm_bounds_constant_singular_characters basis ideal₅
        5 principal hprincipal P hP).2.2 Λ hΛ
    omega
  ·
    have hGc : Nat.card G = 1876896 * a₀ * b₀ ^ 3 := congrArg Prod.fst hX
    have hI : (C t).index = 2793 * b₀ ^ 2 := congrArg Prod.snd hX
    refine ⟨hn5, hc, hd, hGc, hI, ?_⟩
    change (padicValNat 7 (Nat.card G) : ℤ) = 3 * padicValNat 7 (Nat.card (C t)) -
      2 * padicValNat 7 (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}))
    rw [hGc, hc, hd]
    exact padicValNat_seven_order_identity ha hb

end CFSG.Semidihedral.Principal
