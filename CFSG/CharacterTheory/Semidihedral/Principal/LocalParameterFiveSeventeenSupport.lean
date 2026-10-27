module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterSevenRegular
public import CFSG.CharacterTheory.Semidihedral.Principal.FourGroupCosetDegreeBound
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.IsolatedCharacterField
public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.Schur

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem local_parameter_five_rows_of_family {G : Type} [Group G] [Fintype G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = 5) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
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
    let f₁ := Module.finrank ℂ (basis.representation χ₁).vector
    let f₂ := Module.finrank ℂ (basis.representation χ₂).vector
    let f₃ := Module.finrank ℂ (basis.representation χ₃).vector
    n = 4 ∧ Nat.card (C t) = 240 * a₀ * b₀ ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * a₀ ∧
      ((δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1 ∧ f₁ = 19 ∧ f₂ = 75 ∧ f₃ = 57 ∧
          X = (68400 * a₀ * b₀ ^ 3, 285 * b₀ ^ 2)) ∨
        (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1 ∧ f₁ = 125 ∧ f₂ = 21 ∧ f₃ = 105 ∧
          X = (126000 * a₀ * b₀ ^ 3, 525 * b₀ ^ 2)) ∨
        (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1 ∧ f₁ = 35 ∧ f₂ = 85 ∧ f₃ = 119 ∧
          X = (85680 * a₀ * b₀ ^ 3, 357 * b₀ ^ 2))) := by
  intro CN a₀ b₀ X f₁ f₂ f₃
  subst hq
  have he1 : e = 1 := by rw [he]; rfl
  subst he1
  have horder := cleared_first_order_formula (by norm_num) hOF
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨h2part, hCcard, hDcard⟩ := actual_layer_centralizer_orders hG n hn S fS t ht hnonab
    hcentral hnc 5 1 (by norm_num) (by decide) le_rfl hmodel
    (fun a _ ha => Nat.dvd_one.mp ha)
  simp only [pow_one] at h2part hCcard hDcard
  rw [ite_true] at hDcard
  have hn4 : n = 4 := eq_four_of_modulus hn (by
    rw [← h2part, show (5 : ℕ) ^ 2 - 1 = 24 by norm_num, padicValNat_two_twentyFour])
  have hqM : 2 ^ padicValNat 2 (5 ^ 2 - 1) = modulus n := h2part
  obtain ⟨hf₁, hf₂, hf₃, ho₁, ho₂, ho₃, hsigns, hsum, hprod, hc₁, hc₂⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal principal hprincipal
      localBasis localPrincipal 5 (by norm_num) (by decide) hqM 1 (fun _ => rfl)
      (fun h => absurd h (by norm_num)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg
  have hM : (2 : ℤ) * (modulus n : ℕ) = 16 := by subst hn4; rfl
  rw [hM] at hc₁ hc₂
  have hrows := (five_signed_degree_product_three_alternatives).1 _ _ _ δ₁ δ₂ δ₃ hf₁ hf₂ hf₃
    ho₁ ho₂ ho₃ hsigns hsum (by rw [hprod]; norm_num)
    (by have h := hc₁; rw [show δ₁ * (2 - 1 * ((5 : ℕ) : ℤ)) = -3 * δ₁ by push_cast; ring] at h
        exact h)
    (by have h := hc₂; rw [show -δ₂ * 1 * ((5 : ℕ) : ℤ) = -5 * δ₂ by push_cast; ring] at h
        exact h)
  have hCt : Nat.card (C t) = 240 * a₀ * b₀ := by rw [hCcard]; ring
  have hDt : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * a₀ := by
    have h : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) = 12 * a₀ := by
      rw [hDcard]
      push_cast
      ring
    exact_mod_cast h
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  refine ⟨hn4, hCt, hDt, ?_⟩
  rcases hrows with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨⟨rfl, rfl, rfl⟩, h1, h2, h3⟩ := h
  · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 19 := by
      exact_mod_cast h1
    rw [hf1] at horder
    exact Or.inl ⟨rfl, rfl, rfl, by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
      order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num) (by norm_num) hCt hDt horder
        (by norm_num) (by norm_num)⟩
  · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 125 := by
      exact_mod_cast h1
    rw [hf1] at horder
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl, by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
        (by norm_num) hCt hDt horder (by norm_num) (by norm_num)⟩)
  · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 35 := by
      exact_mod_cast h1
    rw [hf1] at horder
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
        (by norm_num) hCt hDt horder (by norm_num) (by norm_num)⟩)

theorem isPerfect_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    have hcomm := isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)
    exact (hab (hcomm a b)).elim
  · exact h

theorem sum_character_comp_hom_eq {D G : Type} [Group D] [Fintype D] [Group G] (f : D →* G)
    (θ : FiniteComplexRepresentation.{0, 0} G) :
    ∃ m : ℕ, ∑ x : D, θ.character (f x) = (Nat.card D : ℂ) * m := by
  obtain ⟨b⟩ := finiteIrreducibleCharacterBasis_exists (G := D)
  obtain ⟨p0, hp0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible b
    (principalFiniteComplexRepresentation D) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hp0
  obtain ⟨m, hm⟩ := characterPairing_basis_natural b (inflatedFiniteComplexRepresentation f θ) p0
  refine ⟨m, ?_⟩
  unfold characterPairing at hm
  rw [hp0] at hm
  simp only [Pi.one_apply, mul_one] at hm
  have hcard : (Nat.card D : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [← hm, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  rfl

theorem supplied_four_group_isKleinFour {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 4 ≤ n)
    {S : Subgroup G} (fS : SemidihedralGroup n ≃* S) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    IsKleinFour (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) := by
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  let s₀ : C t := ⟨(fS (s n) : G), hsC⟩
  have ht2' : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
  have hs2' : orderOf s₀ = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hne : tInC t ≠ s₀ := fun h => hst (congrArg Subtype.val h).symm
  have hV := KleinFourOddKernel.fourSubgroup_isKleinFour (tInC t) s₀ (tInC_central t) ht2' hs2'
    hne
  have hmap : (KleinFourOddKernel.fourSubgroup (tInC t) s₀).map (C t).subtype =
      Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) := by
    rw [KleinFourOddKernel.fourSubgroup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    rfl
  let e := Subgroup.equivMapOfInjective (KleinFourOddKernel.fourSubgroup (tInC t) s₀)
    (C t).subtype Subtype.val_injective
  rw [← hmap]
  exact ⟨(Nat.card_congr e.toEquiv).symm.trans hV.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans hV.exponent_two⟩

theorem exists_inverting_involution_seventeen {G : Type*} [Group G] [Finite G] {u h : G}
    (hu : orderOf u = 17) (hnorm : h * u * h⁻¹ ∈ Subgroup.zpowers u) (hnc : h * u * h⁻¹ ≠ u)
    (hinv : ∀ x : G, orderOf x = 2 → x * u * x⁻¹ ≠ u) :
    ∃ w : G, orderOf w = 2 ∧ w * u * w⁻¹ = u⁻¹ := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hu17 : u ^ 17 = 1 := hu ▸ pow_orderOf_eq_one u
  obtain ⟨k, hk⟩ : ∃ k : ℕ, h * u * h⁻¹ = u ^ k := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hnorm
    refine ⟨(i % 17).toNat, ?_⟩
    rw [← hi, zpow_eq_zpow_emod' i hu17, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    rfl
  have hpow : ∀ j : ℕ, h ^ j * u * (h ^ j)⁻¹ = u ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc h ^ (j + 1) * u * (h ^ (j + 1))⁻¹ = h * (h ^ j * u * (h ^ j)⁻¹) * h⁻¹ := by group
        _ = h * u ^ (k ^ j) * h⁻¹ := by rw [ih]
        _ = (h * u * h⁻¹) ^ (k ^ j) := by rw [conj_pow]
        _ = u ^ (k ^ (j + 1)) := by rw [hk, ← pow_mul, pow_succ', mul_comm]
  have hmod : ∀ a : ℕ, u ^ a = u ↔ (a : ZMod 17) = 1 := by
    intro a
    rw [show u ^ a = u ↔ u ^ a = u ^ 1 by rw [pow_one], pow_eq_pow_iff_modEq, hu,
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  have hkey : ∀ j : ℕ, h ^ j * u * (h ^ j)⁻¹ = u ↔ (k : ZMod 17) ^ j = 1 := by
    intro j
    rw [hpow j, hmod, Nat.cast_pow]
  have hk1 : (k : ZMod 17) ≠ 1 := fun h1 => hnc (by
    have := (hkey 1).mpr (by rw [pow_one]; exact h1)
    simpa using this)
  have hk0 : (k : ZMod 17) ≠ 0 := by
    intro h0
    have h17 : 17 ∣ k := (ZMod.natCast_eq_zero_iff k 17).mp h0
    obtain ⟨c, rfl⟩ := h17
    have h1 : h * u * h⁻¹ = 1 := by rw [hk, pow_mul, hu17, one_pow]
    have : u = 1 := by
      have := congrArg (fun x => h⁻¹ * x * h) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hk16 : (k : ZMod 17) ^ 16 = 1 := ZMod.pow_card_sub_one_eq_one hk0
  have hm0 : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨a, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hgcd : Nat.gcd m' 16 = 1 := by
    have := (Nat.coprime_two_right.mpr hm').pow_right 4
    simpa using this
  have hkm' : (k : ZMod 17) ^ m' ≠ 1 := by
    intro h1
    apply hk1
    have h2 : (k : ZMod 17) ^ Nat.gcd m' 16 = 1 := pow_gcd_eq_one.mpr ⟨h1, hk16⟩
    rwa [hgcd, pow_one] at h2
  set h' := h ^ m' with hh'
  have hm'0 : m' ≠ 0 := fun h0 => by rw [h0] at hm'; exact absurd hm' (by decide)
  have hord' : orderOf h' = 2 ^ a := by
    rw [hh', orderOf_pow' h hm'0, hm, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (by omega)]
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hord'
    apply hkm'
    have := (hkey m').mp (by rw [← hh', hord']; group)
    exact this
  set w := h' ^ (orderOf h' / 2) with hw
  have h2dvd : 2 ∣ orderOf h' := by
    rw [hord']
    exact dvd_pow_self 2 ha
  have hw2 : orderOf w = 2 := orderOf_pow_orderOf_div (by rw [hord']; positivity) h2dvd
  set J := m' * (orderOf h' / 2) with hJ
  have hwJ : w = h ^ J := by rw [hw, hh', ← pow_mul]
  have hJ1 : (k : ZMod 17) ^ J ≠ 1 := by
    intro h1
    apply hinv w hw2
    rw [hwJ]
    exact (hkey J).mpr h1
  have hJ2 : ((k : ZMod 17) ^ J) * ((k : ZMod 17) ^ J) = 1 := by
    rw [← pow_add, ← two_mul]
    apply (hkey (2 * J)).mp
    have hw1 : w ^ 2 = 1 := hw2 ▸ pow_orderOf_eq_one w
    rw [pow_mul', ← hwJ, hw1]
    group
  have hJm1 : (k : ZMod 17) ^ J = -1 := (mul_self_eq_one_iff.mp hJ2).resolve_left hJ1
  refine ⟨w, hw2, ?_⟩
  rw [hwJ, hpow J]
  have h16 : (k ^ J : ℕ) ≡ 16 [MOD 17] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, hJm1]
    rfl
  rw [show u⁻¹ = u ^ 16 by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hu17]]
  rw [← hu] at h16
  exact (pow_eq_pow_iff_modEq.mpr h16)

@[expose] def dihedralHomOfInverting {G : Type*} [Group G] (n : ℕ) [NeZero n] (u w : G)
    (hu : u ^ n = 1) (hw : w * w = 1) (hwu : w * u * w⁻¹ = u⁻¹) : DihedralGroup n →* G where
  toFun x := match x with
    | DihedralGroup.r i => u ^ i.val
    | DihedralGroup.sr i => w * u ^ i.val
  map_one' := by
    show u ^ (0 : ZMod n).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hA : ∀ a b : ZMod n, u ^ a.val * u ^ b.val = u ^ (a + b).val := fun a b => by
      rw [← pow_add, pow_eq_pow_mod (a.val + b.val) hu, ← ZMod.val_add]
    have hB : ∀ i j : ZMod n, u ^ (j - i).val = (u ^ i.val)⁻¹ * u ^ j.val := fun i j => by
      apply eq_inv_mul_of_mul_eq
      rw [hA, add_sub_cancel]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
    have hC : ∀ k : ℕ, u ^ k * w = w * (u ^ k)⁻¹ := fun k => by
      have h1 : w * u ^ k * w⁻¹ = (u ^ k)⁻¹ := by rw [← conj_pow, hwu, inv_pow]
      calc u ^ k * w = w * (w⁻¹ * u ^ k * w) := by group
        _ = w * (w * u ^ k * w⁻¹) := by rw [hwinv]
        _ = w * (u ^ k)⁻¹ := by rw [h1]
    rintro (i | i) (j | j)
    · show u ^ (i + j).val = u ^ i.val * u ^ j.val
      rw [hA]
    · show w * u ^ (j - i).val = u ^ i.val * (w * u ^ j.val)
      rw [← mul_assoc, hC, hB, mul_assoc]
    · show w * u ^ (i + j).val = w * u ^ i.val * u ^ j.val
      rw [mul_assoc, hA]
    · show u ^ (j - i).val = w * u ^ i.val * (w * u ^ j.val)
      rw [hB, mul_assoc w, ← mul_assoc (u ^ i.val), hC, ← mul_assoc, ← mul_assoc, hw, one_mul]

theorem sum_dihedralGroup {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    (F : DihedralGroup n → M) :
    ∑ x, F x = ∑ i : ZMod n, F (DihedralGroup.r i) + ∑ i : ZMod n, F (DihedralGroup.sr i) := by
  rw [show (∑ i : ZMod n, F (DihedralGroup.r i) + ∑ i : ZMod n, F (DihedralGroup.sr i)) =
      ∑ x : ZMod n ⊕ ZMod n, F (DihedralGroup.equivSum.symm x) from
    (Fintype.sum_sum_type (fun x => F (DihedralGroup.equivSum.symm x))).symm]
  exact Fintype.sum_equiv DihedralGroup.equivSum _ _ (fun x => by cases x <;> rfl)

theorem not_dihedral_seventeen_character {G : Type} [Group G] [Fintype G]
    (θ : FiniteComplexRepresentation.{0, 0} G) {u w : G} (hu : orderOf u = 17)
    (hw2 : orderOf w = 2) (hwu : w * u * w⁻¹ = u⁻¹) (h1 : θ.character 1 = 35)
    (hP : ∀ i : ℕ, 0 < i → i < 17 → θ.character (u ^ i) = 1)
    (hinv : ∀ x : G, orderOf x = 2 → θ.character x = -5) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu17 : u ^ 17 = 1 := hu ▸ pow_orderOf_eq_one u
  have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  let f := dihedralHomOfInverting 17 u w hu17 hww hwu
  obtain ⟨m, hm⟩ := sum_character_comp_hom_eq f θ
  rw [sum_dihedralGroup, DihedralGroup.nat_card] at hm
  have hr : ∑ i : ZMod 17, θ.character (f (DihedralGroup.r i)) = 51 := by
    change ∑ i : Fin 17, θ.character (u ^ (i : ℕ)) = 51
    rw [← Finset.sum_range (fun i => θ.character (u ^ i)), Finset.sum_range_succ', pow_zero, h1,
      Finset.sum_congr rfl (fun i hi => hP (i + 1) (by omega)
        (by have := Finset.mem_range.mp hi; omega))]
    simp
    norm_num
  have hsr : ∑ i : ZMod 17, θ.character (f (DihedralGroup.sr i)) = -85 := by
    change ∑ i : Fin 17, θ.character (w * u ^ (i : ℕ)) = -85
    have hall : ∀ k : ℕ, θ.character (w * u ^ k) = -5 := by
      intro k
      apply hinv
      apply orderOf_eq_prime
      · have hC : u ^ k * w = w * (u ^ k)⁻¹ := by
          have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
          have h1 : w * u ^ k * w⁻¹ = (u ^ k)⁻¹ := by rw [← conj_pow, hwu, inv_pow]
          calc u ^ k * w = w * (w⁻¹ * u ^ k * w) := by group
            _ = w * (w * u ^ k * w⁻¹) := by rw [hwinv]
            _ = w * (u ^ k)⁻¹ := by rw [h1]
        rw [pow_two]
        calc w * u ^ k * (w * u ^ k) = w * (u ^ k * w) * u ^ k := by group
          _ = w * (w * (u ^ k)⁻¹) * u ^ k := by rw [hC]
          _ = (w * w) * ((u ^ k)⁻¹ * u ^ k) := by group
          _ = 1 := by rw [hww, inv_mul_cancel, one_mul]
      · intro h
        have hw' : w = (u ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h
        have hdvd : orderOf w ∣ 17 := by
          rw [hw', orderOf_inv, ← hu]
          exact orderOf_pow_dvd k
        rw [hw2] at hdvd
        norm_num at hdvd
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [hr, hsr] at hm
  have hm' : ((2 * 17 : ℕ) : ℂ) * (m : ℂ) = -34 := by rw [← hm]; norm_num
  have : (34 : ℤ) * m = -34 := by exact_mod_cast hm'
  omega

theorem mem_oddCore_of_pow_seventeen {G : Type} [Group G] [Finite G] {t s₀ : G}
    (hD : Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀}) =
      12 * Nat.card (((Subgroup.centralizer {s₀}).comap (C t).subtype).subgroupOf (N t)))
    {y : G} (hyC : y ∈ C t) (hys : y ∈ Subgroup.centralizer {s₀}) (hy : y ^ 17 = 1) :
    (⟨y, hyC⟩ : C t) ∈ N t := by
  set Ds : Subgroup (C t) := (Subgroup.centralizer {s₀}).comap (C t).subtype with hDs
  set K : Subgroup Ds := (N t).subgroupOf Ds with hK
  have hcardDs : Nat.card Ds = Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀}) := by
    rw [← Subgroup.card_map_of_injective (K := Ds) (f := (C t).subtype)
      (C t).subtype_injective, hDs, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hcardK : Nat.card K = Nat.card (Ds.subgroupOf (N t)) := by
    rw [hK, ← Subgroup.card_map_of_injective (K := (N t).subgroupOf Ds) (f := Ds.subtype)
        Ds.subtype_injective, Subgroup.subgroupOf_map_subtype,
      ← Subgroup.card_map_of_injective (K := Ds.subgroupOf (N t)) (f := (N t).subtype)
        (N t).subtype_injective, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hindex : K.index = 12 := by
    have h := Subgroup.card_mul_index K
    rw [hcardDs, hD, ← hcardK] at h
    have h' : Nat.card K * K.index = Nat.card K * 12 := by rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  have : K.Normal := Subgroup.Normal.subgroupOf inferInstance Ds
  let yD : Ds := ⟨⟨y, hyC⟩, by
    change y ∈ Subgroup.centralizer {s₀}
    exact hys⟩
  have hyD : yD ^ 17 = 1 := Subtype.ext (Subtype.ext hy)
  have h12 : yD ^ 12 ∈ K := hindex ▸ Subgroup.pow_index_mem K yD
  have hyD' : yD = (yD ^ 12) ^ 10 := by
    rw [← pow_mul, show 12 * 10 = 17 * 7 + 1 by norm_num, pow_add, pow_mul, hyD, one_pow,
      one_mul, pow_one]
  have hmem : yD ∈ K := hyD' ▸ K.pow_mem h12 10
  exact hmem

theorem seventeen_not_dvd_card_oddCore_centralizer {G : Type} [Group G] [Fintype G] {n : ℕ}
    (hn : 4 ≤ n) {S : Subgroup G} (fS : SemidihedralGroup n ≃* S) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G), v ≠ 1 →
      ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t)
    (θ : FiniteComplexRepresentation.{0, 0} G) (hdeg : Module.finrank ℂ θ.vector = 35)
    (hrat : ∀ g, ∃ q : ℚ, θ.character g = q) (hfaith : Function.Injective θ.representation)
    (htval : θ.character t = -5) (hNval : ∀ y : C t, y ∈ N t → θ.character (t * y) = -5)
    (hD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) =
      12 * Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
        (N t))) :
    ¬ 17 ∣ Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
      (N t)) := by
  intro h17
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) with hV
  have : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  obtain ⟨-, ht2, -, hsC, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 17 h17
  set u : G := (((x : N t) : C t) : G) with hu
  have hu17 : orderOf u = 17 := by
    rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have huC : u ∈ C t := ((x : N t) : C t).property
  have hus : u ∈ Subgroup.centralizer {(fS (s n) : G)} := (Subgroup.mem_subgroupOf.mp x.property)
  set P : Subgroup G := Subgroup.zpowers u with hP
  have hPcard : Nat.card P = 17 := by rw [hP, Nat.card_zpowers, hu17]
  have hPV : P ≤ Subgroup.centralizer V := by
    rw [hP, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro v hv
    have hle : V ≤ Subgroup.centralizer {u} := by
      rw [hV]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp huC).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hus).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv))
  have hconst : ∀ v ∈ V, v ≠ 1 → ∀ z ∈ P, θ.representation.character (v * z) =
      θ.representation.character v := by
    intro v hv hv1 z hz
    obtain ⟨g, hg, hgv⟩ := hfus v hv hv1
    have hzV : z ∈ Subgroup.centralizer V := hPV hz
    have hyV : g * z * g⁻¹ ∈ Subgroup.centralizer V := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : g⁻¹ * w * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hzV _ hw'
      calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
        _ = g * z * g⁻¹ * w := by group
    have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have hsV : (fS (s n) : G) ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hyC : g * z * g⁻¹ ∈ C t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyV t htV).symm
    have hys : g * z * g⁻¹ ∈ Subgroup.centralizer {(fS (s n) : G)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyV _ hsV).symm
    have hz17 : z ^ 17 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu17,
        pow_orderOf_eq_one, one_zpow]
    have hy17 : (g * z * g⁻¹) ^ 17 = 1 := by rw [conj_pow, hz17]; group
    have hyN := mem_oddCore_of_pow_seventeen hD hyC hys hy17
    have hval := hNval ⟨g * z * g⁻¹, hyC⟩ hyN
    have hconj : θ.representation.character (v * z) =
        θ.representation.character (g * (v * z) * g⁻¹) :=
      (Representation.char_conj θ.representation (v * z) g).symm
    rw [hconj, show g * (v * z) * g⁻¹ = (g * v * g⁻¹) * (g * z * g⁻¹) by group, hgv]
    have hconjv : θ.representation.character v =
        θ.representation.character (g * v * g⁻¹) :=
      (Representation.char_conj θ.representation v g).symm
    rw [hconjv, hgv]
    exact hval.trans htval.symm
  have hker : ¬ P ≤ MonoidHom.ker θ.representation := by
    intro hle
    have huker : u ∈ MonoidHom.ker θ.representation := hle (Subgroup.mem_zpowers u)
    have hu1 : u = 1 := hfaith ((MonoidHom.mem_ker.mp huker).trans (map_one _).symm)
    rw [hu1, orderOf_one] at hu17
    norm_num at hu17
  obtain ⟨-, hbound⟩ := four_group_central_prime_coset_constant_degree_bound θ.representation V
    P hPV (by norm_num : Nat.Prime 17) (by decide) hPcard
    (fun z _ => hrat z) hker hconst
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    norm_num at ht2
  have h := hbound t htV ht1
  rw [show θ.representation.character t = -5 from htval, hdeg] at h
  norm_num at h

theorem isConj_of_orderOf_eq_two {G : Type} [Group G] [Finite G] [Group.IsPerfect G] {n : ℕ}
    (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) {x : G} (hx : orderOf x = 2) : IsConj x t := by
  obtain ⟨-, -, hconj⟩ := CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn
    S fS
  have h := (hconj Group.IsPerfect.commutator_eq_top x).mp hx
  rw [ht]
  convert h using 1

theorem local_parameter_five_seventeen_excluded_of_family {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = 5) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hOF : ActualPrincipalOrderFormulas G t (fS (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector))
    (hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G), v ≠ 1 →
      ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    let X : ℕ × ℕ := (Nat.card G, (C t).index)
    (X = (68400 * a₀ * b₀ ^ 3, 285 * b₀ ^ 2) ∨ X = (126000 * a₀ * b₀ ^ 3, 525 * b₀ ^ 2)) ∧
      Nat.card G ≠ 85680 * a₀ * b₀ ^ 3 := by
  intro CN a₀ b₀ X
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  obtain ⟨hn4, hCt, hDt, hrows⟩ := local_parameter_five_rows_of_family n hn S fS t ht hnonab
    hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal q hq e he φ δ₁
    δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg hOF
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hne : ∀ K : ℕ, K ≠ 85680 → Nat.card G = K * a₀ * b₀ ^ 3 →
      Nat.card G ≠ 85680 * a₀ * b₀ ^ 3 := by
    intro K hK h h'
    rw [h] at h'
    apply hK
    have h'' : K * (a₀ * b₀ ^ 3) = 85680 * (a₀ * b₀ ^ 3) := by
      rw [← mul_assoc, h', mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h''
  rcases hrows with ⟨-, -, -, -, -, -, hX⟩ | ⟨-, -, -, -, -, -, hX⟩ |
    ⟨hδ₁, hδ₂, hδ₃, hf₁, hf₂, hf₃, hX⟩
  · exact ⟨Or.inl hX, hne 68400 (by norm_num) (congrArg Prod.fst hX)⟩
  · exact ⟨Or.inr hX, hne 126000 (by norm_num) (congrArg Prod.fst hX)⟩
  exfalso
  have hGcard : Nat.card G = 85680 * a₀ * b₀ ^ 3 := congrArg Prod.fst hX
  subst hq
  have he1 : e = 1 := by rw [he]; rfl
  subst he1 hδ₁ hδ₂ hδ₃ hn4
  obtain ⟨hlφ, -, -, -, -, hnd, hψinj, hνinj, hψx, hνx, hνψ, hB, -, hodd, hsec, hrel⟩ := hfam
  obtain ⟨-, -, -, -, -, -, hf₄, -, -⟩ := hdeg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨lφ, -, -, hφchar, hφdeg, hφker⟩ := hlφ
  have hφN : ∀ y : C t, y ∈ N t → φ y = 5 := by
    intro y hy
    have hyker : y ∈ MonoidHom.ker (localBasis.representation lφ).representation := by
      rw [hφker]
      exact Subgroup.mem_sup_left hy
    have hρ : (localBasis.representation lφ).representation y =
        (localBasis.representation lφ).representation 1 := by
      rw [MonoidHom.mem_ker.mp hyker, map_one]
    rw [← hφchar]
    change LinearMap.trace ℂ _ ((localBasis.representation lφ).representation y) = 5
    rw [hρ]
    change (localBasis.representation lφ).character 1 = 5
    rw [(basis_character_one localBasis lφ).1, hφdeg]
    norm_num
  have hNodd : ∀ y : C t, y ∈ N t → Odd (orderOf y) := by
    intro y hy
    have hcop : Nat.Coprime 2 (Nat.card (N t)) := CFSG.pPrimeCore_coprime_card
    have hdvd : orderOf (⟨y, hy⟩ : N t) ∣ Nat.card (N t) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h2 =>
      absurd (Nat.Coprime.coprime_dvd_right hdvd hcop) (by
        rw [Nat.coprime_two_left]; exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))))
  have hNval : ∀ y : C t, y ∈ N t →
      (basis.representation χ₁).character (t * y) = -5 := by
    intro y hy
    rw [(hsec y (hNodd y hy)).1, hφN y hy]
    norm_num
  have htval : (basis.representation χ₁).character t = -5 := by
    have h := hNval 1 (one_mem _)
    rwa [OneMemClass.coe_one, mul_one] at h
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hdeg1 : ∀ c : basis.index, (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) :=
    fun c => (basis_character_one basis c).1
  have hχ₁1 : (basis.representation χ₁).character 1 = 35 := by rw [hdeg1, hf₁]; norm_num
  obtain ⟨hψ1, hν1, -, -⟩ := hrel 1 (by rw [orderOf_one]; exact odd_one)
  have hψdeg : ∀ j ∈ Finset.Icc 1 (2 ^ (4 - 3) - 1),
      (basis.representation (ψ j)).character 1 = 34 := by
    intro j hj
    rw [hψ1 j hj, hχ₁1]
    norm_num
  have hνdeg : ∀ i ∈ Finset.range (2 ^ (4 - 3)),
      (basis.representation (ν i)).character 1 = 34 := by
    intro i hi
    rw [hν1 i hi, hχ₁1]
    norm_num
  have hrat : ∀ g, ∃ q : ℚ, (basis.representation χ₁).character g = q := by
    intro g
    apply CFSG.LyonsUnitaryFour.character_rat_of_isolated_principal_block basis ideal hprincipal
      hχ₁B {1} (fun x hx => ⟨35, by rw [Set.mem_singleton_iff.mp hx, hχ₁1]; norm_num⟩)
    intro b hb hbval
    have hb1 := hbval 1 (Set.mem_singleton 1)
    rw [hχ₁1] at hb1
    have hb' : b ∈ B := hb
    rw [hB] at hb'
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at hb'
    rcases hb' with ((h | h | h | h | h) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [h, hprincipal] at hb1
      norm_num at hb1
    · exact h
    · rw [h, hdeg1, hf₂] at hb1
      norm_num at hb1
    · rw [h, hdeg1, hf₃] at hb1
      norm_num at hb1
    · rw [h, hdeg1] at hb1
      have h84 : (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = 84 := by
        rw [hf₄, hf₂]
        norm_num
      have : (Module.finrank ℂ (basis.representation χ₄).vector : ℂ) = 84 := by
        exact_mod_cast h84
      rw [this] at hb1
      norm_num at hb1
    · rw [hψdeg j hj] at hb1
      norm_num at hb1
    · rw [hνdeg i hi] at hb1
      norm_num at hb1
  have hfaith : Function.Injective (basis.representation χ₁).representation := by
    rcases (MonoidHom.normal_ker (basis.representation χ₁).representation).eq_bot_or_eq_top
      with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).mp h
    · exfalso
      have htker : t ∈ MonoidHom.ker (basis.representation χ₁).representation := h ▸ trivial
      have h1 : (basis.representation χ₁).character t =
          (basis.representation χ₁).character 1 := by
        change LinearMap.trace ℂ _ ((basis.representation χ₁).representation t) =
          LinearMap.trace ℂ _ ((basis.representation χ₁).representation 1)
        rw [MonoidHom.mem_ker.mp htker, (basis.representation χ₁).representation.map_one]
      rw [htval, hχ₁1] at h1
      norm_num at h1
  obtain ⟨P17⟩ : Nonempty (Sylow 17 G) := inferInstance
  have hschur := CFSG.LyonsUnitaryFour.sylow_card_dvd_of_faithful_rational_character
    (basis.representation χ₁) hfaith hrat P17
  rw [hf₁, show (35 : ℕ) / (17 - 1) = 2 by norm_num, Nat.factorial_two] at hschur
  have hcardP := Sylow.card_eq_multiplicity P17
  have hfac_le : (Nat.card G).factorization 17 ≤ 2 := by
    by_contra hk
    push Not at hk
    have h3 : 17 ^ 3 ∣ Nat.card P17 := by
      rw [hcardP]
      exact pow_dvd_pow 17 hk
    have := h3.trans hschur
    norm_num at this
  have h85680 : padicValNat 17 85680 = 1 := by
    rw [show (85680 : ℕ) = 17 ^ 1 * 5040 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hval : (Nat.card G).factorization 17 =
      1 + padicValNat 17 a₀ + 3 * padicValNat 17 b₀ := by
    rw [Nat.factorization_def _ (by norm_num), hGcard,
      padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by norm_num) ha.ne',
      padicValNat.pow, h85680]
  have h17b : ¬ 17 ∣ b₀ := fun h => by
    have := one_le_padicValNat_of_dvd hb.ne' h
    omega
  have h17a : ¬ 17 ∣ a₀ := seventeen_not_dvd_card_oddCore_centralizer hn fS ht hfus
    (basis.representation χ₁) hf₁ hrat hfaith htval hNval hDt
  have hfac1 : (Nat.card G).factorization 17 = 1 := by
    rw [hval, padicValNat.eq_zero_of_not_dvd h17a, padicValNat.eq_zero_of_not_dvd h17b]
  have hP17 : Nat.card P17 = 17 := by rw [hcardP, hfac1, pow_one]
  have h17C : ¬ 17 ∣ Nat.card (C t) := by
    rw [hCt]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
    · rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
      · norm_num at h
      · exact h17a h
    · exact h17b h
  have hNC : ¬ (Subgroup.normalizer ((P17 : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((P17 : Subgroup G) : Set G)) := by
    intro hle
    obtain ⟨K, hKn, -, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement P17 hle
    rcases hKn.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.index_bot, hP17, hGcard] at hKidx
      have h1 : 1 ≤ a₀ * b₀ ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    · rw [h, Subgroup.index_top, hP17] at hKidx
      norm_num at hKidx
  obtain ⟨h, hhN, hhC⟩ := IsConcreteLE.not_le_iff_exists.mp hNC
  obtain ⟨u, huP, hu1⟩ : ∃ u ∈ (P17 : Subgroup G), u ≠ 1 := by
    by_contra! hall
    have hbot : (P17 : Subgroup G) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [hbot, Subgroup.card_bot] at hP17
    norm_num at hP17
  have hu17 : orderOf u = 17 := orderOf_eq_prime_of_mem_of_card_eq hP17 huP hu1
  have hPu : (P17 : Subgroup G) = Subgroup.zpowers u := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact huP
    · rw [hP17, Nat.card_zpowers, hu17]
  have hnorm : h * u * h⁻¹ ∈ Subgroup.zpowers u := by
    rw [← hPu]
    exact (Subgroup.mem_normalizer_iff.mp hhN u).mp huP
  have hnc : h * u * h⁻¹ ≠ u := by
    intro heq
    apply hhC
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hPu] at hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcomm : Commute u h := by
      have : h * u = u * h := by
        calc h * u = h * u * h⁻¹ * h := by group
          _ = u * h := by rw [heq]
      exact this.symm
    exact (hcomm.zpow_left k).eq
  have hinv : ∀ x : G, orderOf x = 2 → x * u * x⁻¹ ≠ u := by
    intro x hx heq
    have hcomm : Commute x u := by
      have : x * u = u * x := by
        calc x * u = x * u * x⁻¹ * x := by group
          _ = u * x := by rw [heq]
      exact this
    have hord : orderOf (x * u) = 2 * 17 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hu17]; norm_num), hx, hu17]
    have hodd := odd_orderOf_of_prime_dvd_orderOf hn S fS ht h17C (x * u)
      (by rw [hord]; exact dvd_mul_left 17 2)
    rw [hord] at hodd
    exact absurd hodd (by decide)
  obtain ⟨w, hw2, hwu⟩ := exists_inverting_involution_seventeen hu17 hnorm hnc hinv
  obtain ⟨⟨ideal₁₇, hmax₁₇, h17mem⟩, hchar₁₇⟩ :=
    CFSG.BlockBasics.residue_prime_existence 17 (by norm_num)
  have : ideal₁₇.IsMaximal := hmax₁₇
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₁₇) 17 := hchar₁₇ ideal₁₇ hmax₁₇ h17mem
  have h1mem : 1 ∈ Finset.Icc 1 (2 ^ (4 - 3) - 1) := by simp
  have hψ34 : Module.finrank ℂ (basis.representation (ψ 1)).vector = 34 := by
    have h := hψdeg 1 h1mem
    rw [hdeg1] at h
    exact_mod_cast h
  obtain ⟨-, hvan⟩ := full_prime_part_character_degree_singleton_block_singular_vanishing basis
    ideal₁₇ 17 (ψ 1) (by rw [hfac1, pow_one, hψ34]; norm_num)
  have hP : ∀ i : ℕ, 0 < i → i < 17 → (basis.representation χ₁).character (u ^ i) = 1 := by
    intro i hi0 hi17
    have hord : orderOf (u ^ i) = 17 := by
      rw [orderOf_pow' u (by omega), hu17]
      have hcop : Nat.gcd 17 i = 1 :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
          (fun h => absurd (Nat.le_of_dvd hi0 h) (by omega))
      rw [hcop]
    have hz := hvan (u ^ i) (by rw [hord])
    obtain ⟨hψx', -, -, -⟩ := hrel (u ^ i) (by rw [hord]; decide)
    rw [hψx' 1 h1mem] at hz
    push_cast at hz
    linear_combination hz
  have hinv' : ∀ x : G, orderOf x = 2 → (basis.representation χ₁).character x = -5 := by
    intro x hx
    rw [RotationCongruence.character_eq_of_isConj _ (isConj_of_orderOf_eq_two hn S fS ht hx),
      htval]
  exact not_dihedral_seventeen_character (basis.representation χ₁) hu17 hw2 hwu hχ₁1 hP hinv'

end CFSG.Semidihedral.Principal
