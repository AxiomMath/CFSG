module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem exists_enum_of_card {α : Type*} (I : Finset α) {k : ℕ} (hk : I.card = k) {a : α}
    (ha : a ∈ I) :
    ∃ b : ℕ → α, b 0 = a ∧ Set.InjOn b (Finset.range k) ∧
      (∀ i ∈ Finset.range k, b i ∈ I) ∧ ∀ x ∈ I, ∃ i ∈ Finset.range k, b i = x := by
  have hk' : Fintype.card I = k := by rw [Fintype.card_coe, hk]
  have hkpos : 0 < k := hk ▸ Finset.card_pos.mpr ⟨a, ha⟩
  let e₀ : I ≃ Fin k := Fintype.equivFinOfCardEq hk'
  let e : I ≃ Fin k := e₀.trans (Equiv.swap (e₀ ⟨a, ha⟩) ⟨0, hkpos⟩)
  have he : e ⟨a, ha⟩ = ⟨0, hkpos⟩ := by
    simp only [e, Equiv.trans_apply, Equiv.swap_apply_left]
  let b : ℕ → α := fun i => if h : i < k then (e.symm ⟨i, h⟩ : α) else a
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · simp only [b, hkpos, dite_true]
    rw [show (⟨0, hkpos⟩ : Fin k) = e ⟨a, ha⟩ from he.symm, Equiv.symm_apply_apply]
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    simp only [b, hi', hj', dite_true] at hij
    have h := e.symm.injective (Subtype.ext hij)
    exact congrArg Fin.val h
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [b, hi', dite_true]
    exact (e.symm ⟨i, hi'⟩).2
  · intro x hx
    refine ⟨(e ⟨x, hx⟩ : ℕ), Finset.mem_range.mpr (e ⟨x, hx⟩).2, ?_⟩
    simp only [b, (e ⟨x, hx⟩).2, dite_true, Fin.eta, Equiv.symm_apply_apply]

theorem exists_ne_one_odd_orderOf_of_isSimpleGroup {L : Type*} [Group L] [Finite L]
    [IsSimpleGroup L] (hnonab : ∃ a b : L, a * b ≠ b * a) :
    ∃ g : L, g ≠ 1 ∧ Odd (orderOf g) := by
  by_contra hcon
  have hall : ∀ g : L, g ≠ 1 → ¬ Odd (orderOf g) := fun g hg hodd => hcon ⟨g, hg, hodd⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 L := by
    rw [IsPGroup.iff_orderOf]
    intro g
    obtain ⟨k, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    refine ⟨k, ?_⟩
    have hdvd : m ∣ orderOf g := ⟨2 ^ k, by rw [hgm, mul_comm]⟩
    have hord := orderOf_pow_orderOf_div (orderOf_pos g).ne' hdvd
    have hdiv : orderOf g / m = 2 ^ k := by
      rw [hgm, Nat.mul_div_cancel _ hm.pos]
    rw [hdiv] at hord
    by_cases h1 : g ^ 2 ^ k = 1
    · rw [h1, orderOf_one] at hord
      rw [hgm, ← hord, mul_one]
    · exact absurd (hord ▸ hm) (hall _ h1)
  have hcen : Nontrivial (Subgroup.center L) := h2.center_nontrivial
  have htop : Subgroup.center L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exfalso
      rw [h] at hcen
      exact (Subgroup.nontrivial_iff_ne_bot ⊥).mp hcen rfl
    · exact h
  obtain ⟨a, b, hab⟩ := hnonab
  have ha : a ∈ Subgroup.center L := htop ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem exists_odd_orderOf_map_ne_one {X Q : Type*} [Group X] [Finite X] [Group Q]
    (κ : X →* Q) (hκ : Function.Surjective κ) {γ : Q} (hγ : γ ≠ 1) (hodd : Odd (orderOf γ)) :
    ∃ c : X, Odd (orderOf c) ∧ κ c ≠ 1 := by
  obtain ⟨c₀, rfl⟩ := hκ γ
  obtain ⟨k, m, hm, hc₀⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c₀).ne'
  have hdvd : m ∣ orderOf c₀ := ⟨2 ^ k, by rw [hc₀, mul_comm]⟩
  have hord := orderOf_pow_orderOf_div (orderOf_pos c₀).ne' hdvd
  have hdiv : orderOf c₀ / m = 2 ^ k := by
    rw [hc₀, Nat.mul_div_cancel _ hm.pos]
  rw [hdiv] at hord
  refine ⟨c₀ ^ 2 ^ k, hord ▸ hm, fun h1 => hγ ?_⟩
  rw [map_pow] at h1
  have hd := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (orderOf (κ c₀)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd)

theorem perm_eq_one_of_card_fixed {X : Type*} [Finite X] (σ : Equiv.Perm X)
    (h : Nat.card {x // σ x = x} = Nat.card X) : σ = 1 := by
  ext x
  by_contra hx
  have hlt := Finite.card_subtype_lt (p := fun x => σ x = x) (x := x) hx
  omega

theorem eq_zero_of_forall_odd_add_mul {X : Type*} [Group X] (φ : X → ℂ) (q e : ℂ) (he : e ≠ 0)
    (hφ1 : φ 1 = q) (hex : ∃ y : X, Odd (orderOf y) ∧ φ y ≠ q) {a b : ℂ}
    (h : ∀ y : X, Odd (orderOf y) → a + b * (1 + e * φ y) = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨y₀, hy₀, hy₀ne⟩ := hex
  have h1 := h 1 (by rw [orderOf_one]; exact odd_one)
  have h2 := h y₀ hy₀
  rw [hφ1] at h1
  have hsub : φ y₀ - q ≠ 0 := sub_ne_zero.mpr hy₀ne
  have hb : b = 0 := by
    have h3 : b * (e * (φ y₀ - q)) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h (mul_ne_zero he hsub)
  refine ⟨?_, hb⟩
  rw [hb] at h1
  simpa using h1

theorem sum_mul_columns_eq_zero {ι X : Type*} [Group X] (B : Finset ι) (φ : X → ℂ) (q e : ℂ)
    (he : e ≠ 0) (hφ1 : φ 1 = q) (hex : ∃ y : X, Odd (orderOf y) ∧ φ y ≠ q)
    (U : ι → Fin 2 → ℤ) (val : ι → X → ℂ)
    (hval : ∀ c ∈ B, ∀ y : X, Odd (orderOf y) → val c y = U c 0 + U c 1 * (1 + e * φ y))
    (w : ι → ℤ) (hvan : ∀ y : X, Odd (orderOf y) → ∑ c ∈ B, (w c : ℂ) * val c y = 0) :
    ∑ c ∈ B, w c * U c 0 = 0 ∧ ∑ c ∈ B, w c * U c 1 = 0 := by
  have h := eq_zero_of_forall_odd_add_mul φ q e he hφ1 hex
    (a := ∑ c ∈ B, (w c : ℂ) * U c 0) (b := ∑ c ∈ B, (w c : ℂ) * U c 1) fun y hy => by
      rw [← hvan y hy, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [hval c hc y hy]
      ring
  obtain ⟨h0, h1⟩ := h
  constructor
  · exact_mod_cast h0
  · exact_mod_cast h1

theorem exists_odd_fixedPoint_character_ne {G : Type} [Group G] [Finite G] {t : G}
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (F : Type) [Field F] [Finite F] (ρ : Gamma t →* coordinateE F) (hρ : Function.Injective ρ) :
    ∃ y : C t, Odd (orderOf y) ∧
      (Nat.card {x : Omega F // ((ρ (kappa t y) : coordinateE F) : Equiv.Perm (Omega F)) x = x} :
        ℂ) - 1 ≠ Nat.card F := by
  have : Finite (Gamma t) := Finite.of_surjective _ (QuotientGroup.mk'_surjective (NZ t))
  obtain ⟨γ, hγ1, hγodd⟩ := exists_ne_one_odd_orderOf_of_isSimpleGroup hnonab
  have hγ1' : (γ : Gamma t) ≠ 1 := fun h => hγ1 (Subtype.ext h)
  have hγodd' : Odd (orderOf (γ : Gamma t)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨c, hc, hκc⟩ := exists_odd_orderOf_map_ne_one (kappa t)
    (QuotientGroup.mk'_surjective _) hγ1' hγodd'
  refine ⟨c, hc, fun h => hκc ?_⟩
  have := Fintype.ofFinite F
  have hcard : Nat.card {x : Omega F //
      ((ρ (kappa t c) : coordinateE F) : Equiv.Perm (Omega F)) x = x} = Nat.card (Omega F) := by
    rw [card_omega]
    have h' : (Nat.card {x : Omega F //
        ((ρ (kappa t c) : coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) =
        Nat.card F + 1 := by linear_combination h
    exact_mod_cast h'
  have hσ := perm_eq_one_of_card_fixed _ hcard
  apply hρ
  rw [map_one]
  exact Subtype.ext hσ

section Listed

variable {ι : Type*} [DecidableEq ι]

theorem sum_listed {M' : Type*} [AddCommMonoid M'] (k : ℕ) {x₀ x₁ x₂ x₃ x₄ : ι}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃) (h04 : x₀ ≠ x₄) (h12 : x₁ ≠ x₂)
    (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    {a b : ℕ → ι} (ha : Set.InjOn a (Finset.Icc 1 (k - 1))) (hb : Set.InjOn b (Finset.range k))
    (ha_x : ∀ j ∈ Finset.Icc 1 (k - 1),
      a j ≠ x₀ ∧ a j ≠ x₁ ∧ a j ≠ x₂ ∧ a j ≠ x₃ ∧ a j ≠ x₄)
    (hb_x : ∀ i ∈ Finset.range k, b i ≠ x₀ ∧ b i ≠ x₁ ∧ b i ≠ x₂ ∧ b i ≠ x₃ ∧ b i ≠ x₄)
    (hb_a : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.Icc 1 (k - 1), b i ≠ a j) (g : ι → M') :
    ∑ c ∈ ({x₀, x₁, x₂, x₃, x₄} ∪ (Finset.Icc 1 (k - 1)).image a ∪
        (Finset.range k).image b : Finset ι), g c =
      g x₀ + g x₁ + g x₂ + g x₃ + g x₄ + ∑ j ∈ Finset.Icc 1 (k - 1), g (a j) +
        ∑ i ∈ Finset.range k, g (b i) := by
  have hd1 : Disjoint ({x₀, x₁, x₂, x₃, x₄} : Finset ι) ((Finset.Icc 1 (k - 1)).image a) := by
    rw [Finset.disjoint_right]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h0, h1, h2, h3, h4⟩ := ha_x j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h0, h1, h2, h3, h4⟩
  have hd2 : Disjoint (({x₀, x₁, x₂, x₃, x₄} : Finset ι) ∪ (Finset.Icc 1 (k - 1)).image a)
      ((Finset.range k).image b) := by
    rw [Finset.disjoint_right]
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h0, h1, h2, h3, h4⟩ := hb_x i hi
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      not_or]
    refine ⟨⟨h0, h1, h2, h3, h4⟩, ?_⟩
    rintro ⟨j, hj, hji⟩
    exact hb_a i hi j hj hji.symm
  rw [Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_image ha, Finset.sum_image hb,
    Finset.sum_insert (by simp [h01, h02, h03, h04]), Finset.sum_insert (by simp [h12, h13, h14]),
    Finset.sum_insert (by simp [h23, h24]), Finset.sum_pair h34]
  simp only [add_assoc]

theorem sum_cast_four_mul {B : Finset ι} (g : ι → ℂ) {x₀ x₁ x₂ x₃ : ι} (hx₀ : x₀ ∈ B)
    (hx₁ : x₁ ∈ B) (hx₂ : x₂ ∈ B) (hx₃ : x₃ ∈ B) (δ₁ δ₂ δ₃ : ℤ) :
    ∑ y ∈ B, (((Pi.single x₀ 1 + δ₁ • Pi.single x₁ 1 + δ₂ • Pi.single x₂ 1 +
      δ₃ • Pi.single x₃ 1 : ι → ℤ) y : ℤ) : ℂ) * g y =
      g x₀ + δ₁ * g x₁ + δ₂ * g x₂ + δ₃ * g x₃ := by
  simp [Pi.single_apply, hx₀, hx₁, hx₂, hx₃, add_mul, Finset.sum_add_distrib]

theorem sum_cast_three_mul {B : Finset ι} (g : ι → ℂ) {x₀ x₁ z : ι} (hx₀ : x₀ ∈ B)
    (hx₁ : x₁ ∈ B) (hz : z ∈ B) (δ : ℤ) :
    ∑ y ∈ B, (((Pi.single x₀ 1 + δ • Pi.single x₁ 1 - δ • Pi.single z 1 : ι → ℤ) y : ℤ) : ℂ) *
      g y = g x₀ + δ * g x₁ - δ * g z := by
  simp [Pi.single_apply, hx₀, hx₁, hz, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem sum_cast_two_mul {B : Finset ι} (g : ι → ℂ) {z w : ι} (hz : z ∈ B) (hw : w ∈ B)
    (ε : ℤ) :
    ∑ y ∈ B, (((ε • (Pi.single z 1 - Pi.single w 1) : ι → ℤ) y : ℤ) : ℂ) * g y =
      ε * (g z - g w) := by
  simp [Pi.single_apply, hz, hw, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem card_listed (k : ℕ) (hk : 1 ≤ k) {x₀ x₁ x₂ x₃ x₄ : ι}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃) (h04 : x₀ ≠ x₄) (h12 : x₁ ≠ x₂)
    (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    {a b : ℕ → ι} (ha : Set.InjOn a (Finset.Icc 1 (k - 1))) (hb : Set.InjOn b (Finset.range k))
    (ha_x : ∀ j ∈ Finset.Icc 1 (k - 1),
      a j ≠ x₀ ∧ a j ≠ x₁ ∧ a j ≠ x₂ ∧ a j ≠ x₃ ∧ a j ≠ x₄)
    (hb_x : ∀ i ∈ Finset.range k, b i ≠ x₀ ∧ b i ≠ x₁ ∧ b i ≠ x₂ ∧ b i ≠ x₃ ∧ b i ≠ x₄)
    (hb_a : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.Icc 1 (k - 1), b i ≠ a j) :
    ({x₀, x₁, x₂, x₃, x₄} ∪ (Finset.Icc 1 (k - 1)).image a ∪
        (Finset.range k).image b : Finset ι).card = 2 * k + 4 := by
  rw [Finset.card_eq_sum_ones, sum_listed k h01 h02 h03 h04 h12 h13 h14 h23 h24 h34 ha hb ha_x
    hb_x hb_a, Finset.sum_const, Finset.sum_const, Nat.card_Icc, Finset.card_range]
  simp only [smul_eq_mul, mul_one]
  omega

end Listed

theorem neg_sign_one_add_mul_eq {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) {d : ℕ} (hd : 0 < d)
    (hne : (1 : ℂ) + (δ : ℂ) * (d : ℂ) ≠ 0) :
    -((SignType.sign ((1 : ℂ) + (δ : ℂ) * (d : ℂ)).re : SignType) : ℤ) = -δ := by
  have hre : ((1 : ℂ) + (δ : ℂ) * (d : ℂ)).re = 1 + (δ : ℝ) * d := by simp
  rw [hre]
  rcases hδ with rfl | rfl
  · have hpos : (0 : ℝ) < 1 + ((1 : ℤ) : ℝ) * d := by push_cast; positivity
    rw [sign_pos hpos]
    rfl
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hne' : (1 : ℝ) + ((-1 : ℤ) : ℝ) * d ≠ 0 := by
      intro h
      apply hne
      apply Complex.ext
      · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.intCast_re,
          Complex.natCast_re, Complex.intCast_im, Complex.natCast_im, mul_zero, sub_zero,
          Complex.zero_re]
        push_cast at h ⊢
        linarith
      · simp
    have hneg : 1 + ((-1 : ℤ) : ℝ) * d < 0 := by
      push_cast at hne' ⊢
      rcases lt_or_gt_of_ne hne' with h | h
      · exact h
      · exfalso
        linarith
    rw [sign_neg hneg]
    rfl

@[expose] def ActualPrincipalBlockFamily {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (t : G)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (e : ℤ) (k : ℕ) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index) : Prop :=
  (∃ lφ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
    (localBasis.representation lφ).IsIrreducible ∧
    (localBasis.representation lφ).character = φ ∧
    Module.finrank ℂ (localBasis.representation lφ).vector = q ∧
    MonoidHom.ker (localBasis.representation lφ).representation = NZ t) ∧
  (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (δ₄ = 1 ∨ δ₄ = -1) ∧
  [principal, χ₁, χ₂, χ₃, χ₄].Nodup ∧
  Set.InjOn ψ (Finset.Icc 1 (k - 1)) ∧ Set.InjOn ν (Finset.range k) ∧
  (∀ j ∈ Finset.Icc 1 (k - 1),
    ψ j ≠ principal ∧ ψ j ≠ χ₁ ∧ ψ j ≠ χ₂ ∧ ψ j ≠ χ₃ ∧ ψ j ≠ χ₄) ∧
  (∀ i ∈ Finset.range k, ν i ≠ principal ∧ ν i ≠ χ₁ ∧ ν i ≠ χ₂ ∧ ν i ≠ χ₃ ∧ ν i ≠ χ₄) ∧
  (∀ i ∈ Finset.range k, ∀ j ∈ Finset.Icc 1 (k - 1), ν i ≠ ψ j) ∧
  coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
    ({principal, χ₁, χ₂, χ₃, χ₄} ∪ (Finset.Icc 1 (k - 1)).image ψ ∪
      (Finset.range k).image ν : Finset basis.index) ∧
  (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).card = 2 * k + 4 ∧
  (∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
    Odd (Module.finrank ℂ (basis.representation c).vector) ↔
      c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃) ∧
  (∀ y : C t, Odd (orderOf y) →
    (basis.representation χ₁).character (t * y) = δ₁ * e * φ y ∧
    (basis.representation χ₂).character (t * y) = -(δ₂ * e * φ y) ∧
    (basis.representation χ₃).character (t * y) = -δ₃ ∧
    (basis.representation χ₄).character (t * y) = δ₄ * (1 - e * φ y) ∧
    (∀ j ∈ Finset.Icc 1 (k - 1),
      (basis.representation (ψ j)).character (t * y) = δ₁ * (1 + e * φ y)) ∧
    ∀ i ∈ Finset.range k,
      (basis.representation (ν i)).character (t * y) = -(δ₁ * (1 + e * φ y))) ∧
  ∀ x : G, Odd (orderOf x) →
    (∀ j ∈ Finset.Icc 1 (k - 1), (basis.representation (ψ j)).character x =
      (basis.representation χ₁).character x + δ₁) ∧
    (∀ i ∈ Finset.range k, (basis.representation (ν i)).character x =
      (basis.representation χ₁).character x + δ₁) ∧
    1 + δ₁ * (basis.representation χ₁).character x + δ₂ * (basis.representation χ₂).character x +
      δ₃ * (basis.representation χ₃).character x = 0 ∧
    1 + δ₂ * (basis.representation χ₂).character x + δ₄ * (basis.representation χ₄).character x =
      0

end CFSG.Semidihedral.Principal
