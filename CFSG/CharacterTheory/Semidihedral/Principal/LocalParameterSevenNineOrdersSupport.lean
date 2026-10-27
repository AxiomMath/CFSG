module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeSevenNine

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem prime_pow_seven_or_nine {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f = 7 ∨ p ^ f = 9) : (p = 7 ∧ f = 1) ∨ (p = 3 ∧ f = 2) := by
  rcases hq with h | h
  · have hp7 : p ∣ 7 := by rw [← h]; exact dvd_pow_self p (by omega)
    have hp7' : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp7
    subst hp7'
    exact Or.inl ⟨rfl, Nat.pow_right_injective (by norm_num) (h.trans (pow_one 7).symm)⟩
  · have hp3 : p ∣ 3 ^ 2 := by rw [show 3 ^ 2 = 9 by norm_num, ← h]; exact dvd_pow_self p (by omega)
    have hp3' : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow hp3)
    subst hp3'
    exact Or.inr ⟨rfl, Nat.pow_right_injective (by norm_num) (h.trans (by norm_num))⟩

theorem padicValNat_two_fortyEight : padicValNat 2 48 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem padicValNat_two_eighty : padicValNat 2 80 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (80 : ℕ) = 2 ^ 4 * 5 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem eq_five_of_modulus {n : ℕ} (hn : 4 ≤ n) (h : 2 ^ 4 = modulus n) : n = 5 := by
  rw [modulus] at h
  have := Nat.pow_right_injective le_rfl h
  omega

theorem local_parameter_seven_nine_orders_of_family {G : Type} [Group G] [Fintype G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq79 : p ^ f = 7 ∨ p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
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
    n = 5 ∧ Nat.card (C t) = 2 * a₀ * b₀ * p ^ f * ((p ^ f) ^ 2 - 1) ∧
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) =
        2 * a₀ * ((p ^ f : ℕ) + if p ^ f = 7 then -1 else 1) ∧
      ((p ^ f = 7 ∧ (X = (2328480 * a₀ * b₀ ^ 3, 3465 * b₀ ^ 2) ∨
          X = (1876896 * a₀ * b₀ ^ 3, 2793 * b₀ ^ 2))) ∨
        (p ^ f = 9 ∧ (X = (8514720 * a₀ * b₀ ^ 3, 5913 * b₀ ^ 2) ∨
          X = (6441120 * a₀ * b₀ ^ 3, 4473 * b₀ ^ 2) ∨
          X = (7236000 * a₀ * b₀ ^ 3, 5025 * b₀ ^ 2)))) ∧
      b₀ ^ 2 ∣ (C t).index := by
  intro CN a₀ b₀ X
  subst hq
  have horder := cleared_first_order_formula (pow_pos hp.pos f) hOF
  have he₀ : e = if p ^ f = 7 then -1 else 1 := by
    rw [he]
    rcases hq79 with h | h <;> rw [h] <;> rfl
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  have hpf := prime_pow_seven_or_nine hp hf hq79
  have hfodd : ∀ a : ℕ, Odd a → a ∣ f → a = 1 := by
    intro a ha hdvd
    rcases hpf with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Nat.dvd_one.mp hdvd
    · have := Nat.le_of_dvd (by norm_num) hdvd
      obtain ⟨k, hk⟩ := ha
      interval_cases a <;> omega
  obtain ⟨h2part, hCcard, hDcard⟩ := actual_layer_centralizer_orders hG n hn S fS t ht hnonab
    hcentral hnc p f hp hpodd hf hmodel hfodd
  rw [← he] at hDcard
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hn5 : n = 5 := by
    apply eq_five_of_modulus hn
    rw [← h2part]
    rcases hq79 with h | h <;> rw [h]
    · rw [show (7 : ℕ) ^ 2 - 1 = 48 by norm_num, padicValNat_two_fortyEight]
    · rw [show (9 : ℕ) ^ 2 - 1 = 80 by norm_num, padicValNat_two_eighty]
  have hq3 : 3 ≤ p ^ f := by rcases hq79 with h | h <;> omega
  have hqodd : Odd (p ^ f) := hpodd.pow
  have he1 : p ^ f % 4 = 1 → e = 1 := by
    intro h
    rw [he, ite_eq_left h]
  have he3 : p ^ f % 4 = 3 → e = -1 := by
    intro h
    rw [he, ite_eq_right (by omega)]
  obtain ⟨hf₁, hf₂, hf₃, ho₁, ho₂, ho₃, hsigns, hsum, hprod, hc₁, hc₂⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal principal hprincipal
      localBasis localPrincipal (p ^ f) hq3 hqodd h2part e he1 he3 φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ
      ν hfam hdeg
  have hM : (2 : ℤ) * (modulus n : ℕ) = 32 := by subst hn5; rfl
  rw [hM] at hc₁ hc₂
  have hrows := (seven_nine_signed_degree_product_finite_alternatives).1 ((p ^ f : ℕ) : ℤ) e
    _ _ _ δ₁ δ₂ δ₃ (by
      rcases hq79 with h | h
      · exact Or.inl ⟨by rw [h]; norm_num, by rw [he₀, ite_eq_left h]⟩
      · exact Or.inr ⟨by rw [h]; norm_num, by rw [he₀, ite_eq_right (by omega)]⟩)
    hf₁ hf₂ hf₃ ho₁ ho₂ ho₃ hsigns hsum hprod hc₁ hc₂
  have hCt : ∀ c₀ : ℕ, 2 * p ^ f * ((p ^ f) ^ 2 - 1) = c₀ →
      Nat.card (C t) = c₀ * a₀ * b₀ := by
    intro c₀ hc₀
    rw [hCcard, ← hc₀]
    ring
  have hDt : ∀ d₀ : ℕ, (2 * ((p ^ f : ℕ) + e) : ℤ) = d₀ →
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = d₀ * a₀ := by
    intro d₀ hd₀
    have h : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) = d₀ * a₀ := by
      rw [hDcard, ← hd₀]
      ring
    exact_mod_cast h
  have hX : (p ^ f = 7 ∧ (X = (2328480 * a₀ * b₀ ^ 3, 3465 * b₀ ^ 2) ∨
        X = (1876896 * a₀ * b₀ ^ 3, 2793 * b₀ ^ 2))) ∨
      (p ^ f = 9 ∧ (X = (8514720 * a₀ * b₀ ^ 3, 5913 * b₀ ^ 2) ∨
        X = (6441120 * a₀ * b₀ ^ 3, 4473 * b₀ ^ 2) ∨
        X = (7236000 * a₀ * b₀ ^ 3, 5025 * b₀ ^ 2))) := by
    rcases hrows with ⟨hq7, hδ, hfs⟩ | ⟨hq9, hfs⟩
    · have hq : p ^ f = 7 := by exact_mod_cast hq7
      have he7 : e = -1 := by rw [he₀, ite_eq_left hq]
      subst he7
      simp only [Prod.mk.injEq] at hδ
      obtain ⟨rfl, rfl, rfl⟩ := hδ
      have hc := hCt 672 (by rw [hq]; norm_num)
      have hd := hDt 12 (by rw [hq]; norm_num)
      rw [hq] at horder
      refine Or.inl ⟨hq, ?_⟩
      rcases hfs with h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨h1, -, -⟩ := h
      · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 55 := by
          exact_mod_cast h1
        rw [hf1] at horder
        exact Or.inl (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num))
      · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 343 := by
          exact_mod_cast h1
        rw [hf1] at horder
        exact Or.inr (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num))
    · have hq : p ^ f = 9 := by exact_mod_cast hq9
      have he9 : e = 1 := by rw [he₀, ite_eq_right (by omega)]
      subst he9
      have hc := hCt 1440 (by rw [hq]; norm_num)
      have hd := hDt 20 (by rw [hq]; norm_num)
      rw [hq] at horder
      refine Or.inr ⟨hq, ?_⟩
      rcases hfs with h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        obtain ⟨⟨rfl, rfl, rfl⟩, h1, -, -⟩ := h
      · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 729 := by
          exact_mod_cast h1
        rw [hf1] at horder
        exact Or.inl (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num))
      · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 71 := by
          exact_mod_cast h1
        rw [hf1] at horder
        exact Or.inr (Or.inl (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num)))
      · have hf1 : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) = 135 := by
          exact_mod_cast h1
        rw [hf1] at horder
        exact Or.inr (Or.inr (order_pair_of_identity (C t) ha hb (by norm_num) (by norm_num)
          (by norm_num) hc hd horder (by norm_num) (by norm_num)))
  refine ⟨hn5, hCcard, by rw [hDcard, he₀], hX, ?_⟩
  rcases hX with ⟨-, h | h⟩ | ⟨-, h | h | h⟩ <;>
    rw [show (C t).index = X.2 from rfl, h] <;> exact Dvd.intro_left _ rfl

end CFSG.Semidihedral.Principal
