module

public import CFSG.CharacterTheory.Semidihedral.Principal.AlternatingFourFiveTraces

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u w

namespace CyclicNineFour

theorem fourier_inversion_nat {G : Type*} [Monoid G] (f : G → ℂ) (g : G) {M i : ℕ} (hM : 0 < M)
    (hi : i < M) :
    f (g ^ i) = ∑ k ∈ Finset.range M, cyclicMultiplicity f g M k * cyclicRoot M ^ (k * i) := by
  rw [cyclicMultiplicity_inversion f g hM hi]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Nat.cast_mul, zpow_natCast]

theorem sum_four_group {V : Type*} [Group V] [Fintype V] (hV : Nat.card V = 4) (F : V → ℂ)
    (c₀ c : ℂ) (h0 : F 1 = c₀) (hF : ∀ v, v ≠ 1 → F v = c) : ∑ v, F v = c₀ + 3 * c := by
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ 1), h0,
    Finset.sum_congr rfl fun v hv => hF v (Finset.ne_of_mem_erase hv), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
    hV]
  norm_num

theorem commute_subgroupAverage_of_mem_normalizer {G : Type*} [Group G] {E : Type*}
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (H : Subgroup G) [Fintype H] (c : G)
    (hc : c ∈ Subgroup.normalizer (H : Set G)) :
    Commute (ρ c) (CFSG.LyonsUnitaryFour.subgroupAverage ρ H) := by
  unfold CFSG.LyonsUnitaryFour.subgroupAverage
  apply Commute.smul_right
  change ρ c * ∑ h : H, ρ h = (∑ h : H, ρ h) * ρ c
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (H.normalizerMonoidHom ⟨c, hc⟩).toEquiv _ _ fun h => ?_
  have e := Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨c, hc⟩ h
  change ρ c * ρ h = ρ ((H.normalizerMonoidHom ⟨c, hc⟩ h : H) : G) * ρ c
  rw [e, ← map_mul, ← map_mul]
  congr 1
  group

theorem trace_subgroupAverage_mul_eigenprojection {G : Type*} [Group G]
    (θ : FiniteComplexRepresentation G) (H : Subgroup G) [Fintype H] (c : G) (M : ℕ) (hM : 0 < M)
    (μ : ℂˣ) (k : ℕ) (hμ : (μ : ℂ) = cyclicRoot M ^ k) :
    LinearMap.trace ℂ θ.vector (CFSG.LyonsUnitaryFour.subgroupAverage θ.representation H *
      finiteOrderEigenprojection M (Units.mk0 (M : ℂ) (Nat.cast_ne_zero.mpr hM.ne')) μ
        (θ.representation c)) =
      cyclicMultiplicity (fun y => (Nat.card H : ℂ)⁻¹ * ∑ h : H, θ.character (h * y)) c M k := by
  unfold CFSG.LyonsUnitaryFour.subgroupAverage cyclicMultiplicity
  rw [smul_mul_assoc, Finset.sum_mul, map_smul, map_sum, smul_eq_mul]
  simp_rw [AlternatingFourFive.trace_mul_finiteOrderEigenprojection θ _ c M hM μ]
  have hpow : ∀ j : ℕ, ((μ⁻¹ : ℂˣ) : ℂ) ^ j = cyclicRoot M ^ (-((k : ℤ) * j)) := by
    intro j
    rw [Units.val_inv_eq_inv_val, hμ, zpow_neg, ← Nat.cast_mul, zpow_natCast, inv_pow, ← pow_mul]
  simp_rw [hpow, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  ring

theorem order_three_rational_value {G : Type*} [Group G] (θ : FiniteComplexRepresentation G)
    (w : G) (hw : orderOf w = 3) (q : ℚ) (hq : θ.character w = q) :
    ∃ x : ℤ, θ.character w = x ∧ θ.character (w ^ 2) = x := by
  have h3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  choose n hn using fun k : ℕ =>
    cyclicMultiplicity_natural θ w (M := 3) (by norm_num) h3 (k : ℤ)
  have hinv : ∀ j : ℕ, j < 3 → θ.character (w ^ j) =
      ∑ k ∈ Finset.range 3, (n k : ℂ) * cyclicRoot 3 ^ (k * j) := by
    intro j hj
    rw [fourier_inversion_nat θ.character w (by norm_num) hj]
    exact Finset.sum_congr rfl fun k _ => by rw [hn k]
  have hζ := cyclicRoot_isPrimitiveRoot (M := 3) (by norm_num)
  have hζp : IsPrimitiveRoot (cyclicRoot 3) (3 ^ (0 + 1)) := by simpa using hζ
  set c : ℕ → ℚ := fun k => (n k : ℚ) - if k = 0 then q else 0 with hc
  have hrel : ∑ k ∈ Finset.range (3 ^ (0 + 1)), (c k : ℂ) * cyclicRoot 3 ^ k = 0 := by
    have e := hinv 1 (by norm_num)
    rw [pow_one, hq] at e
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      mul_one] at e ⊢
    norm_num [hc]
    linear_combination -e
  have hper : ∀ k : ℕ, k < 3 → c k = c 0 := fun k hk => by
    have h := CFSG.LyonsUnitaryFour.periodic_of_sum_pow_eq_zero Nat.prime_three 0 hζp c hrel
      (by simpa using hk)
    simpa [Nat.mod_one] using h
  have hc0 : c 0 = (n 0 : ℚ) - q := by simp [hc]
  have hck : ∀ k : ℕ, 0 < k → k < 3 → (n k : ℚ) = n 0 - q := by
    intro k hk0 hk3
    have h := hper k hk3
    rw [hc0] at h
    simpa [hc, Nat.pos_iff_ne_zero.mp hk0] using h
  have hq' : q = (n 0 : ℚ) - n 1 := by linarith [hck 1 (by norm_num) (by norm_num)]
  have hn21 : (n 2 : ℂ) = n 1 := by
    have h := (hck 2 (by norm_num) (by norm_num)).trans (hck 1 (by norm_num) (by norm_num)).symm
    exact_mod_cast h
  have hgeom := hζ.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hgeom
  have hζ3 : cyclicRoot 3 ^ 3 = 1 := cyclicRoot_pow_self 3
  refine ⟨(n 0 : ℤ) - n 1, ?_, ?_⟩
  · rw [hq, hq']
    push_cast
    ring
  · rw [hinv 2 (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    linear_combination cyclicRoot 3 ^ 4 * hn21 + (n 1 : ℂ) * hgeom + (n 1 * cyclicRoot 3) * hζ3

end CyclicNineFour

open CyclicNineFour

theorem cyclic_nine_four_group_rational_character_mod_thirty_six
    {G : Type u} [Group G] [Fintype G] (V : Subgroup G) (hV : Nat.card V = 4) (c : G)
    (hcN : c ∈ Subgroup.normalizer (V : Set G)) (hc : orderOf c = 9)
    (hφ : orderOf (V.normalizerMonoidHom ⟨c, hcN⟩) = 3) (w : G) (hw : w = c ^ 3)
    (θ : FiniteComplexRepresentation.{u, w} G) (hrat : ∀ g, ∃ q : ℚ, θ.character g = q)
    (a b : ℤ) (ha : ∀ v ∈ V, v ≠ 1 → θ.character v = a)
    (hb : ∀ v ∈ V, v ≠ 1 → θ.character (v * w) = b ∧ θ.character (v * w ^ 2) = b) :
    orderOf w = 3 ∧ (∀ v ∈ V, w * v = v * w) ∧
      ∃ x : ℤ, θ.character w = x ∧ θ.character (w ^ 2) = x ∧
        x ≡ Module.finrank ℂ θ.vector + 3 * (a - b) [ZMOD 36] ∧
        ∃ n : ℕ, (Module.finrank ℂ θ.vector : ℤ) + 3 * a - x - 3 * b = 12 * n ∧ 3 ∣ n := by
  have hw3 : orderOf w = 3 := by
    rw [hw, orderOf_pow_of_dvd (by norm_num) (by rw [hc]; norm_num), hc]
  have hcent : ∀ v ∈ V, w * v = v * w := by
    intro v hv
    have h3 := pow_orderOf_eq_one (V.normalizerMonoidHom ⟨c, hcN⟩)
    rw [hφ, ← map_pow] at h3
    have e := congrArg (fun ψ : MulAut V => ((ψ ⟨v, hv⟩ : V) : G)) h3
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
      SubmonoidClass.coe_pow] at e
    rw [hw]
    calc c ^ 3 * v = c ^ 3 * v * (c ^ 3)⁻¹ * c ^ 3 := (inv_mul_cancel_right _ _).symm
      _ = v * c ^ 3 := by rw [e]
  refine ⟨hw3, hcent, ?_⟩
  obtain ⟨qw, hqw⟩ := hrat w
  obtain ⟨x, hxw, hxw2⟩ := order_three_rational_value θ w hw3 qw hqw
  have h9 : (0 : ℕ) < 9 := by norm_num
  have hc9 : c ^ 9 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hT9 : θ.representation c ^ 9 = 1 := by rw [← map_pow, hc9, map_one]
  obtain ⟨T, hT⟩ : ∃ T : G → ℂ,
      T = fun y => (Nat.card V : ℂ)⁻¹ * ∑ h : V, θ.character (h * y) := ⟨_, rfl⟩
  have hTapp : ∀ y, T y = (Nat.card V : ℂ)⁻¹ * ∑ h : V, θ.character (h * y) := fun y => by
    rw [hT]
  have hcommV := commute_subgroupAverage_of_mem_normalizer θ.representation V c hcN
  have hnat : ∀ k : ℕ, ∃ n : ℕ, cyclicMultiplicity T c 9 k = n := by
    intro k
    obtain ⟨μ, hμ⟩ : ∃ u : ℂˣ, (u : ℂ) = cyclicRoot 9 ^ k :=
      ⟨Units.mk0 _ (pow_ne_zero _ (cyclicRoot_ne_zero 9)), rfl⟩
    have hμ9 : μ ^ 9 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hμ, ← pow_mul, mul_comm, pow_mul, cyclicRoot_pow_self,
        one_pow, Units.val_one])
    have hcomm : Commute (CFSG.LyonsUnitaryFour.subgroupAverage θ.representation V)
        (finiteOrderEigenprojection 9 (Units.mk0 ((9 : ℕ) : ℂ) (Nat.cast_ne_zero.mpr h9.ne')) μ
          (θ.representation c)) := by
      rw [finiteOrderEigenprojection, cyclicOperatorAverage]
      apply Commute.smul_right
      apply Commute.sum_right
      intro j _
      exact (hcommV.symm.smul_right _).pow_right j
    have hidem := IsIdempotentElem.mul_of_commute hcomm
      (CFSG.LyonsUnitaryFour.subgroupAverage_idempotent θ.representation V)
      (finiteOrderEigenprojection_idempotent 9
        (Units.mk0 ((9 : ℕ) : ℂ) (Nat.cast_ne_zero.mpr h9.ne')) μ rfl hμ9 _ hT9)
    obtain ⟨n, hn⟩ := AlternatingFourFive.trace_idempotent_natural _ hidem
    refine ⟨n, ?_⟩
    rw [hT, ← trace_subgroupAverage_mul_eigenprojection θ V c 9 h9 μ k hμ, hn]
  choose N hN using hnat
  obtain ⟨ζ, hζ⟩ : ∃ z : ℂ, z = cyclicRoot 9 := ⟨_, rfl⟩
  have hinv : ∀ i : ℕ, i < 9 → T (c ^ i) = ∑ k ∈ Finset.range 9, (N k : ℂ) * ζ ^ (k * i) := by
    intro i hi
    rw [fourier_inversion_nat T c h9 hi, hζ]
    exact Finset.sum_congr rfl fun k _ => by rw [hN k]
  obtain ⟨q, hq⟩ : ∃ q : ℚ, T c = q := by
    choose Q hQ using fun h : V => hrat ((h : G) * c)
    refine ⟨(Nat.card V : ℚ)⁻¹ * ∑ h : V, Q h, ?_⟩
    rw [hTapp]
    push_cast
    simp only [hQ]
  have hζp : IsPrimitiveRoot ζ (3 ^ (1 + 1)) := by
    rw [hζ]
    simpa using cyclicRoot_isPrimitiveRoot (M := 9) (by norm_num)
  set cc : ℕ → ℚ := fun k => (N k : ℚ) - if k = 0 then q else 0 with hcc
  have hrel : ∑ k ∈ Finset.range (3 ^ (1 + 1)), (cc k : ℂ) * ζ ^ k = 0 := by
    have e := hinv 1 (by norm_num)
    rw [pow_one, hq] at e
    rw [show 3 ^ (1 + 1) = 9 by norm_num]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      mul_one] at e ⊢
    norm_num [hcc]
    linear_combination -e
  have hper : ∀ k : ℕ, k < 9 → cc k = cc (k % 3) := fun k hk => by
    have h := CFSG.LyonsUnitaryFour.periodic_of_sum_pow_eq_zero Nat.prime_three 1 hζp cc hrel
      (j := k) (by norm_num; exact hk)
    simpa using h
  have hNeq : ∀ k l : ℕ, 0 < k → 0 < l → cc k = cc l → N k = N l := by
    intro k l hk hl h
    simp only [hcc, Nat.pos_iff_ne_zero.mp hk, Nat.pos_iff_ne_zero.mp hl, ite_false,
      sub_zero] at h
    exact_mod_cast h
  have hN41 : N 4 = N 1 := hNeq 4 1 (by norm_num) (by norm_num) (hper 4 (by norm_num))
  have hN71 : N 7 = N 1 := hNeq 7 1 (by norm_num) (by norm_num) (hper 7 (by norm_num))
  have hN52 : N 5 = N 2 := hNeq 5 2 (by norm_num) (by norm_num) (hper 5 (by norm_num))
  have hN82 : N 8 = N 2 := hNeq 8 2 (by norm_num) (by norm_num) (hper 8 (by norm_num))
  have hN63 : N 6 = N 3 := hNeq 6 3 (by norm_num) (by norm_num)
    ((hper 6 (by norm_num)).trans (hper 3 (by norm_num)).symm)
  have hsumV : ∀ y : G, ∀ c₀ c' : ℂ, θ.character y = c₀ →
      (∀ v ∈ V, v ≠ 1 → θ.character (v * y) = c') → 4 * T y = c₀ + 3 * c' := by
    intro y c₀ c' h0 hF
    rw [hTapp, hV, sum_four_group hV (fun h : V => θ.character (h * y)) c₀ c' (by simpa using h0)
      (fun h hh => hF h h.2 (fun h' => hh (Subtype.ext h')))]
    push_cast
    field_simp
  have h1C : θ.character 1 = (Module.finrank ℂ θ.vector : ℂ) := Representation.char_one _
  have hT1 : 4 * T 1 = (Module.finrank ℂ θ.vector : ℂ) + 3 * a :=
    hsumV 1 _ _ h1C fun v hv hv1 => by rw [mul_one]; exact ha v hv hv1
  have hT3 : 4 * T (c ^ 3) = (x : ℂ) + 3 * b :=
    hsumV _ _ _ (by rw [← hw]; exact hxw) fun v hv hv1 => by rw [← hw]; exact (hb v hv hv1).1
  have hc6 : c ^ 6 = w ^ 2 := by rw [hw, ← pow_mul]
  have hT6 : 4 * T (c ^ 6) = (x : ℂ) + 3 * b :=
    hsumV _ _ _ (by rw [hc6]; exact hxw2) fun v hv hv1 => by rw [hc6]; exact (hb v hv hv1).2
  have hζ9 : ζ ^ 9 = 1 := by rw [hζ]; exact cyclicRoot_pow_self 9
  have e0 := hinv 0 (by norm_num)
  have e3 := hinv 3 (by norm_num)
  have e6 := hinv 6 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at e0 e3 e6
  norm_num at e0 e3 e6
  rw [pow_eq_pow_mod 9 hζ9, pow_eq_pow_mod 12 hζ9, pow_eq_pow_mod 15 hζ9,
    pow_eq_pow_mod 18 hζ9, pow_eq_pow_mod 21 hζ9, pow_eq_pow_mod 24 hζ9] at e3
  rw [pow_eq_pow_mod 12 hζ9, pow_eq_pow_mod 18 hζ9, pow_eq_pow_mod 24 hζ9,
    pow_eq_pow_mod 30 hζ9, pow_eq_pow_mod 36 hζ9, pow_eq_pow_mod 42 hζ9,
    pow_eq_pow_mod 48 hζ9] at e6
  norm_num at e3 e6
  rw [hN41, hN71, hN52, hN82, hN63] at e0 e3 e6
  have hζ' := cyclicRoot_isPrimitiveRoot (M := 9) (by norm_num)
  rw [← hζ] at hζ'
  have hζ3 : ζ ^ 3 ≠ 1 := fun h => by
    have := hζ'.dvd_of_pow_eq_one 3 h
    norm_num at this
  have hζ0 : ζ ≠ 0 := by rw [hζ]; exact cyclicRoot_ne_zero 9
  have hω : ζ ^ 6 + ζ ^ 3 + 1 = 0 := by
    have h : (ζ ^ 3 - 1) * (ζ ^ 6 + ζ ^ 3 + 1) = 0 := by linear_combination hζ9
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ3)
  have hne : ζ ^ 3 - ζ ^ 6 ≠ 0 := by
    have : ζ ^ 3 - ζ ^ 6 = ζ ^ 3 * (1 - ζ ^ 3) := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ hζ0) (sub_ne_zero.mpr (Ne.symm hζ3))
  have hdiff : 3 * ((N 1 : ℂ) - N 2) * (ζ ^ 3 - ζ ^ 6) = 0 := by
    linear_combination -e3 + e6 + (1 / 4 : ℂ) * hT3 - (1 / 4 : ℂ) * hT6
  have hN12 : (N 2 : ℂ) = N 1 := by
    have h := (mul_eq_zero.mp hdiff).resolve_right hne
    have h' : (N 1 : ℂ) - N 2 = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
    linear_combination -h'
  have hfinal : (Module.finrank ℂ θ.vector : ℤ) + 3 * a - x - 3 * b = 36 * N 1 := by
    have h : (((Module.finrank ℂ θ.vector : ℤ) + 3 * a - x - 3 * b : ℤ) : ℂ) =
        ((36 * N 1 : ℤ) : ℂ) := by
      push_cast
      linear_combination -hT1 + hT3 + 4 * e0 - 4 * e3 - 12 * (N 1 : ℂ) * hω +
        12 * (1 - ζ ^ 6) * hN12
    exact_mod_cast h
  refine ⟨x, hxw, hxw2, Int.modEq_iff_dvd.mpr ⟨N 1, by linarith⟩, 3 * N 1, ?_,
    dvd_mul_right 3 _⟩
  push_cast
  linarith

end CFSG.Semidihedral.Principal
