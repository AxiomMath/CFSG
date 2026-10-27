module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Aut
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldInv
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG GorensteinWalter Subgroup AutL2Facts

namespace FieldOrd

universe u

variable {F : Type u} [Field F] [Finite F]

theorem eq_of_mul_self_eq_one {σ τ : F ≃+* F} (hσ : σ * σ = 1) (hτ : τ * τ = 1) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) : σ = τ := by
  classical
  have := isCyclic_ringAut F
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) two_pos
  by_contra hne
  have hsub : ({1, σ, τ} : Finset (F ≃+* F)) ⊆ Finset.univ.filter fun z => z ^ 2 = 1 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_two]
    rcases hz with rfl | rfl | rfl
    · exact mul_one 1
    · exact hσ
    · exact hτ
  have h3 : ({1, σ, τ} : Finset (F ≃+* F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hσ1, Ne.symm hτ1⟩
  have := (Finset.card_le_card hsub).trans h
  omega

theorem right_ne_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (T : Sylow 2 (PSL2 F)) (hT : 8 ≤ Nat.card T)
    (g : PGammaL2 F) (hg2 : g * g = 1)
    (hgT : ∀ t ∈ (T : Subgroup (PSL2 F)), g * incl F t = incl F t * g)
    (hgT' : g ∉ (T : Subgroup (PSL2 F)).map (incl F)) : g.right ≠ 1 := by
  intro h1
  apply hgT'
  have := mem_center_of_right_eq_one (isOddPrimePower_of hp hp2 hf hF) T hT g h1 (k := 1)
    (by rw [pow_one, pow_two]; exact hg2) hgT
  exact map_mono inf_le_left this

theorem mod_four_of_involution {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    {σ : F ≃+* F} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Nat.card F % 4 = 1 ∧ IsSquare (-1 : F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσord : orderOf σ = 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
  obtain ⟨t, -, ht, -, hcard, -⟩ := exists_odd_pow_of_orderOf_two_pow hp hp2 hF σ le_rfl hσord
  have hq4 : Nat.card F % 4 = 1 := by
    obtain ⟨j, rfl⟩ := ht
    rw [hcard, show (2 * j + 1) ^ 2 ^ 1 = 4 * (j * j + j) + 1 by ring]
    omega
  refine ⟨hq4, ?_⟩
  have : Fintype F := Fintype.ofFinite F
  classical
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
  omega

theorem card_sylow (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (T : Sylow 2 (PSL2 F)) : Nat.card T = 2 ^ twoVal F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (stdSylow F hodd hsq hq4),
    coe_stdSylow, card_stdT hodd hsq]

theorem le_twoVal_of_dvd {m : ℕ} (h : 2 ^ m ∣ Nat.card F - 1) : m ≤ twoVal F := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  exact (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h

theorem two_pow_add_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hq4 : Nat.card F % 4 = 1)
    (c : PSL2 F) {a : ℕ} (ha : 2 ≤ a) (hc : orderOf c = 2 ^ a)
    (x : PGammaL2 F) (hxc : x * incl F c = incl F c * x)
    {k : ℕ} (hk : 1 ≤ k) (hτ : orderOf x.right = 2 ^ k) :
    2 ^ (a + k) ∣ Nat.card F - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hc2 : IsPGroup 2 (zpowers c) := IsPGroup.of_card (by rw [Nat.card_zpowers, hc])
  obtain ⟨S, hS⟩ := hc2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) S
  have hcS : c ∈ ((h • stdSylow F hodd hsq hq4 : Sylow 2 (PSL2 F)) : Subgroup (PSL2 F)) := by
    rw [hh]
    exact hS (mem_zpowers c)
  rw [mem_smul_sylow_iff, coe_stdSylow] at hcS
  set c' := h⁻¹ * c * h with hc'
  obtain ⟨y, -, ε, hy⟩ := (mem_map_stdT_iff hsq _).mp (mem_map_of_mem (incl F) hcS)
  have hordc' : orderOf (incl F c') = 2 ^ a := by
    rw [orderOf_injective (incl F) (incl_injective F), ← hc]
    exact (SemiconjBy.orderOf_eq h⁻¹ (show h⁻¹ * c = c' * h⁻¹ by rw [hc']; group)).symm
  have hε : ε = false := by
    by_contra hne
    have hne' : ε = true := by simpa using hne
    rw [hne'] at hy
    have h2 : orderOf (incl F c') ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two, hy, nm_true_mul_self])
    rw [hordc'] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  rw [hε, ← inl_tor] at hy
  have hyord : orderOf y = 2 ^ a := by
    rw [← hordc', hy, orderOf_injective _ SemidirectProduct.inl_injective,
      orderOf_injective _ (pGammaL2FullSplitTorus_injective F)]
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyord
    omega
  set x' := (incl F h)⁻¹ * x * incl F h with hx'
  have hx'c : x' * incl F c' = incl F c' * x' := by
    rw [hx', hc', map_mul, map_mul, map_inv]
    calc (incl F h)⁻¹ * x * incl F h * ((incl F h)⁻¹ * incl F c * incl F h) =
        (incl F h)⁻¹ * (x * incl F c) * incl F h := by group
      _ = (incl F h)⁻¹ * (incl F c * x) * incl F h := by rw [hxc]
      _ = _ := by group
  have hx'r : x'.right = x.right := by simp [hx', incl_apply]
  rw [hy] at hx'c
  obtain ⟨b, ε', hb⟩ := exists_nm_of_conj_tor x' hy1 (ν := y) (by rw [hx'c, mul_inv_cancel_right])
  have htw := (nm_commute_tor_iff b y ε' x'.right).mp (by rw [← hb, ← inl_tor]; exact hx'c)
  have hfix : fu F x.right y = y ∨ fu F x.right y = y⁻¹ := by
    rw [← hx'r]
    cases ε'
    · exact Or.inl htw
    · right
      simp only [twist_true] at htw
      exact inv_eq_iff_eq_inv.mp htw
  exact two_pow_add_dvd_of_fix_or_inv hp hp2 hF x.right hk hτ y hyord hfix

theorem two_mul_orderOf_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (T : Sylow 2 (PSL2 F)) (hT : 8 ≤ Nat.card T)
    (g : PGammaL2 F) (hg2 : g * g = 1)
    (hgT : ∀ t ∈ (T : Subgroup (PSL2 F)), g * incl F t = incl F t * g)
    (hgT' : g ∉ (T : Subgroup (PSL2 F)).map (incl F))
    (x : PGammaL2 F) (hxg : x * g = g * x) {m : ℕ} (hxm : x ^ 2 ^ m = 1) :
    2 * orderOf x ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hσ1 := right_ne_one hp hp2 hf hF T hT g hg2 hgT hgT'
  have hσσ : g.right * g.right = 1 := by
    have := congrArg SemidirectProduct.right hg2
    simpa using this
  have hσord : orderOf g.right = 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
  obtain ⟨hq4, hsq⟩ := mod_four_of_involution hp hp2 hF hσσ hσ1
  have hle : ∀ {j : ℕ}, 2 ^ j ∣ Nat.card F - 1 → 2 ^ j ≤ Nat.card T := fun h => by
    rw [card_sylow hodd hsq hq4 T]
    exact Nat.pow_le_pow_right (by norm_num) (le_twoVal_of_dvd h)
  have hlin : ∀ z : PGammaL2 F, z.right = 1 → z * g = g * z → ∃ c : PSL2 F, z = incl F c := by
    intro z hz1 hzg
    have hz : z = SemidirectProduct.inl z.left := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right z, hz1, map_one, mul_one]
    have := mem_pslRange_of_commute_fieldInv hp hp2 hF g hg2 hσ1 z.left
      (by rw [← hz]; exact hzg.symm)
    rw [← range_incl] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hz.trans hc.symm⟩
  have h2el : ∀ c : PSL2 F, ∀ {j : ℕ}, c ^ 2 ^ j = 1 → ∃ a, orderOf c = 2 ^ a := by
    intro c j hc
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hc)
    exact ⟨a, ha⟩
  by_cases hx1 : x.right = 1
  · obtain ⟨c, rfl⟩ := hlin x hx1 hxg
    have hcm : c ^ 2 ^ m = 1 := incl_injective F (by rw [map_pow, hxm, map_one])
    obtain ⟨a, ha⟩ := h2el c hcm
    rw [orderOf_injective (incl F) (incl_injective F), ha]
    by_cases ha2 : 2 ≤ a
    · rw [← pow_succ']
      exact hle (two_pow_add_dvd hp hp2 hF hodd hsq hq4 c ha2 ha g hxg.symm le_rfl hσord)
    · have : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hτm : x.right ^ 2 ^ m = 1 := by
    have := congrArg (fieldProj F) hxm
    rwa [map_pow, map_one] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hτm)
  have hk1 : 1 ≤ k := by
    by_contra h0
    rw [show k = 0 by omega, pow_zero, orderOf_eq_one_iff] at hk
    exact hx1 hk
  set y := x ^ 2 ^ (k - 1) with hy
  have hyr' : y.right = x.right ^ 2 ^ (k - 1) := by
    change fieldProj F (x ^ 2 ^ (k - 1)) = _
    rw [map_pow]
    rfl
  have hyr : y.right = g.right := by
    apply eq_of_mul_self_eq_one _ hσσ _ hσ1
    · rw [hyr', ← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hk1, ← hk,
        pow_orderOf_eq_one]
    · rw [hyr']
      intro h
      have h' := orderOf_dvd_of_pow_eq_one h
      rw [hk] at h'
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h'
      omega
  have hyg : Commute y g := Commute.pow_left hxg _
  have hxy : Commute x y := Commute.pow_right (Commute.refl x) _
  set c₀ := y * g with hc₀
  have hc₀r : c₀.right = 1 := by
    rw [hc₀, SemidirectProduct.mul_right, hyr, hσσ]
  obtain ⟨d, hd⟩ := hlin c₀ hc₀r (Commute.mul_left hyg (Commute.refl g))
  have hxd : x * incl F d = incl F d * x := by
    rw [← hd]
    exact Commute.mul_right hxy hxg
  have hg2' : ∀ j : ℕ, 1 ≤ j → g ^ 2 ^ j = 1 := by
    intro j hj
    rw [show 2 ^ j = 2 * 2 ^ (j - 1) by rw [← pow_succ']; congr 1; omega, pow_mul, pow_two,
      hg2, one_pow]
  have hyc : ∀ j : ℕ, 1 ≤ j → y ^ 2 ^ j = incl F (d ^ 2 ^ j) := by
    intro j hj
    rw [map_pow, ← hd, hc₀, Commute.mul_pow hyg, hg2' j hj, mul_one]
  have hm1 : 1 ≤ m := by
    by_contra h0
    rw [show m = 0 by omega, pow_zero, pow_one] at hxm
    exact hx1 (by rw [hxm]; rfl)
  have hdm : d ^ 2 ^ m = 1 := by
    apply incl_injective F
    rw [← hyc m hm1, map_one, hy, ← pow_mul, mul_comm, pow_mul, hxm, one_pow]
  obtain ⟨a, ha⟩ := h2el d hdm
  have hxpow : ∀ j : ℕ, 1 ≤ j → d ^ 2 ^ j = 1 → x ^ 2 ^ (k - 1 + j) = 1 := by
    intro j hj hdj
    rw [pow_add, pow_mul, ← hy, hyc j hj, hdj, map_one]
  by_cases ha2 : 2 ≤ a
  · have hdvd := two_pow_add_dvd hp hp2 hF hodd hsq hq4 d ha2 ha x hxd hk1 hk
    have hx := hxpow a (by omega) (by rw [← ha]; exact pow_orderOf_eq_one d)
    have hle' := Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one hx)
    calc 2 * orderOf x ≤ 2 * 2 ^ (k - 1 + a) := Nat.mul_le_mul_left 2 hle'
      _ = 2 ^ (a + k) := by rw [← pow_succ']; congr 1; omega
      _ ≤ Nat.card T := hle hdvd
  · have hd2 : d ^ 2 ^ 1 = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [ha]
      exact Nat.pow_dvd_pow 2 (by omega)
    have hx := hxpow 1 le_rfl hd2
    rw [Nat.sub_add_cancel hk1] at hx
    have hle' := Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one hx)
    have h2 := two_ne_zero_of_isOddPrimePower hodd
    have hne : (-1 : Fˣ) ≠ 1 := by
      intro h1
      apply h2
      have := congrArg (fun u : Fˣ => (u : F)) h1
      simp only [Units.val_neg, Units.val_one] at this
      linear_combination -this
    have hord : orderOf (-1 : Fˣ) = 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_eq_prime (by rw [neg_one_sq]) hne
    have hdvd := two_pow_add_dvd_of_fix_or_inv hp hp2 hF x.right hk1 hk (-1) hord
      (Or.inl (Units.ext (by simp)))
    calc 2 * orderOf x ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hle'
      _ = 2 ^ (1 + k) := by rw [← pow_succ', add_comm]
      _ ≤ Nat.card T := hle hdvd

end FieldOrd

open FieldOrd in
theorem cf81FieldOrd : CF81FieldOrd := by
  intro Y _ _ p f hp hp2 hf hY T hT φ hφ2 hφT hφT' w hwφ hw2
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  obtain ⟨m, hm⟩ := hw2 ⟨w, mem_zpowers w⟩
  have hm' : w ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [← MulEquiv.orderOf_eq (autEquiv e) w, ← card_sylowMap e T]
  refine two_mul_orderOf_le hp hp2 hf hF (sylowMap e T) (by rw [card_sylowMap]; exact hT)
    (autEquiv e φ) (by rw [← map_mul, hφ2, map_one]) ?_ ?_ (autEquiv e w)
    (by rw [← map_mul, ← map_mul, hwφ]) (m := m) (by rw [← map_pow, hm', map_one])
  · intro t ht
    rw [coe_sylowMap] at ht
    exact centralizes_map_autEquiv e T (zpowers φ) (zpowers_le.mpr hφT) _
      (mem_map_of_mem _ (mem_zpowers φ)) t ht
  · rintro ⟨t, ht, hte⟩
    rw [coe_sylowMap] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    apply hφT'
    refine ⟨s, hs, (autEquiv e).injective ?_⟩
    rw [autEquiv_conj]
    exact hte

end CFSG.ComponentClassification.GSThmB
