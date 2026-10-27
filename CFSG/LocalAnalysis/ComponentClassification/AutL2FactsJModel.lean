module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped Pointwise

universe u

variable {F : Type u} [Field F] [Finite F]

theorem mem_zpowers_of_orderOf_dvd {G : Type*} [Group G] [Finite G] [IsCyclic G] (c y : G)
    (h : orderOf y ∣ orderOf c) : y ∈ zpowers c := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set k := orderOf c
  have hk : 0 < k := orderOf_pos c
  have hle := IsCyclic.card_pow_eq_one_le (α := G) hk
  have hsub : (zpowers c : Set G).toFinset ⊆ Finset.univ.filter fun x => x ^ k = 1 := by
    intro x hx
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_of_mem_zpowers hx)
  have hcard : (zpowers c : Set G).toFinset.card = k := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, SetLike.coe_sort_coe, Nat.card_zpowers]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hy : y ∈ Finset.univ.filter fun x => x ^ k = 1 := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact orderOf_dvd_iff_pow_eq_one.mp h
  rw [← heq] at hy
  simpa using hy

theorem two_pow_dvd_sub_or_add {t : ℤ} (ht : Odd t) {n : ℕ} (h : (2 : ℤ) ^ (n + 1) ∣ t ^ 2 - 1) :
    (2 : ℤ) ^ n ∣ t - 1 ∨ (2 : ℤ) ^ n ∣ t + 1 := by
  obtain ⟨k, rfl⟩ := ht
  have hfac : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by ring
  rw [hfac, pow_succ, mul_comm] at h
  have h' : (2 : ℤ) ^ n ∣ 2 * k * (k + 1) :=
    (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    have hcop : IsCoprime ((2 : ℤ) ^ n) (k + 1) :=
      IsCoprime.pow_left (Int.isCoprime_two_left.mpr ⟨m, by rw [hm]; ring⟩)
    have := hcop.dvd_of_dvd_mul_right h'
    rwa [show 2 * k + 1 - 1 = 2 * k by ring]
  · right
    have hcop : IsCoprime ((2 : ℤ) ^ n) k :=
      IsCoprime.pow_left (Int.isCoprime_two_left.mpr ⟨m, hm⟩)
    have h'' : (2 : ℤ) ^ n ∣ k * (2 * (k + 1)) := by rwa [show k * (2 * (k + 1)) =
      2 * k * (k + 1) by ring]
    have := hcop.dvd_of_dvd_mul_left h''
    rwa [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

theorem fix_or_inv_of_order_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (σ : F ≃+* F) (hσ : orderOf σ = 2 ^ 1) (y : Fˣ)
    (hy : orderOf y = 2 ^ (twoVal F - 1)) (hn : 1 ≤ twoVal F) :
    fu F σ y = y ∨ fu F σ y = y⁻¹ := by
  obtain ⟨t, u, ht, hu, hcard, hσx⟩ := exists_odd_pow_of_orderOf_two_pow hp hp2 hF σ le_rfl hσ
  rw [pow_one] at hcard
  have hσy : fu F σ y = y ^ (t ^ u) := by
    ext
    simp [hσx]
  have h2n : (2 : ℤ) ^ (twoVal F - 1 + 1) ∣ (t : ℤ) ^ 2 - 1 := by
    have h := two_pow_twoVal_dvd F
    rw [hcard] at h
    have ht1 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ ht.pos
    have := Int.natCast_dvd_natCast.mpr h
    push_cast [Nat.cast_sub ht1] at this
    rwa [Nat.sub_add_cancel hn]
  have htu1 : 1 ≤ t ^ u := Nat.one_le_pow _ _ ht.pos
  rcases two_pow_dvd_sub_or_add (by exact_mod_cast ht) h2n with h | h
  · left
    have h' := (two_pow_dvd_pow_sub_one_iff (by exact_mod_cast ht) hu _).mpr h
    have h'' : 2 ^ (twoVal F - 1) ∣ t ^ u - 1 := by
      have : ((2 ^ (twoVal F - 1) : ℕ) : ℤ) ∣ ((t ^ u - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub htu1]; exact h'
      exact Int.natCast_dvd_natCast.mp this
    rw [hσy]
    rw [← hy] at h''
    have hh := orderOf_dvd_iff_pow_eq_one.mp h''
    rw [pow_sub _ htu1, pow_one] at hh
    exact mul_inv_eq_one.mp hh
  · right
    have h' := (two_pow_dvd_pow_add_one_iff (by exact_mod_cast ht) hu _).mpr h
    have h'' : 2 ^ (twoVal F - 1) ∣ t ^ u + 1 := by
      have : ((2 ^ (twoVal F - 1) : ℕ) : ℤ) ∣ ((t ^ u + 1 : ℕ) : ℤ) := by
        push_cast; exact h'
      exact Int.natCast_dvd_natCast.mp this
    rw [hσy]
    rw [← hy] at h''
    have hh := orderOf_dvd_iff_pow_eq_one.mp h''
    rw [pow_succ] at hh
    exact eq_inv_of_mul_eq_one_left hh

theorem inf_pslRange_eq (T : Sylow 2 (PSL2 F)) (R : Subgroup (PGammaL2 F)) (hR : IsPGroup 2 R)
    (hTR : (T : Subgroup (PSL2 F)).map (incl F) ≤ R) :
    R ⊓ pGammaL2PSLRange F = (T : Subgroup (PSL2 F)).map (incl F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (le_inf hTR (by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩))
  set H := (R ⊓ pGammaL2PSLRange F).comap (incl F)
  have hHmap : H.map (incl F) = R ⊓ pGammaL2PSLRange F := Subgroup.map_comap_eq_self inf_le_right
  have hH2 : IsPGroup 2 H := (hR.to_le inf_le_left).comap_of_injective _ (incl_injective F)
  obtain ⟨S, hS⟩ := hH2.exists_le_sylow
  rw [← hHmap, Subgroup.card_map_of_injective (incl_injective F),
    Subgroup.card_map_of_injective (incl_injective F), Sylow.card_eq_multiplicity T,
    ← Sylow.card_eq_multiplicity S]
  exact Subgroup.card_le_of_le hS

theorem pslRange_conj_mem (g : PGammaL2 F) {x : PGammaL2 F} (hx : x ∈ pGammaL2PSLRange F) :
    g * x * g⁻¹ ∈ pGammaL2PSLRange F := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, (conj_incl g y).symm⟩

theorem conj_mem_of_mem (T : Sylow 2 (PSL2 F)) (R : Subgroup (PGammaL2 F)) (hR : IsPGroup 2 R)
    (hTR : (T : Subgroup (PSL2 F)).map (incl F) ≤ R) {x : PGammaL2 F} (hx : x ∈ R) :
    ∀ g ∈ (T : Subgroup (PSL2 F)).map (incl F), x * g * x⁻¹ ∈
      (T : Subgroup (PSL2 F)).map (incl F) := by
  intro g hg
  rw [← inf_pslRange_eq T R hR hTR] at hg ⊢
  exact ⟨R.mul_mem (R.mul_mem hx hg.1) (R.inv_mem hx),
    pslRange_conj_mem x hg.2⟩

theorem exists_nm_of_normalizes_stdT (hodd : IsOddPrimePower (Nat.card F))
    (hsq : IsSquare (-1 : F)) (hn : 3 ≤ twoVal F) (s : PGammaL2 F)
    (hsT : ∀ g ∈ (stdT F).map (incl F), s * g * s⁻¹ ∈ (stdT F).map (incl F)) :
    ∃ b ε, s = nm F b ε s.right := by
  set c₀ := stdGen F ^ 2
  have hc₀ : orderOf c₀ = 2 ^ (twoVal F - 1) := orderOf_stdGen_sq hodd
  have hc₀T : nm F c₀ false 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨c₀, mem_zpowers _, false, rfl⟩
  have hμ1 : c₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc₀
    have : 2 ≤ 2 ^ (twoVal F - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (twoVal F - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨y, -, ε'', hy'⟩ := (mem_map_stdT_iff hsq _).mp (hsT _ hc₀T)
  have hε'' : ε'' = false := by
    by_contra hne
    have hne' : ε'' = true := by simpa using hne
    rw [hne'] at hy'
    have hsq1 : s * (nm F c₀ false 1 * nm F c₀ false 1) * s⁻¹ = 1 := by
      calc s * (nm F c₀ false 1 * nm F c₀ false 1) * s⁻¹ =
          (s * nm F c₀ false 1 * s⁻¹) * (s * nm F c₀ false 1 * s⁻¹) := by group
        _ = 1 := by rw [hy', nm_true_mul_self]
    rw [conj_eq_one_iff, nm_mul, ← nm_one, nm_eq_nm_iff] at hsq1
    have h3 := hsq1.1
    simp only [twist_false, fu_one] at h3
    have hord : orderOf c₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    rw [hc₀] at hord
    have := Nat.le_of_dvd (by norm_num) hord
    have : 2 ^ 2 ≤ 2 ^ (twoVal F - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hε''] at hy'
  exact exists_nm_of_conj_tor s hμ1 (ν := y) (by rw [inl_tor, inl_tor, hy'])

omit [Finite F] in
theorem twist_zpow (ε : Bool) (x : Fˣ) (i : ℤ) : twist F ε (x ^ i) = twist F ε x ^ i := by
  cases ε
  · rfl
  · simp

omit [Finite F] in
@[simp] theorem twist_one (ε : Bool) : twist F ε 1 = 1 := by
  cases ε <;> simp

omit [Finite F] in
theorem twist_twist_self (ε : Bool) (x : Fˣ) : twist F ε (twist F ε x) = x := by
  cases ε <;> simp

omit [Finite F] in
theorem nm_false_pow (x : Fˣ) (j : ℕ) : nm F x false 1 ^ j = nm F (x ^ j) false 1 := by
  induction j with
  | zero => simp [nm_one]
  | succ j ih => rw [pow_succ, ih, nm_mul]; simp [pow_succ, fu_one]

theorem decomp_fieldInv {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hq4 : Nat.card F % 4 = 1)
    (hn : 3 ≤ twoVal F) (R : Subgroup (PGammaL2 F)) (hR : IsPGroup 2 R)
    (hTR : (stdT F).map (incl F) ≤ R) (y : PGammaL2 F) (hyR : y ∈ R) (hy2 : y * y = 1)
    (hyr : y.right ≠ 1) :
    ∃ t ∈ (stdT F).map (incl F), ∃ w ∈ R,
      (∀ g ∈ (stdT F).map (incl F), w * g = g * w) ∧ y = t * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₀ := stdSylow F hodd hsq hq4
  have hS₀ : (S₀ : Subgroup (PSL2 F)) = stdT F := coe_stdSylow hodd hsq hq4
  have hnorm := conj_mem_of_mem S₀ R hR (by rw [hS₀]; exact hTR) hyR
  rw [hS₀] at hnorm
  obtain ⟨b, ε', hyb⟩ := exists_nm_of_normalizes_stdT hodd hsq hn y hnorm
  set σ := y.right with hσdef
  have hσσ : σ * σ = 1 := by
    have := congrArg SemidirectProduct.right hy2
    simpa using this
  have hσ2 : orderOf σ = 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hσσ) hyr
  have hb1 : b * twist F ε' (fu F σ b) = 1 := by
    have h := hy2
    rw [hyb, nm_mul, ← nm_one, nm_eq_nm_iff] at h
    exact h.1
  have hσb : fu F σ b = twist F ε' b⁻¹ := by
    have : twist F ε' (fu F σ b) = b⁻¹ := eq_inv_of_mul_eq_one_right hb1
    rw [← this, twist_twist_self]
  have hsw : nm F 1 true 1 ∈ R := hTR ((mem_map_stdT_iff hsq _).mpr ⟨1, one_mem _, true, rfl⟩)
  have hysw : y * nm F 1 true 1 ∈ R := R.mul_mem hyR hsw
  have hsq' : (y * nm F 1 true 1) * (y * nm F 1 true 1) = nm F (b * b) false 1 := by
    rw [hyb, nm_mul, nm_mul]
    simp only [map_one, twist_one, mul_one, Bool.xor_true, Bool.xor_self, hσσ]
    rw [hσb, twist_twist]
    cases ε' <;> simp
  obtain ⟨k, hk⟩ := hR ⟨_, hysw⟩
  have hk' : (b * b) ^ 2 ^ k = 1 := by
    have h1 : ((y * nm F 1 true 1) * (y * nm F 1 true 1)) ^ 2 ^ k = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm, pow_mul]
      have := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      rw [this, one_pow]
    rw [hsq', nm_false_pow, ← nm_one, nm_eq_nm_iff] at h1
    exact h1.1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (show
    b ^ 2 ^ (k + 1) = 1 by rw [pow_succ', pow_mul, sq]; exact hk'))
  set c₀ := stdGen F ^ 2
  have hc₀ : orderOf c₀ = 2 ^ (twoVal F - 1) := orderOf_stdGen_sq hodd
  have hjn : j ≤ twoVal F := by
    have h1 : 2 ^ j ∣ Nat.card F - 1 := by
      rw [← hj, ← Nat.card_units]
      exact orderOf_dvd_natCard b
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp h1
  have hjn' : j ≠ twoVal F := by
    intro hjeq
    rw [hjeq] at hj
    have hfix : fu F σ b = b ∨ fu F σ b = b⁻¹ := by
      rw [hσb]
      cases ε'
      · right; rfl
      · left; simp
    have := two_pow_add_dvd_of_fix_or_inv hp hp2 hF σ le_rfl hσ2 b hj hfix
    exact not_two_pow_twoVal_succ_dvd F Finite.one_lt_card this
  have hb : b ∈ zpowers c₀ := by
    apply mem_zpowers_of_orderOf_dvd
    rw [hj, hc₀]
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨ε'', hε''⟩ : ∃ ε'' : Bool, twist F ε'' (fu F σ c₀) = c₀ := by
    rcases fix_or_inv_of_order_two hp hp2 hF σ hσ2 c₀ hc₀ (by omega) with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, by rw [h, twist_true, inv_inv]⟩
  have hfixall : ∀ y₁ ∈ zpowers c₀, twist F ε'' (fu F σ y₁) = y₁ := by
    rintro _ ⟨i, rfl⟩
    simp only [map_zpow, twist_zpow, hε'']
  have ht : nm F b (ε' ^^ ε'') 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨b, hb, _, rfl⟩
  have hyt : y = nm F b (ε' ^^ ε'') 1 * nm F 1 ε'' σ := by
    rw [hyb, nm_mul]
    simp [fu_one]
  refine ⟨_, ht, nm F 1 ε'' σ, ?_, ?_, hyt⟩
  · have : nm F 1 ε'' σ = (nm F b (ε' ^^ ε'') 1)⁻¹ * y := by rw [hyt]; group
    rw [this]
    exact R.mul_mem (R.inv_mem (hTR ht)) hyR
  · intro g hg
    obtain ⟨y₁, hy₁, ε, rfl⟩ := (mem_map_stdT_iff hsq _).mp hg
    rw [nm_mul, nm_mul, hfixall y₁ hy₁]
    simp [fu_one, Bool.xor_comm]

theorem l2J_model {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (T : Sylow 2 (PSL2 F)) (R : Subgroup (PGammaL2 F))
    (hR : IsPGroup 2 R) (hTR : (T : Subgroup (PSL2 F)).map (incl F) ≤ R)
    (E : Subgroup (PGammaL2 F)) (hER : E ≤ R)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE8 : Nat.card E = 8) :
    E ≤ (T : Subgroup (PSL2 F)).map (incl F) ⊔
      (R ⊓ centralizer (((T : Subgroup (PSL2 F)).map (incl F) : Subgroup (PGammaL2 F)) :
        Set (PGammaL2 F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hlin : Nat.card (linearPart E) ≤ 4 :=
    pgl2_card_le_four_of_sq hodd _ fun g hg => SemidirectProduct.inl_injective (by
      rw [map_mul, map_one]; exact hE2 _ hg)
  obtain ⟨y, hyE, hyr⟩ : ∃ y ∈ E, y.right ≠ 1 := by
    by_contra h
    push Not at h
    have hpi : Nat.card (E.map (fieldProj F)) ≤ 1 := by
      apply Finite.card_le_one_iff_subsingleton.mpr
      constructor
      rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
      apply Subtype.ext
      change a.right = b.right
      rw [h a ha, h b hb]
    have := card_eq_linearPart_mul E
    rw [hE8] at this
    have : 8 ≤ 4 * 1 := by
      calc 8 = _ := this
        _ ≤ 4 * 1 := Nat.mul_le_mul hlin hpi
    omega
  have hy2 := hE2 y hyE
  have hyσ : y.right * y.right = 1 := by
    have := congrArg SemidirectProduct.right hy2
    simpa using this
  have hfe : Even f := even_of_ringAut hp hF hyσ hyr
  have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
  have hsq : IsSquare (-1 : F) := by
    have : Fintype F := Fintype.ofFinite F
    classical
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have hn : 3 ≤ twoVal F := by
    have h8 : 2 ^ 3 ∣ Nat.card F - 1 := by rw [hF]; exact eight_dvd_of_even hp hp2 hfe
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp h8
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    commute_of_forall_sq E hE2 ha hb
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) T
  set c := incl F h
  have hTmem : ∀ d : PSL2 F, d ∈ (T : Subgroup (PSL2 F)) ↔ h⁻¹ * d * h ∈ stdT F := by
    intro d
    rw [← hh, mem_smul_sylow_iff, coe_stdSylow]
  set R' := R.map (MulAut.conj c⁻¹).toMonoidHom
  have hR' : IsPGroup 2 R' := hR.map _
  have hTR' : (stdT F).map (incl F) ≤ R' := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨c * incl F t * c⁻¹, hTR ⟨h * t * h⁻¹, (hTmem _).mpr (by
      rwa [show h⁻¹ * (h * t * h⁻¹) * h = t by group]), by rw [map_mul, map_mul, map_inv]⟩, ?_⟩
    change MulAut.conj c⁻¹ (c * incl F t * c⁻¹) = incl F t
    rw [MulAut.conj_apply]
    group
  intro x hx
  by_cases hxr : x.right = 1
  ·
    have hxL : x ∈ pGammaL2PSLRange F := by
      rw [left_mem_of_right_eq_one hxr]
      exact mem_pslRange_of_commute_fieldInv hp hp2 hF y hy2 hyr x.left (by
        rw [← left_mem_of_right_eq_one hxr]; exact hcommE y hyE x hx)
    have : x ∈ R ⊓ pGammaL2PSLRange F := ⟨hER hx, hxL⟩
    rw [inf_pslRange_eq T R hR hTR] at this
    exact le_sup_left (a := (T : Subgroup (PSL2 F)).map (incl F)) this
  ·
    have hx' : c⁻¹ * x * c ∈ R' := ⟨x, hER hx, by
      change MulAut.conj c⁻¹ x = _
      rw [MulAut.conj_apply, inv_inv]⟩
    have hxx : (c⁻¹ * x * c) * (c⁻¹ * x * c) = 1 := by
      calc (c⁻¹ * x * c) * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
        _ = 1 := by rw [hE2 x hx]; group
    have hxr' : (c⁻¹ * x * c).right ≠ 1 := by simpa [c, incl_apply] using hxr
    obtain ⟨t, ht, w, hwR, hwC, hxtw⟩ := decomp_fieldInv hp hp2 hF hodd hsq hq4 hn R' hR' hTR'
      (c⁻¹ * x * c) hx' hxx hxr'
    have hxeq : x = (c * t * c⁻¹) * (c * w * c⁻¹) := by
      have : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      rw [this, hxtw]
      group
    rw [hxeq]
    apply mul_mem
    · apply le_sup_left (a := (T : Subgroup (PSL2 F)).map (incl F))
      obtain ⟨t₀, ht₀, rfl⟩ := ht
      exact ⟨h * t₀ * h⁻¹, (hTmem _).mpr (by
        rwa [show h⁻¹ * (h * t₀ * h⁻¹) * h = t₀ by group]), by rw [map_mul, map_mul, map_inv]⟩
    · apply le_sup_right (b := R ⊓ centralizer (((T : Subgroup (PSL2 F)).map (incl F) :
        Subgroup (PGammaL2 F)) : Set (PGammaL2 F)))
      refine ⟨?_, ?_⟩
      · obtain ⟨r, hr, hrw⟩ := hwR
        rw [← hrw]
        change c * (MulAut.conj c⁻¹ r) * c⁻¹ ∈ R
        rw [MulAut.conj_apply, inv_inv, show c * (c⁻¹ * r * c) * c⁻¹ = r by group]
        exact hr
      · change c * w * c⁻¹ ∈ centralizer _
        rw [mem_centralizer_iff]
        rintro _ ⟨d, hd, rfl⟩
        have hd' : incl F (h⁻¹ * d * h) ∈ (stdT F).map (incl F) :=
          ⟨h⁻¹ * d * h, (hTmem d).mp hd, rfl⟩
        have h1 := hwC _ hd'
        have e1 : incl F d = c * incl F (h⁻¹ * d * h) * c⁻¹ := by
          simp only [c, map_mul, map_inv]
          group
        rw [e1]
        calc c * incl F (h⁻¹ * d * h) * c⁻¹ * (c * w * c⁻¹) =
            c * (incl F (h⁻¹ * d * h) * w) * c⁻¹ := by group
          _ = c * (w * incl F (h⁻¹ * d * h)) * c⁻¹ := by rw [h1]
          _ = c * w * c⁻¹ * (c * incl F (h⁻¹ * d * h) * c⁻¹) := by group

end CFSG.ComponentClassification.AutL2Facts
