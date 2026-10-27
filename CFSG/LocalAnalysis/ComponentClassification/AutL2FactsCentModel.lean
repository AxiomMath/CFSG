module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentral

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped Pointwise

universe u

variable {F : Type u} [Field F] [Finite F]

omit [Finite F] in
theorem nm_true_mul_self (y : Fˣ) : nm F y true 1 * nm F y true 1 = 1 := by
  rw [nm_mul]
  simp [fu_one, nm_one]

theorem mem_map_stdT_iff (hsq : IsSquare (-1 : F)) (g : PGammaL2 F) :
    g ∈ (stdT F).map (incl F) ↔ ∃ y ∈ zpowers (stdGen F ^ 2), ∃ ε, g = nm F y ε 1 := by
  rw [show (stdT F).map (incl F) = ((stdT F).map
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))).map
        SemidirectProduct.inl by rw [Subgroup.map_map]; rfl, map_stdT hsq]
  constructor
  · rintro ⟨_, ⟨y, hy, ε, rfl⟩, rfl⟩
    exact ⟨y, hy, ε, rfl⟩
  · rintro ⟨y, hy, ε, rfl⟩
    exact ⟨_, ⟨y, hy, ε, rfl⟩, rfl⟩

omit [Finite F] in
theorem nm_mem_pslRange (hsq : IsSquare (-1 : F)) {y : Fˣ} (hy : IsSquare (y : F)) (ε : Bool) :
    nm F y ε 1 ∈ pGammaL2PSLRange F := by
  have hmem : tor F y * swp F ε ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    refine mul_mem (tor_mem_range hy) ?_
    cases ε
    · exact one_mem _
    · exact sw_mem_range hsq
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, by rw [MonoidHom.comp_apply, hz]; rfl⟩

theorem right_eq_one_of_commute_outer {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hn : 3 ≤ twoVal F) (x s : PGammaL2 F) (hs1 : s.right = 1)
    (hsL : s ∉ pGammaL2PSLRange F)
    (hsT : ∀ g ∈ (stdT F).map (incl F), s * g * s⁻¹ ∈ (stdT F).map (incl F))
    (hxT : ∀ g ∈ (stdT F).map (incl F), x * g = g * x) (hxs : x * s = s * x)
    {k : ℕ} (hk : x.right ^ 2 ^ k = 1) : x.right = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_isOddPrimePower hodd
  set c₀ := stdGen F ^ 2
  have hc₀ : orderOf c₀ = 2 ^ (twoVal F - 1) := orderOf_stdGen_sq hodd
  have hc₀T : nm F c₀ false 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨c₀, mem_zpowers _, false, rfl⟩
  have hswT : nm F 1 true 1 ∈ (stdT F).map (incl F) :=
    (mem_map_stdT_iff hsq _).mpr ⟨1, one_mem _, true, rfl⟩
  have hxc := hxT _ hc₀T
  have hσsq := fieldProj_sq_of_commute_tor hp hp2 hF x hc₀ (by omega)
    (by rw [inl_tor]; exact hxc) hk
  have hμ1 : c₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc₀
    have : 2 ≤ 2 ^ (twoVal F - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (twoVal F - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨a, ε, hxa⟩ := exists_nm_of_conj_tor x hμ1 (ν := c₀)
    (by rw [inl_tor, hxc, mul_inv_cancel_right])
  have ha : a⁻¹ = a := by
    have h := hxT _ hswT
    rw [hxa, nm_mul, nm_mul, nm_eq_nm_iff] at h
    obtain ⟨h1, -, -⟩ := h
    simp only [fu_one, twist_true, one_mul, map_one] at h1
    cases ε <;> simp only [twist_false, twist_true, mul_one, inv_one] at h1
    · simpa using h1.symm
    · simpa using h1.symm
  have hsc := hsT _ hc₀T
  obtain ⟨y, hy, ε'', hy'⟩ := (mem_map_stdT_iff hsq _).mp hsc
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
  obtain ⟨b, ε', hsb⟩ := exists_nm_of_conj_tor s hμ1 (ν := y)
    (by rw [inl_tor, inl_tor, hy'])
  rw [hs1] at hsb
  have hb2 : b ^ 2 ∈ zpowers c₀ := by
    have hsw := hsT _ hswT
    obtain ⟨y', hy'', ε''', hy'''⟩ := (mem_map_stdT_iff hsq _).mp hsw
    rw [hsb, nm_inv, nm_mul, nm_mul, nm_eq_nm_iff] at hy'''
    obtain ⟨h1, -, -⟩ := hy'''
    cases ε' <;> simp [twist_false, twist_true, fu_one] at h1 <;>
      · rw [show b ^ 2 = y' by rw [← h1, pow_two]]
        exact hy''
  have hbsq : ¬ IsSquare (b : F) := by
    intro h
    apply hsL
    rw [hsb]
    exact nm_mem_pslRange hsq h ε'
  have hbord : orderOf b = 2 ^ twoVal F := by
    have hdvd : orderOf b ∣ 2 ^ twoVal F := by
      apply orderOf_dvd_of_pow_eq_one
      obtain ⟨i, hi⟩ := hb2
      have h1 : c₀ ^ 2 ^ (twoVal F - 1) = 1 := by rw [← hc₀]; exact pow_orderOf_eq_one c₀
      calc b ^ 2 ^ twoVal F = (b ^ 2) ^ 2 ^ (twoVal F - 1) := by
            rw [← pow_mul, ← pow_succ']
            congr 2
            omega
        _ = 1 := by
            rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj']
    by_contra hne
    apply hbsq
    have : Fintype F := Fintype.ofFinite F
    have hchar : ringChar F ≠ 2 := by
      intro h
      apply h2
      have := ringChar.spec F 2
      exact_mod_cast (CharP.cast_eq_zero_iff F (ringChar F) 2).mpr (by rw [h])
    rw [FiniteField.isSquare_iff hchar b.ne_zero]
    have hjle : j ≤ twoVal F - 1 := by
      have : j ≠ twoVal F := fun h => hne (by rw [h])
      omega
    have hdvd' : 2 ^ j ∣ Fintype.card F / 2 := by
      obtain ⟨m, hm⟩ := two_pow_twoVal_dvd F
      rw [← Nat.card_eq_fintype_card]
      have hq1 : 1 ≤ Nat.card F := Finite.card_pos
      have : Nat.card F / 2 = (Nat.card F - 1) / 2 := by
        have := hodd
        obtain ⟨p', n', hp', hpodd', -, hc'⟩ := this
        rw [hc']
        have : Odd (p' ^ n') := hpodd'.pow
        obtain ⟨t, ht⟩ := this
        omega
      rw [this, hm]
      have h2t : 2 ^ twoVal F = 2 * 2 ^ (twoVal F - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [h2t, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
      exact (Nat.pow_dvd_pow 2 hjle).mul_right _
    have hb1 : b ^ 2 ^ j = 1 := by rw [← hj']; exact pow_orderOf_eq_one b
    obtain ⟨m, hm⟩ := hdvd'
    have : (b : F) ^ (Fintype.card F / 2) = ((b ^ 2 ^ j : Fˣ) : F) ^ m := by
      rw [hm, pow_mul, Units.val_pow_eq_pow_val]
    rw [this, hb1, Units.val_one, one_pow]
  have htw : twist F ε (fu F x.right b) = b := by
    have h := hxs
    rw [hxa, hsb, nm_mul, nm_mul, nm_eq_nm_iff] at h
    obtain ⟨h1, -, -⟩ := h
    cases ε' <;> simp only [twist_false, twist_true, fu_one, ha] at h1 <;> rw [mul_comm] at h1 <;>
      exact mul_right_cancel h1
  by_contra hσ1
  have hord : orderOf x.right = 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_eq_prime hσsq hσ1
  have hfix : fu F x.right b = b ∨ fu F x.right b = b⁻¹ := by
    cases ε
    · exact Or.inl htw
    · right
      simp only [twist_true] at htw
      exact inv_eq_iff_eq_inv.mp htw
  have hdvd := two_pow_add_dvd_of_fix_or_inv hp hp2 hF x.right le_rfl hord b hbord hfix
  exact not_two_pow_twoVal_succ_dvd F Finite.one_lt_card hdvd

omit [Finite F] in
theorem mem_smul_sylow_iff {G : Type*} [Group G] (P : Sylow 2 G) (g d : G) :
    d ∈ ((g • P : Sylow 2 G) : Subgroup G) ↔ g⁻¹ * d * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.smul_def, MulAut.conj_apply, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  · intro h
    exact ⟨_, h, by rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

theorem sylow_noncomm_center (hodd : IsOddPrimePower (Nat.card F)) (D : Sylow 2 (PSL2 F))
    (hD : 8 ≤ Nat.card D) :
    (∃ a ∈ (D : Subgroup (PSL2 F)), ∃ b ∈ (D : Subgroup (PSL2 F)), a * b ≠ b * a) ∧
      Nat.card ↥((D : Subgroup (PSL2 F)) ⊓ centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F)))
        = 2 := by
  obtain ⟨m, -, ⟨φ⟩⟩ := sylow_two_dihedral_of_equiv (MulEquiv.refl (PSL2 F)) hodd D
  have hcard : Nat.card D = 2 ^ (m + 1) := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hm : 2 ≤ m := by
    rw [hcard] at hD
    by_contra h
    push Not at h
    interval_cases m <;> simp_all
  refine ⟨?_, (dihedral_sylow_conclusions _ hm φ).1⟩
  have hnc : ∃ a b : DihedralGroup (2 ^ m), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact DihedralGroup.not_commutative (n := 2 ^ m) (by omega) (by omega) ⟨⟨h⟩⟩
  obtain ⟨a₁, b₁, hnc⟩ := hnc
  refine ⟨φ.symm a₁, (φ.symm a₁).2, φ.symm b₁, (φ.symm b₁).2, fun h => hnc ?_⟩
  apply φ.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext h

theorem mem_center_of_right_eq_one (hodd : IsOddPrimePower (Nat.card F)) (D : Sylow 2 (PSL2 F))
    (hD : 8 ≤ Nat.card D) (x : PGammaL2 F) (hx1 : x.right = 1) {k : ℕ} (hk : x ^ 2 ^ k = 1)
    (hxD : ∀ d ∈ (D : Subgroup (PSL2 F)), x * incl F d = incl F d * x) :
    x ∈ ((D : Subgroup (PSL2 F)) ⊓ centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F))).map
      (incl F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨a, ha, b, hb, hab⟩, hZ⟩ := sylow_noncomm_center hodd D hD
  set Z := ((D : Subgroup (PSL2 F)) ⊓ centralizer ((D : Subgroup (PSL2 F)) : Set (PSL2 F))).map
    (incl F)
  have hZcard : Nat.card Z = 2 := by
    rw [Subgroup.card_map_of_injective (incl_injective F), hZ]
  have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hx2 : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hxZ : ∀ z ∈ Z, x * z = z * x := by
    rintro _ ⟨d, hd, rfl⟩
    exact hxD d hd.1
  have hxN : zpowers x ≤ normalizer (Z : Set (PGammaL2 F)) := by
    rw [zpowers_le]
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro z hz
    exact (hxZ z hz).symm
  set R := zpowers x ⊔ Z
  have hR2 : IsPGroup 2 R := hx2.to_sup_of_normal_right' hZ2 hxN
  have hRD : ∀ r ∈ R, ∀ d ∈ (D : Subgroup (PSL2 F)), r * incl F d = incl F d * r := by
    have hle : R ≤ centralizer (((D : Subgroup (PSL2 F)).map (incl F) : Subgroup (PGammaL2 F)) :
        Set (PGammaL2 F)) := by
      apply sup_le
      · rw [zpowers_le, mem_centralizer_iff]
        rintro _ ⟨d, hd, rfl⟩
        exact (hxD d hd).symm
      · rintro _ ⟨z, hz, rfl⟩
        rw [mem_centralizer_iff]
        rintro _ ⟨d, hd, rfl⟩
        rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hz.2 d hd]
    intro r hr d hd
    exact (mem_centralizer_iff.mp (hle hr) _ ⟨d, hd, rfl⟩).symm
  have hlin := card_linearPart_le_two hodd D D.isPGroup' ha hb hab R hR2 hRD
  have hRrange : R ≤ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
    apply sup_le
    · rw [zpowers_le]
      exact ⟨x.left, SemidirectProduct.ext rfl hx1.symm⟩
    · rintro _ ⟨z, -, rfl⟩
      exact ⟨_, rfl⟩
  have hRcard : Nat.card R ≤ 2 := by
    have := Subgroup.card_map_of_injective (K := linearPart R)
      (SemidirectProduct.inl_injective (φ := pgl2FieldAut F))
    rw [Subgroup.map_comap_eq_self hRrange] at this
    rw [this]
    exact hlin
  have hZR : Z ≤ R := le_sup_right
  have hEq : Z = R := Subgroup.eq_of_le_of_card_ge hZR (by rw [hZcard]; exact hRcard)
  rw [hEq]
  exact le_sup_left (a := zpowers x) (mem_zpowers x)

theorem klein_case (hodd : IsOddPrimePower (Nat.card F)) (D : Sylow 2 (PSL2 F))
    (hD : Nat.card D < 8) (s : PGammaL2 F) (hs1 : s.right = 1) (hsL : s ∉ pGammaL2PSLRange F)
    (τ ζ : PGammaL2 F) (hτ1 : τ.right = 1) (hζr : ζ.right = 1) (hτs : τ * s = s * τ)
    (hζs : ζ * s = s * ζ) (hτD : ∀ d ∈ (D : Subgroup (PSL2 F)), τ * incl F d = incl F d * τ)
    (hζD : ∀ d ∈ (D : Subgroup (PSL2 F)), ζ * incl F d = incl F d * ζ) (hζ1 : ζ ≠ 1) :
    τ = 1 ∨ τ = ζ := by
  obtain ⟨m, hm, ⟨φ⟩⟩ := sylow_two_dihedral_of_equiv (MulEquiv.refl (PSL2 F)) hodd D
  have hcard : Nat.card D = 2 ^ (m + 1) := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hm1 : m = 1 := by
    rw [hcard] at hD
    by_contra h
    have : 2 ≤ m := by omega
    have : 2 ^ 3 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hm1
  set D' := (D : Subgroup (PSL2 F)).map
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
  have hD'card : Nat.card D' = 4 := by
    rw [Subgroup.card_map_of_injective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, hcard]
    norm_num
  have hsq : ∀ g ∈ D', g * g = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul]
    have h1 : (⟨d, hd⟩ : D) * ⟨d, hd⟩ = 1 := by
      apply φ.injective
      rw [map_mul, map_one]
      generalize φ ⟨d, hd⟩ = y
      rcases y with i | i
      · rw [DihedralGroup.r_mul_r, DihedralGroup.one_def]
        congr 1
        fin_cases i <;> rfl
      · exact DihedralGroup.sr_mul_self i
    have h2 : d * d = 1 := congrArg Subtype.val h1
    rw [h2, map_one]
  have hK : IsKleinFour D' := by
    have : Nontrivial D' := by
      rw [← Finite.one_lt_card_iff_nontrivial, hD'card]
      norm_num
    refine ⟨hD'card, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
    apply orderOf_eq_prime
    · rw [pow_two]
      exact Subtype.ext (hsq g g.2)
    · exact hg
  have hC := pgl2_kleinFour_centralizer_eq_self F hodd D' hK
  have hcent : ∀ x : PGammaL2 F, x.right = 1 →
      (∀ d ∈ (D : Subgroup (PSL2 F)), x * incl F d = incl F d * x) → x.left ∈ D' := by
    intro x hx1 hxD
    rw [← hC, mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have h := hxD d hd
    have hx : x = SemidirectProduct.inl x.left := SemidirectProduct.ext rfl hx1
    rw [hx, incl_apply, ← map_mul, ← map_mul] at h
    exact (SemidirectProduct.inl_injective h).symm
  have hτD' := hcent τ hτ1 hτD
  have hζD' := hcent ζ hζr hζD
  have hτ : τ = SemidirectProduct.inl τ.left := SemidirectProduct.ext rfl hτ1
  have hζ : ζ = SemidirectProduct.inl ζ.left := SemidirectProduct.ext rfl hζr
  have hs : s = SemidirectProduct.inl s.left := SemidirectProduct.ext rfl hs1
  by_contra hne
  push Not at hne
  obtain ⟨hτne1, hτζ⟩ := hne
  have hτ1' : (⟨τ.left, hτD'⟩ : D') ≠ 1 := by
    intro h
    apply hτne1
    rw [hτ, show τ.left = 1 from congrArg Subtype.val h, map_one]
  have hζ1' : (⟨ζ.left, hζD'⟩ : D') ≠ 1 := by
    intro h
    apply hζ1
    rw [hζ, show ζ.left = 1 from congrArg Subtype.val h, map_one]
  have hτζ' : (⟨τ.left, hτD'⟩ : D') ≠ ⟨ζ.left, hζD'⟩ := by
    intro h
    apply hτζ
    rw [hτ, hζ, show τ.left = ζ.left from congrArg Subtype.val h]
  have hcomm : ∀ x : PGammaL2 F, x = SemidirectProduct.inl x.left → x * s = s * x →
      x.left * s.left = s.left * x.left := by
    intro x hx hxs
    rw [hx, hs, ← map_mul, ← map_mul] at hxs
    exact SemidirectProduct.inl_injective hxs
  have hsτ := hcomm τ hτ hτs
  have hsζ := hcomm ζ hζ hζs
  apply hsL
  have hsD' : s.left ∈ D' := by
    rw [← hC, mem_centralizer_iff]
    intro w hw
    by_cases hw1 : (⟨w, hw⟩ : D') = 1
    · rw [show w = 1 from congrArg Subtype.val hw1, one_mul, mul_one]
    by_cases hwτ : (⟨w, hw⟩ : D') = ⟨τ.left, hτD'⟩
    · rw [show w = τ.left from congrArg Subtype.val hwτ]
      exact hsτ
    by_cases hwζ : (⟨w, hw⟩ : D') = ⟨ζ.left, hζD'⟩
    · rw [show w = ζ.left from congrArg Subtype.val hwζ]
      exact hsζ
    have := IsKleinFour.eq_mul_of_ne_all hτ1' hζ1' hτζ' hw1 hwτ hwζ
    rw [show w = τ.left * ζ.left from congrArg Subtype.val this]
    rw [mul_assoc, hsζ, ← mul_assoc, hsτ, mul_assoc]
  obtain ⟨d, -, hd⟩ := hsD'
  rw [hs, ← hd]
  exact ⟨d, rfl⟩

theorem eight_dvd_of_even {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : Even f) :
    8 ∣ p ^ f - 1 := by
  obtain ⟨g, rfl⟩ := hf
  rw [← two_mul, pow_mul']
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := g)
  rw [hk, show (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) by ring_nf; omega]
  obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
  rw [hm]
  exact ⟨m, by ring⟩

theorem right_eq_one_of_commute_outer_sylow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (D : Sylow 2 (PSL2 F)) (s : PGammaL2 F) (hs1 : s.right = 1)
    (hsL : s ∉ pGammaL2PSLRange F)
    (hsD : ∀ d ∈ (D : Subgroup (PSL2 F)), s * incl F d * s⁻¹ ∈ (D : Subgroup (PSL2 F)).map
      (incl F))
    (x : PGammaL2 F) {k : ℕ} (hk : x ^ 2 ^ k = 1) (hxs : x * s = s * x)
    (hxD : ∀ d ∈ (D : Subgroup (PSL2 F)), x * incl F d = incl F d * x) : x.right = 1 := by
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hk' : x.right ^ 2 ^ k = 1 := by
    have := congrArg (fieldProj F) hk
    rwa [map_pow, map_one] at this
  rcases Nat.even_or_odd f with hfe | hfo
  · have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
    have hsq : IsSquare (-1 : F) := by
      have : Fintype F := Fintype.ofFinite F
      classical
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
      omega
    have hn : 3 ≤ twoVal F := by
      have h8 : 2 ^ 3 ∣ Nat.card F - 1 := by rw [hF]; exact eight_dvd_of_even hp hp2 hfe
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
        have := Finite.one_lt_card (α := F); omega)).mp h8
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) D
    set c := incl F h
    have hD : ∀ d : PSL2 F, d ∈ (D : Subgroup (PSL2 F)) ↔ h⁻¹ * d * h ∈ stdT F := by
      intro d
      rw [← hh, mem_smul_sylow_iff, coe_stdSylow]
    have hconjT : ∀ g ∈ (stdT F).map (incl F), c * g * c⁻¹ ∈ (D : Subgroup (PSL2 F)).map
        (incl F) := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨h * t * h⁻¹, (hD _).mpr (by rwa [show h⁻¹ * (h * t * h⁻¹) * h = t by group]), ?_⟩
      simp only [c, map_mul, map_inv]
    have hconjD : ∀ g ∈ (D : Subgroup (PSL2 F)).map (incl F), c⁻¹ * g * c ∈ (stdT F).map
        (incl F) := by
      rintro _ ⟨d, hd, rfl⟩
      exact ⟨h⁻¹ * d * h, (hD d).mp hd, by simp only [c, map_mul, map_inv]⟩
    have hx' := right_eq_one_of_commute_outer hp hp2 hF hodd hsq hn (c⁻¹ * x * c) (c⁻¹ * s * c)
      (by simp [c, incl_apply, hs1])
      (by
        intro hmem
        apply hsL
        have : c * (c⁻¹ * s * c) * c⁻¹ ∈ pGammaL2PSLRange F :=
          (pGammaL2PSLRange F).mul_mem ((pGammaL2PSLRange F).mul_mem ⟨h, rfl⟩ hmem)
            ((pGammaL2PSLRange F).inv_mem ⟨h, rfl⟩)
        simpa [mul_assoc] using this)
      (by
        intro g hg
        have h1 := hconjT g hg
        obtain ⟨d, hd, hd'⟩ := h1
        have h2 := hsD d hd
        rw [hd'] at h2
        have h3 := hconjD _ h2
        have : c⁻¹ * (s * (c * g * c⁻¹) * s⁻¹) * c = c⁻¹ * s * c * g * (c⁻¹ * s * c)⁻¹ := by group
        rwa [this] at h3)
      (by
        intro g hg
        obtain ⟨d, hd, hd'⟩ := hconjT g hg
        have h1 := hxD d hd
        rw [hd'] at h1
        calc c⁻¹ * x * c * g = c⁻¹ * (x * (c * g * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * g * c⁻¹) * x) * c := by rw [h1]
          _ = g * (c⁻¹ * x * c) := by group)
      (by
        calc c⁻¹ * x * c * (c⁻¹ * s * c) = c⁻¹ * (x * s) * c := by group
          _ = c⁻¹ * (s * x) * c := by rw [hxs]
          _ = c⁻¹ * s * c * (c⁻¹ * x * c) := by group)
      (k := k) (by
        have : (c⁻¹ * x * c).right = x.right := by simp [c, incl_apply]
        rw [this]
        exact hk')
    simpa [c, incl_apply] using hx'
  · exact eq_one_of_two_power_ringAut hp hF hfo x.right k hk'

theorem l2Cent_model {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (D : Sylow 2 (PSL2 F)) (s : PGammaL2 F) (hs1 : s.right = 1)
    (hsL : s ∉ pGammaL2PSLRange F)
    (hsD : ∀ d ∈ (D : Subgroup (PSL2 F)), s * incl F d * s⁻¹ ∈ (D : Subgroup (PSL2 F)).map
      (incl F))
    (τ ζ : PGammaL2 F) (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) (hζ2 : ∃ k : ℕ, ζ ^ 2 ^ k = 1)
    (hτs : τ * s = s * τ) (hζs : ζ * s = s * ζ)
    (hτD : ∀ d ∈ (D : Subgroup (PSL2 F)), τ * incl F d = incl F d * τ)
    (hζD : ∀ d ∈ (D : Subgroup (PSL2 F)), ζ * incl F d = incl F d * ζ) (hζ1 : ζ ≠ 1) :
    τ = 1 ∨ τ = ζ := by
  have hodd := isOddPrimePower_of hp hp2 hf hF
  obtain ⟨kτ, hkτ⟩ := hτ2
  obtain ⟨kζ, hkζ⟩ := hζ2
  have hτ1 := right_eq_one_of_commute_outer_sylow hp hp2 hf hF D s hs1 hsL hsD τ hkτ hτs hτD
  have hζr := right_eq_one_of_commute_outer_sylow hp hp2 hf hF D s hs1 hsL hsD ζ hkζ hζs hζD
  by_cases hD : 8 ≤ Nat.card D
  · have hτZ := mem_center_of_right_eq_one hodd D hD τ hτ1 hkτ hτD
    have hζZ := mem_center_of_right_eq_one hodd D hD ζ hζr hkζ hζD
    set Z := ((D : Subgroup (PSL2 F)) ⊓ centralizer ((D : Subgroup (PSL2 F)) :
      Set (PSL2 F))).map (incl F)
    have hZcard : Nat.card Z = 2 := by
      rw [Subgroup.card_map_of_injective (incl_injective F), (sylow_noncomm_center hodd D hD).2]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZcard
    by_cases hτ1' : τ = 1
    · exact Or.inl hτ1'
    · right
      have e1 := hy ⟨τ, hτZ⟩ (fun h => hτ1' (congrArg Subtype.val h))
      have e2 := hy ⟨ζ, hζZ⟩ (fun h => hζ1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (e1.trans e2.symm)
  · exact klein_case hodd D (by omega) s hs1 hsL τ ζ hτ1 hζr hτs hζs hτD hζD hζ1

end CFSG.ComponentClassification.AutL2Facts
