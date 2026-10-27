module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActBase
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisFusion
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallOutChar
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActModel

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2Act

open CFSG Subgroup Equiv GorensteinWalter AutL2Facts
open CFSG.ComponentClassification.CatFactsSmall

variable {F : Type} [Field F] [Finite F]

open Classical in
@[expose] def dlog8 (a : Fˣ) : ZMod 8 :=
  if h : a ∈ zpowers (stdGen F) then ((mem_zpowers_iff.mp h).choose : ZMod 8) else 0

theorem orderOf_stdGen_eq_eight (h3 : twoVal F = 3) : orderOf (stdGen F) = 8 := by
  rw [orderOf_stdGen, h3]
  norm_num

theorem dlog8_zpow (h3 : twoVal F = 3) (k : ℤ) : dlog8 (stdGen F ^ k) = k := by
  have hmem : stdGen F ^ k ∈ zpowers (stdGen F) := zpow_mem (mem_zpowers _) k
  rw [dlog8, dite_eq_left hmem]
  have hspec := (mem_zpowers_iff.mp hmem).choose_spec
  rw [zpow_eq_zpow_iff_modEq, orderOf_stdGen_eq_eight h3] at hspec
  exact (ZMod.intCast_eq_intCast_iff _ _ 8).mpr (by exact_mod_cast hspec)

theorem zpow_dlog8 (h3 : twoVal F = 3) {a : Fˣ} (ha : a ∈ zpowers (stdGen F)) :
    stdGen F ^ ((dlog8 a).val : ℤ) = a := by
  obtain ⟨k, rfl⟩ := ha
  simp only
  rw [dlog8_zpow h3, ZMod.val_intCast]
  have := zpow_mod_orderOf (stdGen F) k
  rw [orderOf_stdGen_eq_eight h3] at this
  exact_mod_cast this

theorem dlog8_one (h3 : twoVal F = 3) : dlog8 (1 : Fˣ) = 0 := by
  rw [← zpow_zero (stdGen F), dlog8_zpow h3, Int.cast_zero]

theorem dlog8_mul (h3 : twoVal F = 3) {a b : Fˣ} (ha : a ∈ zpowers (stdGen F))
    (hb : b ∈ zpowers (stdGen F)) : dlog8 (a * b) = dlog8 a + dlog8 b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  simp only
  rw [← zpow_add, dlog8_zpow h3, dlog8_zpow h3, dlog8_zpow h3, Int.cast_add]

theorem dlog8_inv (h3 : twoVal F = 3) {a : Fˣ} (ha : a ∈ zpowers (stdGen F)) :
    dlog8 a⁻¹ = -dlog8 a := by
  obtain ⟨i, rfl⟩ := ha
  simp only
  rw [← zpow_neg, dlog8_zpow h3, dlog8_zpow h3, Int.cast_neg]

theorem eq_one_of_dlog8_eq_zero (h3 : twoVal F = 3) {a : Fˣ} (ha : a ∈ zpowers (stdGen F))
    (h0 : dlog8 a = 0) : a = 1 := by
  rw [← zpow_dlog8 h3 ha, h0, ZMod.val_zero, Nat.cast_zero, zpow_zero]

@[expose] def rU8 (σ : F ≃+* F) : ZMod 8 := dlog8 (fu F σ (stdGen F))

theorem fu_mem_zpowers_stdGen (σ : F ≃+* F) {a : Fˣ} (ha : a ∈ zpowers (stdGen F)) :
    fu F σ a ∈ zpowers (stdGen F) :=
  fu_mem_zpowers σ _ ha

theorem dlog8_fu (h3 : twoVal F = 3) (σ : F ≃+* F) {a : Fˣ} (ha : a ∈ zpowers (stdGen F)) :
    dlog8 (fu F σ a) = rU8 σ * dlog8 a := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (fu_mem_zpowers_stdGen σ (mem_zpowers (stdGen F)))
  simp only
  rw [map_zpow, ← hm, ← zpow_mul, dlog8_zpow h3, rU8, ← hm, dlog8_zpow h3, dlog8_zpow h3,
    Int.cast_mul]

theorem rU8_mul (h3 : twoVal F = 3) (σ τ : F ≃+* F) : rU8 (σ * τ) = rU8 σ * rU8 τ := by
  rw [rU8, fu_mul, dlog8_fu h3 σ (fu_mem_zpowers_stdGen τ (mem_zpowers _))]
  rfl

theorem rU8_one (h3 : twoVal F = 3) : rU8 (1 : F ≃+* F) = 1 := by
  rw [rU8, fu_one, ← zpow_one (stdGen F), dlog8_zpow h3, Int.cast_one]

@[expose] def rUnit8 (h3 : twoVal F = 3) : (F ≃+* F) →* (ZMod 8)ˣ where
  toFun σ := ⟨rU8 σ, rU8 σ⁻¹, by rw [← rU8_mul h3, mul_inv_cancel, rU8_one h3],
    by rw [← rU8_mul h3, inv_mul_cancel, rU8_one h3]⟩
  map_one' := Units.ext (rU8_one h3)
  map_mul' σ τ := Units.ext (rU8_mul h3 σ τ)

theorem coe_rUnit8 (h3 : twoVal F = 3) (σ : F ≃+* F) : (rUnit8 h3 σ : ZMod 8) = rU8 σ := rfl

theorem not_fix_or_inv_stdGen {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    {σ : F ≃+* F} (hσ : σ ∈ galTwo F) (hσ1 : σ ≠ 1) :
    ¬ (fu F σ (stdGen F) = stdGen F ∨ fu F σ (stdGen F) = (stdGen F)⁻¹) := by
  intro hfix
  obtain ⟨i, hi⟩ := orderOf_eq_two_pow_of_mem_galTwo hσ
  have hi1 : 1 ≤ i := by
    by_contra h
    apply hσ1
    rw [← orderOf_eq_one_iff, hi, show i = 0 by omega, pow_zero]
  have hdvd := two_pow_add_dvd_of_fix_or_inv hp hp2 hF σ hi1 hi (stdGen F) orderOf_stdGen hfix
  exact not_two_pow_twoVal_succ_dvd F Finite.one_lt_card
    ((Nat.pow_dvd_pow 2 (by omega)).trans hdvd)

theorem rU8_ne_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (h3 : twoVal F = 3) {σ : F ≃+* F} (hσ : σ ∈ galTwo F) (hσ1 : σ ≠ 1) : rU8 σ ≠ 1 := by
  intro h
  apply not_fix_or_inv_stdGen hp hp2 hF hσ hσ1
  left
  rw [← zpow_dlog8 h3 (fu_mem_zpowers_stdGen σ (mem_zpowers _))]
  change stdGen F ^ ((rU8 σ).val : ℤ) = stdGen F
  rw [h, show ((1 : ZMod 8).val : ℤ) = 1 from rfl, zpow_one]

theorem rU8_ne_neg_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (h3 : twoVal F = 3) {σ : F ≃+* F} (hσ : σ ∈ galTwo F) (hσ1 : σ ≠ 1) : rU8 σ ≠ -1 := by
  intro h
  apply not_fix_or_inv_stdGen hp hp2 hF hσ hσ1
  right
  rw [← zpow_dlog8 h3 (fu_mem_zpowers_stdGen σ (mem_zpowers _))]
  change stdGen F ^ ((rU8 σ).val : ℤ) = (stdGen F)⁻¹
  rw [h, show ((-1 : ZMod 8).val : ℤ) = 7 from rfl, ← zpow_neg_one, zpow_eq_zpow_iff_modEq,
    orderOf_stdGen_eq_eight h3]
  decide

open Classical in
@[expose] def nmA (x : PGammaL2 F) : Fˣ :=
  if h : ∃ a ε, x.left = tor F a * swp F ε then h.choose else 1

open Classical in
@[expose] def nmE (x : PGammaL2 F) : Bool :=
  if h : ∃ a ε, x.left = tor F a * swp F ε then h.choose_spec.choose else false

omit [Finite F] in
theorem nmA_nmE_nm (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nmA (nm F a ε σ) = a ∧ nmE (nm F a ε σ) = ε := by
  have h : ∃ a' ε', (nm F a ε σ).left = tor F a' * swp F ε' := ⟨a, ε, rfl⟩
  rw [nmA, nmE, dite_eq_left h, dite_eq_left h]
  have h' : tor F a * swp F ε = tor F h.choose * swp F h.choose_spec.choose :=
    h.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := tor_mul_swp_injective h'
  exact ⟨h1.symm, h2.symm⟩

@[expose] def sgn8 : Bool → (ZMod 8)ˣ
  | false => 1
  | true => -1

theorem sgn8_xor : ∀ ε ε' : Bool, sgn8 (xor ε ε') = sgn8 ε * sgn8 ε' := by decide

theorem dlog8_twist (h3 : twoVal F = 3) (ε : Bool) {a : Fˣ} (ha : a ∈ zpowers (stdGen F)) :
    dlog8 (twist F ε a) = (sgn8 ε : ZMod 8) * dlog8 a := by
  cases ε
  · simp [sgn8]
  · simp [sgn8, dlog8_inv h3 ha]

@[expose] def jfun8 (h3 : twoVal F = 3) (x : PGammaL2 F) : Perm (ZMod 8) :=
  aff8 (sgn8 (nmE x) * rUnit8 h3 x.right) (dlog8 (nmA x))

theorem jfun8_nm (h3 : twoVal F = 3) (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    jfun8 h3 (nm F a ε σ) = aff8 (sgn8 ε * rUnit8 h3 σ) (dlog8 a) := by
  rw [jfun8, (nmA_nmE_nm a ε σ).1, (nmA_nmE_nm a ε σ).2, nm_right]

@[expose] def j8 (h3 : twoVal F = 3) : sylS0 F →* Perm (ZMod 8) where
  toFun x := jfun8 h3 x
  map_one' := by
    change jfun8 h3 1 = 1
    rw [← nm_one, jfun8_nm, map_one, mul_one, dlog8_one h3]
    exact aff8_one
  map_mul' x y := by
    obtain ⟨a, ha, ε, σ, -, hx⟩ := x.2
    obtain ⟨b, hb, ε', τ, -, hy⟩ := y.2
    change jfun8 h3 ((x : PGammaL2 F) * y) = jfun8 h3 x * jfun8 h3 y
    rw [hx, hy, nm_mul, jfun8_nm, jfun8_nm, jfun8_nm, aff8_mul, sgn8_xor, map_mul,
      dlog8_mul h3 ha (twist_mem (fu_mem_zpowers_stdGen σ hb) ε),
      dlog8_twist h3 ε (fu_mem_zpowers_stdGen σ hb), dlog8_fu h3 σ hb]
    congr 1
    · rw [mul_mul_mul_comm]
    · rw [Units.val_mul, coe_rUnit8, mul_assoc]

theorem j8_apply (h3 : twoVal F = 3) (x : sylS0 F) : j8 h3 x = jfun8 h3 x := rfl

theorem j8_mem_H8 (h3 : twoVal F = 3) (x : sylS0 F) : j8 h3 x ∈ H8 :=
  aff8_mem_H8 _ _

private theorem units8_eq_pm_one_of : ∀ (ε : Bool) (r : (ZMod 8)ˣ), sgn8 ε * r = 1 →
    r = 1 ∨ r = -1 := by decide

private theorem sgn8_eq_one_iff : ∀ ε : Bool, sgn8 ε = 1 → ε = false := by decide

theorem j8_injective {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (h3 : twoVal F = 3) : Function.Injective (j8 h3) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, j8_apply] at hx
  obtain ⟨a, ha, ε, σ, hσ, hxe⟩ := x.2
  rw [hxe, jfun8_nm, ← aff8_one] at hx
  obtain ⟨h1, h2⟩ := aff8_injective hx
  have hσ1 : σ = 1 := by
    by_contra hne
    rcases units8_eq_pm_one_of ε _ h1 with h | h
    · exact rU8_ne_one hp hp2 hF h3 hσ hne (by rw [← coe_rUnit8 h3, h, Units.val_one])
    · exact rU8_ne_neg_one hp hp2 hF h3 hσ hne (by
        rw [← coe_rUnit8 h3, h, Units.val_neg, Units.val_one])
  subst hσ1
  rw [map_one, mul_one] at h1
  have hε := sgn8_eq_one_iff ε h1
  have ha1 := eq_one_of_dlog8_eq_zero h3 ha h2
  rw [mem_bot]
  apply Subtype.ext
  rw [hxe, hε, ha1, nm_one]
  rfl

theorem j8_mem_R8 (h3 : twoVal F = 3) {c : Fˣ} (hc : c ∈ zpowers (stdGen F ^ 2)) (ε : Bool)
    (hx : nm F c ε 1 ∈ sylS0 F) : j8 h3 ⟨nm F c ε 1, hx⟩ ∈ R8 := by
  obtain ⟨k, rfl⟩ := hc
  rw [j8_apply, jfun8_nm, map_one, mul_one]
  simp only
  rw [← zpow_natCast, ← zpow_mul, dlog8_zpow h3, Int.cast_mul, Int.cast_natCast, Nat.cast_ofNat]
  refine ⟨sgn8 ε, k, ?_, rfl⟩
  cases ε
  · exact Or.inl rfl
  · exact Or.inr rfl

@[expose] def fbitΓ (h3 : twoVal F = 3) : PGammaL2 F →* Multiplicative (ZMod 2) :=
  fbitU8.comp ((rUnit8 h3).comp SemidirectProduct.rightHom)

theorem stdGen_not_isSquare (hodd : IsOddPrimePower (Nat.card F)) :
    ¬ IsSquare ((stdGen F : Fˣ) : F) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact (stdGen F).ne_zero hr
  set u := Units.mk0 r hr0
  have hu : u ^ 2 = stdGen F := by
    ext
    simp [u, pow_two, hr]
  have h1 : u ^ 2 ^ (twoVal F + 1) = 1 := by
    rw [pow_succ', pow_mul, hu, pow_two_pow_twoVal_eq_one (mem_zpowers _)]
  obtain ⟨i, hi, hui⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  have hin : i ≤ twoVal F := by
    have : 2 ^ i ∣ Nat.card F - 1 := by
      rw [← hui, ← Nat.card_units]
      exact orderOf_dvd_natCard u
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp this
  have h2 : u ^ 2 ^ twoVal F = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hui]; exact Nat.pow_dvd_pow 2 hin)
  have h1v := one_le_twoVal hodd
  have h3 : stdGen F ^ 2 ^ (twoVal F - 1) = 1 := by
    rw [← hu, ← pow_mul, ← pow_succ', Nat.sub_add_cancel h1v, h2]
  have := orderOf_dvd_of_pow_eq_one h3
  rw [orderOf_stdGen] at this
  have := Nat.le_of_dvd (by positivity) this
  have : 2 ^ (twoVal F - 1) < 2 ^ twoVal F := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem isSquare_stdGen_pow_iff (hodd : IsOddPrimePower (Nat.card F)) (k : ℕ) :
    IsSquare ((stdGen F ^ k : Fˣ) : F) ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Units.val_mul, isSquare_mul_iff (Units.ne_zero _) (Units.ne_zero _), ih,
      Nat.even_add_one]
    have := stdGen_not_isSquare hodd
    tauto

theorem isSquare_iff_dbit8 (hodd : IsOddPrimePower (Nat.card F)) (h3 : twoVal F = 3) {a : Fˣ}
    (ha : a ∈ zpowers (stdGen F)) : IsSquare (a : F) ↔ dbit8 (dlog8 a) = 0 := by
  have hk := zpow_dlog8 h3 ha
  rw [zpow_natCast] at hk
  rw [dbit8, ZMod.natCast_eq_zero_iff_even, ← isSquare_stdGen_pow_iff hodd, hk]

theorem deltaPGL_eq_chiPGL (hodd : IsOddPrimePower (Nat.card F)) (x : PGammaL2 F) :
    deltaPGL hodd x = chiPGL hodd x.left := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, deltaPGL_inl]
  simp [deltaPGL]

theorem pairHom_j8 (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (h3 : twoVal F = 3) (x : sylS0 F) :
    pairHom (deltaPGL hodd) (fbitΓ h3) x = typeP (j8 h3 x) := by
  obtain ⟨a, ha, ε, σ, -, hx⟩ := x.2
  rw [j8_apply, hx, jfun8_nm, typeP_aff8, pairHom_apply]
  congr 2
  · rw [deltaPGL_eq_chiPGL, nm_left, map_mul]
    have hsw : chiPGL hodd (swp F ε) = 1 := by
      rw [chiPGL_eq_one_iff]
      cases ε
      · exact one_mem _
      · exact sw_mem_range hsq
    have htor : chiPGL hodd (tor F a) = Multiplicative.ofAdd (dbit8 (dlog8 a)) := by
      apply zmod2_eq_of_iff
      rw [chiPGL_eq_one_iff, tor_mem_range_iff, isSquare_iff_dbit8 hodd h3 ha, ofAdd_eq_one]
    rw [hsw, mul_one, htor, toAdd_ofAdd]
  · change fbit8 (rUnit8 h3 σ : ZMod 8) = _
    cases ε
    · rw [show sgn8 false = 1 from rfl, one_mul]
    · rw [show sgn8 true = -1 from rfl, neg_one_mul, fbit8_neg_mul]

theorem le_sylS0_of (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (hn : 3 ≤ twoVal F) {Q : Subgroup (PGammaL2 F)}
    (hQ : IsPGroup 2 Q) (hRQ : rStd F ≤ Q) : Q ≤ sylS0 F := by
  intro x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₀ := stdSylow F hodd hsq hq4
  have hS₀ : (S₀ : Subgroup (PSL2 F)) = stdT F := coe_stdSylow hodd hsq hq4
  have hnorm := conj_mem_of_mem S₀ Q hQ (by rw [hS₀]; exact hRQ) hx
  rw [hS₀] at hnorm
  obtain ⟨b, ε, hxb⟩ := exists_nm_of_normalizes_stdT hodd hsq hn x hnorm
  have hσ : x.right ∈ galTwo F := by
    obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have h1 : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [← right_pow, h1]
    rfl
  have h1 := hnorm _ (nm_mem_rStd hsq (one_mem _) true)
  rw [hxb, nm_conj_refl, map_one, twist_one, mul_one] at h1
  obtain ⟨y, hy, ε', hyeq⟩ := (mem_map_stdT_iff hsq _).mp h1
  have hbb : b * b = y := (nm_injective hyeq).1
  have hb : b ∈ zpowers (stdGen F) := by
    apply mem_zpowers_of_orderOf_dvd
    rw [orderOf_stdGen]
    apply orderOf_dvd_of_pow_eq_one
    have := (pow_half_eq_one_iff hodd).mpr (hbb ▸ hy)
    rw [← pow_two, ← pow_mul, ← pow_succ', Nat.sub_add_cancel (one_le_twoVal hodd)] at this
    exact this
  rw [hxb]
  exact nm_mem_sylS0 hb ε hσ

end CFSG.ComponentClassification.HSFLit.L2Act
