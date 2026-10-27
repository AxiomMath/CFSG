module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisT

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.Model

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem isSquare_iff_mem_sq (hodd : IsOddPrimePower (Nat.card F)) {b : Fˣ}
    (hb : b ∈ zpowers (stdGen F)) : IsSquare (b : F) ↔ b ∈ zpowers (stdGen F ^ 2) := by
  constructor
  · intro hsq
    by_contra hn
    have hneg := pow_half_eq_neg_one hodd hb hn
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_isOddPrimePower hodd
    have : Fintype F := Fintype.ofFinite F
    have hchar : ringChar F ≠ 2 := by
      intro h
      apply h2
      have := ringChar.spec F 2
      exact_mod_cast (CharP.cast_eq_zero_iff F (ringChar F) 2).mpr (by rw [h])
    rw [FiniteField.isSquare_iff hchar b.ne_zero] at hsq
    obtain ⟨m, hm⟩ := two_pow_twoVal_dvd F
    have hv := one_le_twoVal hodd
    have hmodd : Odd m := by
      by_contra hme
      obtain ⟨m', rfl⟩ := Nat.not_odd_iff_even.mp hme
      apply not_two_pow_twoVal_succ_dvd F Finite.one_lt_card
      exact ⟨m', by rw [hm, pow_succ]; ring⟩
    have hhalf : Fintype.card F / 2 = 2 ^ (twoVal F - 1) * m := by
      rw [← Nat.card_eq_fintype_card]
      obtain ⟨p', n', -, hpodd', -, hc'⟩ := hodd
      have hodd' : Odd (Nat.card F) := by rw [hc']; exact hpodd'.pow
      have h2v : 2 ^ twoVal F = 2 * 2 ^ (twoVal F - 1) := by
        rw [← pow_succ']; congr 1; omega
      obtain ⟨t, ht⟩ := hodd'
      have : Nat.card F - 1 = 2 * t := by omega
      rw [ht, show (2 * t + 1) / 2 = t by omega]
      rw [this, h2v, mul_assoc] at hm
      omega
    rw [hhalf, pow_mul] at hsq
    have : ((b ^ 2 ^ (twoVal F - 1) : Fˣ) : F) ^ m = 1 := by
      rw [Units.val_pow_eq_pow_val]; exact hsq
    rw [hneg, Units.val_neg, Units.val_one, hmodd.neg_one_pow] at this
    apply h2
    linear_combination -this
  · rintro ⟨j, rfl⟩
    refine ⟨((stdGen F ^ j : Fˣ) : F), ?_⟩
    simp only [← zpow_natCast, ← zpow_mul, Units.val_zpow_eq_zpow_val]
    rw [← zpow_add₀ (Units.ne_zero _)]
    congr 1
    push_cast
    ring

theorem std_right_sq {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hn : 2 ≤ twoVal F)
    (x : PGammaL2 F) {k : ℕ} (hk : x.right ^ 2 ^ k = 1)
    (hx : ∀ d ∈ rStd F, x * d = d * x) : x.right ^ 2 = 1 :=
  fieldProj_sq_of_commute_tor hp hp2 hF x (orderOf_stdGen_sq hodd) hn
    (by rw [inl_tor]; exact hx _ (nm_mem_rStd hsq (mem_zpowers _) false)) hk

@[expose] def eps0 (σ₀ : F ≃+* F) : Bool := by
  classical
  exact if fu F σ₀ (stdGen F ^ 2) = stdGen F ^ 2 then false else true

@[expose] def k0 (σ₀ : F ≃+* F) : PGammaL2 F := nm F 1 (eps0 σ₀) σ₀

theorem k0_right (σ₀ : F ≃+* F) : (k0 σ₀).right = σ₀ := rfl

theorem k0_mul_self {σ₀ : F ≃+* F} (hσ₀ : orderOf σ₀ = 2) : k0 σ₀ * k0 σ₀ = 1 := by
  rw [k0, nm_mul, Bool.xor_self, map_one, show σ₀ * σ₀ = 1 by
    rw [← pow_two, ← hσ₀, pow_orderOf_eq_one]]
  simp [nm_one]

theorem k0_sqLeft (hsq : IsSquare (-1 : F)) (σ₀ : F ≃+* F) : SqLeft (k0 σ₀) := by
  change tor F 1 * swp F (eps0 σ₀) ∈ _
  rw [map_one, one_mul]
  cases eps0 σ₀
  · exact one_mem _
  · exact sw_mem_range hsq

theorem twist_eps0 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) {σ₀ : F ≃+* F} (hσ₀ : orderOf σ₀ = 2) {y : Fˣ}
    (hy : y ∈ zpowers (stdGen F ^ 2)) : twist F (eps0 σ₀) (fu F σ₀ y) = y := by
  obtain ⟨j, rfl⟩ := hy
  have hfi := fix_or_inv_of_order_two hp hp2 hF σ₀ (by rw [hσ₀, pow_one]) (stdGen F ^ 2)
    (orderOf_stdGen_sq hodd) (one_le_twoVal hodd)
  rw [map_zpow]
  by_cases h : fu F σ₀ (stdGen F ^ 2) = stdGen F ^ 2
  · have he : eps0 σ₀ = false := by
      classical
      simp only [eps0, h, ite_true]
    rw [he, twist_false, h]
  · have he : eps0 σ₀ = true := by
      classical
      simp only [eps0, h, ite_false]
    rw [he, twist_true, hfi.resolve_left h, inv_zpow, inv_inv]

theorem k0_commute {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) {σ₀ : F ≃+* F}
    (hσ₀ : orderOf σ₀ = 2) {d : PGammaL2 F} (hd : d ∈ rStd F) : k0 σ₀ * d = d * k0 σ₀ := by
  obtain ⟨y, hy, ε, rfl⟩ := (mem_map_stdT_iff hsq d).mp hd
  rw [k0, nm_mul, nm_mul, twist_eps0 hp hp2 hF hodd hσ₀ hy, one_mul, map_one, mul_one,
    one_mul, Bool.xor_comm]
  cases ε <;> simp

theorem std_normalizer (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hn : 3 ≤ twoVal F) {y : PGammaL2 F} (hyL : y ∈ pGammaL2PSLRange F)
    (hyN : ∀ d ∈ rStd F, y * d * y⁻¹ ∈ rStd F) : y ∈ rStd F := by
  obtain ⟨hy1, hySq⟩ := (mem_pslRange_iff y).mp hyL
  obtain ⟨b, ε, hy⟩ := exists_nm_of_normalizes_stdT hodd hsq hn y hyN
  rw [hy1] at hy
  subst hy
  have hbsq : IsSquare (b : F) := by
    have hleft : tor F b * swp F ε ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := hySq
    have hswp : swp F ε ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      cases ε
      · exact one_mem _
      · exact sw_mem_range hsq
    have htor := mul_mem hleft (inv_mem hswp)
    rw [mul_inv_cancel_right] at htor
    change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F b) ∈ _ at htor
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare] at htor
    convert htor using 1
    simp [pGammaL2FullSplitTorusGL]
  obtain ⟨c, hc, δ, hcδ⟩ :=
    (mem_map_stdT_iff hsq _).mp (hyN _ (nm_mem_rStd hsq (one_mem _) true))
  have hsw : nm F b ε 1 * nm F 1 true 1 = nm F c δ 1 * nm F b ε 1 := by rw [← hcδ]; group
  rw [nm_mul, nm_mul, nm_eq_nm_iff] at hsw
  obtain ⟨h1, h2, -⟩ := hsw
  have hδ : δ = true := by cases ε <;> cases δ <;> simp_all
  rw [hδ] at h1
  simp only [map_one, fu_one, twist_true] at h1
  have hb2 : b ^ 2 ∈ zpowers (stdGen F ^ 2) := by
    have hε1 : twist F ε 1 = 1 := by cases ε <;> simp
    rw [hε1, mul_one] at h1
    rw [show b ^ 2 = c by
      calc b ^ 2 = b * b := pow_two b
        _ = c * b⁻¹ * b := by nth_rw 1 [h1]
        _ = c := by group]
    exact hc
  have hbA : b ∈ zpowers (stdGen F) := by
    apply mem_zpowers_of_orderOf_dvd
    rw [orderOf_stdGen]
    apply orderOf_dvd_of_pow_eq_one
    have := (pow_half_eq_one_iff hodd).mpr hb2
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel (one_le_twoVal hodd)] at this
    exact this
  exact nm_mem_rStd hsq ((isSquare_iff_mem_sq hodd hbA).mp hbsq) _

end CFSG.ComponentClassification.HSDihedral.Model
