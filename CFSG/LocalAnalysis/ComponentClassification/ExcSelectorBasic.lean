module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorQuaternion
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.RestrictedStd CFSG.LieType.Chevalley

@[expose] def SmallType (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ LieModel (X ⧸ center X) .PSL 2 p f ∧
      Odd (Nat.card (center X))) ∨
    (Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7)) ∧ Odd (Nat.card (center X))) ∨
    LieModel (X ⧸ center X) .PSL 3 2 2

theorem smallSource_iff {A : Type} [Group A] (L : Subgroup A) : SmallSource L ↔ SmallType L :=
  Iff.rfl

theorem statedClassicalModel_of_lieModel_psl {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSL n p f) : StatedClassicalModel X .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem lieModel_psl_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n p f : ℕ}
    (h : LieModel X .PSL n p f) : LieModel Y .PSL n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

@[expose] def centralQuotientCongr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ center X ≃* Y ⧸ center Y :=
  QuotientGroup.congr (center X) (center Y) e (Subgroup.map_center_eq e)

theorem smallType_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : SmallType X) :
    SmallType Y := by
  have hZ : Nat.card (center X) = Nat.card (center Y) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rcases h with ⟨p, f, hp, hp2, hf, h5, hm, hodd⟩ | ⟨⟨e7⟩, hodd⟩ | h34
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, lieModel_psl_of_equiv (centralQuotientCongr e) hm,
      hZ ▸ hodd⟩
  · exact Or.inr (Or.inl ⟨⟨(centralQuotientCongr e).symm.trans e7⟩, hZ ▸ hodd⟩)
  · exact Or.inr (Or.inr (lieModel_psl_of_equiv (centralQuotientCongr e) h34))

theorem smallType_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    SmallType X ↔ SmallType Y :=
  ⟨smallType_of_equiv e, smallType_of_equiv e.symm⟩

theorem not_injective_quaternion_perm_seven (q : QuaternionGroup 2 →* Equiv.Perm (Fin 7)) :
    ¬ Function.Injective q := by
  intro hq
  have hz : q (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    have h1 : QuaternionGroup.a (2 : ZMod (2 * 2)) = 1 := hq (h.trans (map_one q).symm)
    exact absurd h1 (by decide)
  obtain ⟨x, hx⟩ : ∃ x, q (QuaternionGroup.a 2) x ≠ x := by
    by_contra hall
    push Not at hall
    exact hz (Equiv.ext hall)
  have hinj : Function.Injective (fun g : QuaternionGroup 2 => q g x) := by
    intro g h hgh
    by_contra hne
    have hy : h⁻¹ * g ≠ 1 := fun h1 => hne (by
      calc g = h * (h⁻¹ * g) := by group
        _ = h := by rw [h1, mul_one])
    obtain ⟨k, hk⟩ := OddSelector.quaternion_central_mem_zpowers hy
    have hfix : q (h⁻¹ * g) x = x := by
      have hgh' : q g x = q h x := hgh
      rw [map_mul, Equiv.Perm.mul_apply, hgh', map_inv]
      exact (q h).symm_apply_apply x
    apply hx
    rw [← hk, map_zpow]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix k
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [QuaternionGroup.card, Fintype.card_fin] at hcard
  omega

theorem not_injective_quaternion_alternating_seven
    (q : QuaternionGroup 2 →* alternatingGroup (Fin 7)) : ¬ Function.Injective q :=
  fun hq => not_injective_quaternion_perm_seven ((alternatingGroup (Fin 7)).subtype.comp q)
    (Subtype.val_injective.comp hq)

section SL2

variable {F : Type} [Field F]

theorem exists_sq_add_sq_eq_neg_one [Finite F] : ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hchar⟩ := CharP.exists F
  obtain ⟨-, hp, -⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  refine ⟨ZMod.castHom (dvd_refl p) F a, ZMod.castHom (dvd_refl p) F b, ?_⟩
  rw [← map_pow, ← map_pow, ← map_add, hab]
  exact ((ZMod.castHom (dvd_refl p) F).map_neg 1).trans (by rw [RingHom.map_one])

theorem uSL_one_mul_vSL_one_ne : uSL (1 : F) * vSL 1 ≠ vSL 1 * uSL 1 := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F)) h)
    0) 0
  simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem uSL_pow (c : F) (n : ℕ) : uSL c ^ n = uSL ((n : F) * c) := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uSL]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem neg_one_mul_comm (g : SL2 F) : (-1 : SL2 F) * g = g * -1 := by
  ext i j
  simp

theorem neg_one_ne_one_sl2 (hF : ringChar F ≠ 2) : (-1 : SL2 F) ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F)) h) 0) 0
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at this
  exact Ring.neg_one_ne_one_of_char_ne_two hF this

variable {X : Type} [Group X]

theorem not_smallType_of_sl2 [Finite F] (hF : ringChar F ≠ 2) (φ : SL2 F →* X)
    (hφ : Function.Injective φ) (hz : φ (-1) ∉ center X) : ¬ SmallType X := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set π := QuotientGroup.mk' (center X) with hπ
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one (F := F)
  set Q := π.comp (φ.comp (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab))
  have hQa : LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab
      (QuaternionGroup.a 2) = -1 :=
    Subtype.ext (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom_a_two hab)
  have hzc : π (φ (-1)) ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hz
  have hQ : Function.Injective Q := by
    refine OddSelector.injective_of_quaternion Q ?_
    simp only [Q, MonoidHom.comp_apply, hQa]
    exact hzc
  set p := ringChar F with hp_def
  have hpF : CharP F p := ringChar.charP F
  have hpprime : p.Prime := by
    obtain ⟨n, hn, -⟩ := FiniteField.card F p
    exact hn
  have hz2 : orderOf (π (φ (-1))) = 2 := by
    refine orderOf_eq_prime ?_ hzc
    rw [sq, ← map_mul, ← map_mul, neg_mul_neg, one_mul, map_one, map_one]
  have hxc : π (φ (uSL 1)) ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, mem_center_iff]
    intro hmem
    apply uSL_one_mul_vSL_one_ne (F := F)
    apply hφ
    rw [map_mul, map_mul]
    exact (hmem (φ (vSL 1))).symm
  have : Fact p.Prime := ⟨hpprime⟩
  have hxp : orderOf (π (φ (uSL 1))) = p := by
    refine orderOf_eq_prime ?_ hxc
    rw [← map_pow, ← map_pow, uSL_pow, CharP.cast_eq_zero, zero_mul]
    have h0 : uSL (0 : F) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_uSL]
    rw [h0, map_one, map_one]
  have hcomm : π (φ (uSL 1)) * π (φ (-1)) = π (φ (-1)) * π (φ (uSL 1)) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← neg_one_mul_comm]
  rintro (⟨p', f, -, hp2, -, -, hm, -⟩ | ⟨⟨e7⟩, -⟩ | h34)
  · exact OddSelector.not_psl_two_odd_of_quaternion Q hQ hp2
      (statedClassicalModel_of_lieModel_psl hm)
  · exact not_injective_quaternion_alternating_seven (e7.toMonoidHom.comp Q)
      (e7.injective.comp hQ)
  · obtain ⟨-, hcent, -⟩ := PSL3Four.excludes_alternating_models_stated.{0} _
      (statedClassicalModel_of_lieModel_psl h34)
    have h64 := hcent _ hz2
    have hmem : π (φ (uSL 1)) ∈ centralizer ({π (φ (-1))} : Set (X ⧸ center X)) :=
      mem_centralizer_singleton_iff.mpr hcomm
    have hdvd : p ∣ 64 := by
      rw [← h64, ← hxp, ← Subgroup.orderOf_mk _ hmem]
      exact orderOf_dvd_natCard _
    have h2 : p ∣ 2 := hpprime.dvd_of_dvd_pow (show p ∣ 2 ^ 6 by norm_num; exact hdvd)
    exact hF ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).1 h2)

theorem mul_sq_sub_one_ne_40320 (q : ℕ) : q * (q ^ 2 - 1) ≠ 40320 := by
  rcases Nat.lt_or_ge q 35 with h | h
  · interval_cases q <;> norm_num
  · have h1 : 1224 ≤ q ^ 2 - 1 := by
      have : 35 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h 2
      omega
    have h2 : 35 * 1224 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h h1
    omega

theorem two_mul_card_centralQuotient_of_equiv_sl2 [Finite F] (hF : ringChar F ≠ 2)
    (e : X ≃* SL2 F) :
    2 * Nat.card (X ⧸ center X) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have : Fintype F := Fintype.ofFinite F
  have hodd : Odd (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
  have hg : Nat.gcd 2 (Nat.card F - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have h := UnbalancingLocal.card_psl_two_mul_gcd F
  rw [hg] at h
  rw [← h, mul_comm,
    Nat.card_congr ((centralQuotientCongr e).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 F)).toEquiv]

theorem not_smallType_of_equiv_sl2 [Finite F] (hF : ringChar F ≠ 2) (e : X ≃* SL2 F) :
    ¬ SmallType X := by
  have hzmem : e.symm (-1) ∈ center X := by
    rw [mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, neg_one_mul_comm]
  have hz2 : orderOf (⟨e.symm (-1), hzmem⟩ : center X) = 2 := by
    rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ (neg_one_ne_one_sl2 hF)
    rw [sq, neg_mul_neg, one_mul]
  have heven : ¬ Odd (Nat.card (center X)) := by
    intro hodd
    have h2 : 2 ∣ Nat.card (center X) := hz2 ▸ orderOf_dvd_natCard _
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rintro (⟨-, -, -, -, -, -, -, hodd⟩ | ⟨-, hodd⟩ | h34)
  · exact heven hodd
  · exact heven hodd
  · obtain ⟨hcard, -, -⟩ := PSL3Four.excludes_alternating_models_stated.{0} _
      (statedClassicalModel_of_lieModel_psl h34)
    have h := two_mul_card_centralQuotient_of_equiv_sl2 hF e
    rw [hcard] at h
    exact mul_sq_sub_one_ne_40320 _ h.symm

end SL2

section Orders

theorem two_mul_ne_of_two_adic {n N m : ℕ} (hN : 1 ≤ N) (hm : Odd m) (hn : n = 2 ^ N * m)
    (hlt : n < (2 ^ N - 1) * (2 ^ N - 2) * 2 ^ (N - 1)) {r : ℕ} (hr : Odd r) :
    2 * n ≠ r * (r ^ 2 - 1) := by
  intro h
  obtain ⟨s, rfl⟩ := hr
  have hsq : (2 * s + 1) ^ 2 - 1 = 4 * (s * (s + 1)) := by
    rw [show (2 * s + 1) ^ 2 = 4 * (s * (s + 1)) + 1 by ring]
    omega
  rw [hsq, hn] at h
  have hN1 : 2 ^ N = 2 * 2 ^ (N - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h' : 2 ^ (N - 1) * m = (2 * s + 1) * (s * (s + 1)) := by
    rw [hN1] at h
    have : 4 * (2 ^ (N - 1) * m) = 4 * ((2 * s + 1) * (s * (s + 1))) := by
      calc 4 * (2 ^ (N - 1) * m) = 2 * (2 * 2 ^ (N - 1) * m) := by ring
        _ = (2 * s + 1) * (4 * (s * (s + 1))) := h
        _ = 4 * ((2 * s + 1) * (s * (s + 1))) := by ring
    omega
  have hcop : ∀ x : ℕ, Odd x → Nat.Coprime (2 ^ (N - 1)) x := fun x hx =>
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hx)
  have hdvd : 2 ^ (N - 1) ∣ s * (s + 1) :=
    (hcop _ (odd_two_mul_add_one s)).dvd_of_dvd_mul_left ⟨m, by rw [← h']⟩
  have hpos : 0 < m := hm.pos
  have hs : 2 ^ (N - 1) ≤ s + 1 := by
    rcases Nat.even_or_odd s with hse | hso
    · have h1 : 2 ^ (N - 1) ∣ s :=
        (hcop _ (Even.add_one hse)).dvd_of_dvd_mul_right hdvd
      have hs0 : s ≠ 0 := by
        rintro rfl
        have hA : 0 < 2 ^ (N - 1) * m := Nat.mul_pos (Nat.two_pow_pos _) hpos
        rw [h'] at hA
        simp at hA
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) h1).trans (Nat.le_succ s)
    · have h1 : 2 ^ (N - 1) ∣ s + 1 := (hcop _ hso).dvd_of_dvd_mul_left hdvd
      exact Nat.le_of_dvd (Nat.succ_pos s) h1
  have hA : 2 ^ N - 1 ≤ 2 * s + 1 := by omega
  have hB : (2 ^ N - 2) * 2 ^ N ≤ 4 * (s * (s + 1)) := by
    have : 2 ^ N - 2 ≤ 2 * s := by omega
    calc (2 ^ N - 2) * 2 ^ N ≤ (2 * s) * (2 * s + 2) := Nat.mul_le_mul this (by omega)
      _ = 4 * (s * (s + 1)) := by ring
  have hC : (2 ^ N - 1) * ((2 ^ N - 2) * 2 ^ N) ≤ (2 * s + 1) * (4 * (s * (s + 1))) :=
    Nat.mul_le_mul hA hB
  have e1 : (2 ^ N - 1) * ((2 ^ N - 2) * 2 ^ N) =
      2 * ((2 ^ N - 1) * (2 ^ N - 2) * 2 ^ (N - 1)) := by
    generalize 2 ^ N - 1 = A
    generalize 2 ^ N - 2 = B
    rw [hN1]
    ring
  have hD : 2 * (2 ^ N * m) < (2 ^ N - 1) * ((2 ^ N - 2) * 2 ^ N) := by
    rw [e1, ← hn]
    omega
  omega

theorem pow_le_two_adic_bound {N : ℕ} (hN : 2 ≤ N) :
    2 ^ (3 * N - 3) ≤ (2 ^ N - 1) * (2 ^ N - 2) * 2 ^ (N - 1) := by
  have h1 : 2 ^ (N - 1) ≤ 2 ^ N - 1 := by
    have : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
    have : 1 ≤ 2 ^ (N - 1) := Nat.one_le_two_pow
    omega
  have h2 : 2 ^ (N - 1) ≤ 2 ^ N - 2 := by
    have : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
    have : 2 ≤ 2 ^ (N - 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (N - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 2 ^ (3 * N - 3) = 2 ^ (N - 1) * 2 ^ (N - 1) * 2 ^ (N - 1) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ (2 ^ N - 1) * (2 ^ N - 2) * 2 ^ (N - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) le_rfl

variable {X : Type} [Group X]

theorem card_centralQuotient_of_center_eq_bot (hZ : center X = ⊥) :
    Nat.card (X ⧸ center X) = Nat.card X := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hZ, Subgroup.card_bot,
    mul_one]

theorem not_smallType_of_card (hZ : center X = ⊥)
    (hn : ∀ r : ℕ, Odd r → 2 * Nat.card X ≠ r * (r ^ 2 - 1)) (h7 : Nat.card X ≠ 2520)
    (h34 : Nat.card X ≠ 20160) : ¬ SmallType X := by
  have hc := card_centralQuotient_of_center_eq_bot hZ
  rintro (⟨p, f, hp, hp2, hf, -, hm, -⟩ | ⟨⟨e7⟩, -⟩ | h34')
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psl hm
    have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
    have hg : Nat.gcd 2 (Nat.card K - 1) = 2 := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk, show 2 * k + 1 - 1 = 2 * k by omega]
      exact Nat.gcd_eq_left (dvd_mul_right 2 k)
    have h := UnbalancingLocal.card_psl_two_mul_gcd K
    rw [hg, ← Nat.card_congr e.toEquiv, hc, mul_comm] at h
    exact hn _ hodd h
  · apply h7
    rw [← hc, Nat.card_congr e7.toEquiv]
    exact UnbalancingLocal.card_alternating_seven
  · obtain ⟨hcard, -, -⟩ := PSL3Four.excludes_alternating_models_stated.{0} _
      (statedClassicalModel_of_lieModel_psl h34')
    exact h34 (hc ▸ hcard)

theorem not_smallType_of_elementary (hZ : center X = ⊥) (E : Subgroup X)
    [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) (h7 : Nat.card X ≠ 2520)
    (h34 : Nat.card X ≠ 20160) : ¬ SmallType X := by
  have hc := card_centralQuotient_of_center_eq_bot hZ
  rintro (⟨p, f, hp, hp2, hf, -, hm, -⟩ | ⟨⟨e7⟩, -⟩ | h34')
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psl hm
    have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
    let eZ : X ≃* X ⧸ center X := (QuotientGroup.quotientBot.symm).trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact (UnbalancingLocal.not_odd_psl_two_of_elementary E (by omega) hodd).false
      (eZ.trans e)
  · apply h7
    rw [← hc, Nat.card_congr e7.toEquiv]
    exact UnbalancingLocal.card_alternating_seven
  · obtain ⟨hcard, -, -⟩ := PSL3Four.excludes_alternating_models_stated.{0} _
      (statedClassicalModel_of_lieModel_psl h34')
    exact h34 (hc ▸ hcard)

end Orders

end CFSG.ComponentClassification.ExcSelector
