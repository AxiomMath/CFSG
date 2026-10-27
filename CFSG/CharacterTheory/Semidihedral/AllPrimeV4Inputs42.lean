module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Inputs
public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Frontier
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.Semidihedral.AllPrime

noncomputable section

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.AllPrime.QDTI
open CFSG.Wreathed.OriginalAllPrime.TIFacts CFSG.QuasiDihedralFusion
open Matrix CFSG.Semidihedral.MatrixCoverData
open scoped Pointwise commutatorElement

private theorem qd42_pow_gt {q₁ ℓ : ℕ} (hq₁ : 3 ≤ q₁) (hℓ : 3 ≤ ℓ) : ℓ * (q₁ + 1) + 1 < q₁ ^ ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  have h3 : ∀ m : ℕ, 2 * m + 1 ≤ 3 ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ]; omega
  have h3 := h3 k
  have hpow : 3 ^ k ≤ q₁ ^ k := Nat.pow_le_pow_left hq₁ k
  rw [pow_succ]
  nlinarith

private theorem qd42_torusSize_pow_mul {q₁ ℓ : ℕ} (hq₁ : Odd q₁) (hq₁3 : 3 ≤ q₁) (hℓodd : Odd ℓ) :
    ((torusSize (q₁ ^ ℓ) : ℕ) : ℤ) = (torusSize q₁ : ℤ) *
      ∑ i ∈ Finset.range ℓ, (if q₁ % 4 = 1 then -(q₁ : ℤ) else q₁) ^ i := by
  have hmod := CFSG.Semidihedral.FixedFieldData.odd_power_mod_eight hq₁ hℓodd
  have hmod4 : q₁ ^ ℓ % 4 = q₁ % 4 := by omega
  have hq4 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq₁)
  have hpow1 : 1 ≤ q₁ ^ ℓ := Nat.one_le_pow _ _ (by omega)
  rcases hq4 with h1 | h3
  · have hg := geom_sum_mul (-(q₁ : ℤ)) ℓ
    rw [hℓodd.neg_pow] at hg
    simp only [torusSize, h1, hmod4, ↓reduceIte]
    push_cast
    linear_combination hg
  · have h3' : ¬ q₁ % 4 = 1 := by omega
    have hg := geom_sum_mul (q₁ : ℤ) ℓ
    simp only [torusSize, h3', hmod4, ↓reduceIte]
    rw [Nat.cast_sub hpow1, Nat.cast_sub (by omega)]
    push_cast
    linear_combination -hg

private theorem qd42_not_sq_dvd_geom_sum {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (u : ℤ) :
    ¬ ((ℓ : ℤ) ^ 2 ∣ ∑ i ∈ Finset.range ℓ, u ^ i) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  intro h
  have hdvd : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range ℓ, u ^ i :=
    (dvd_pow_self (ℓ : ℤ) two_ne_zero).trans h
  have hu : (ℓ : ℤ) ∣ u - 1 := by
    have hg := geom_sum_mul u ℓ
    have h1 : (ℓ : ℤ) ∣ u ^ ℓ - 1 := hg ▸ dvd_mul_of_dvd_left hdvd _
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 ⊢
    push_cast at h1 ⊢
    rwa [ZMod.pow_card] at h1
  obtain ⟨t, ht⟩ := hu
  have hsq := odd_sq_dvd_geom_sum₂_sub (1 : ℤ) t hℓodd
  simp only [one_pow, mul_one] at hsq
  have hu' : u = 1 + (ℓ : ℤ) * t := by linear_combination ht
  rw [← hu'] at hsq
  have h2 : (ℓ : ℤ) ^ 2 ∣ (ℓ : ℤ) := by
    have := dvd_sub h hsq
    simpa using this
  have h3 : (ℓ : ℤ) ∣ 1 := by
    obtain ⟨c, hc⟩ := h2
    refine ⟨c, ?_⟩
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have : (ℓ : ℤ) * 1 = (ℓ : ℤ) * (ℓ * c) := by linear_combination hc
    exact mul_left_cancel₀ hℓ0 this
  have := Int.eq_one_of_dvd_one (by positivity) h3
  have : ℓ = 1 := by exact_mod_cast this
  exact hℓ.one_lt.ne' this

private theorem qd42_not_ordCompl_dvd_torusSize {q₁ ℓ : ℕ} (hq₁ : Odd q₁) (hq₁3 : 3 ≤ q₁)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ¬ (torusSize (q₁ ^ ℓ) / 2) / ℓ ^ (torusSize (q₁ ^ ℓ) / 2).factorization ℓ ∣
      torusSize q₁ := by
  intro hdvd
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hℓ3 : 3 ≤ ℓ := by have := hℓ.two_le; rcases hℓodd with ⟨k, hk⟩; omega
  have hTΦ := qd42_torusSize_pow_mul hq₁ hq₁3 hℓodd
  obtain ⟨u, hu⟩ : ∃ u : ℤ, u = if q₁ % 4 = 1 then -(q₁ : ℤ) else q₁ := ⟨_, rfl⟩
  rw [← hu] at hTΦ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℤ, Φ = ∑ i ∈ Finset.range ℓ, u ^ i := ⟨_, rfl⟩
  rw [← hΦ] at hTΦ
  obtain ⟨T, hT⟩ : ∃ T, T = torusSize (q₁ ^ ℓ) := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, T₁ = torusSize q₁ := ⟨_, rfl⟩
  rw [← hT, ← hT₁] at hTΦ
  rw [← hT, ← hT₁] at hdvd
  have hqodd : Odd (q₁ ^ ℓ) := hq₁.pow
  have hT2 : T = 2 * (T / 2) := hT ▸ torusSize_two_mul_half hqodd
  have hT₁2 : T₁ = 2 * (T₁ / 2) := hT₁ ▸ torusSize_two_mul_half hq₁
  have hMo : Odd (T / 2) := hT ▸ torusSize_half_odd hqodd
  have hT₁pos : 0 < T₁ := by
    have := torusSize_mod_four hq₁
    rw [← hT₁] at this
    omega
  have hTle : q₁ ^ ℓ - 1 ≤ T := by
    rw [hT, torusSize]
    split_ifs <;> omega
  have hT₁le : T₁ ≤ q₁ + 1 := by
    rw [hT₁, torusSize]
    split_ifs <;> omega
  have hT₁dvd : T₁ ∣ T := by
    have : (T₁ : ℤ) ∣ (T : ℤ) := ⟨Φ, hTΦ⟩
    exact_mod_cast this
  obtain ⟨Φn, hΦn⟩ := hT₁dvd
  have hΦeq : (Φn : ℤ) = Φ := by
    have h1 : (T₁ : ℤ) * Φn = (T₁ : ℤ) * Φ := by rw [← hTΦ, hΦn]; push_cast; ring
    exact mul_left_cancel₀ (by exact_mod_cast hT₁pos.ne') h1
  have hbig := qd42_pow_gt hq₁3 hℓ3
  have hΦgt : ℓ < Φn := by
    by_contra hle
    replace hle := not_lt.mp hle
    have h1 : T ≤ ℓ * (q₁ + 1) := by
      rw [hΦn, mul_comm ℓ]
      exact Nat.mul_le_mul hT₁le hle
    omega
  obtain ⟨M, hM⟩ : ∃ M, M = T / 2 := ⟨_, rfl⟩
  rw [← hM] at hT2 hMo hdvd
  obtain ⟨M', hM'⟩ : ∃ M', M' = M / ℓ ^ M.factorization ℓ := ⟨_, rfl⟩
  rw [← hM'] at hdvd
  have hM'odd : Odd M' := hM' ▸ hMo.of_dvd_nat (Nat.ordCompl_dvd M ℓ)
  have hM'1 : M' ∣ T₁ / 2 := by
    have h1 : M' ∣ 2 * (T₁ / 2) := hT₁2 ▸ hdvd
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hM'odd) h1
  obtain ⟨c, hc⟩ := hM'1
  have hMM : M = T₁ / 2 * Φn := by
    have h1 : 2 * M = 2 * (T₁ / 2) * Φn := by rw [← hT2, ← hT₁2, hΦn]
    rw [mul_assoc] at h1
    exact Nat.eq_of_mul_eq_mul_left two_pos h1
  have hord := Nat.ordProj_mul_ordCompl_eq_self M ℓ
  rw [← hM'] at hord
  have hM'0 : M' ≠ 0 := hM'odd.pos.ne'
  have hpow : ℓ ^ M.factorization ℓ = c * Φn := by
    have h1 : ℓ ^ M.factorization ℓ * M' = M' * c * Φn := by rw [hord, hMM, hc]
    have h2 : M' * ℓ ^ M.factorization ℓ = M' * (c * Φn) := by
      rw [mul_comm M', h1, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hM'0) h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).mp (Dvd.intro_left c hpow.symm)
  have hj2 : 2 ≤ j := by
    by_contra hj2
    have h1 : ℓ ^ j ≤ ℓ ^ 1 := Nat.pow_le_pow_right hℓ.pos (by omega)
    rw [← hj, pow_one] at h1
    omega
  have hsq : (ℓ : ℤ) ^ 2 ∣ Φ := by
    rw [← hΦeq, hj]
    exact_mod_cast pow_dvd_pow ℓ hj2
  exact qd42_not_sq_dvd_geom_sum hℓ hℓ2 u (hΦ ▸ hsq)

private theorem qd42_mem_fixedPoints_zpowers {F : Type} [Field F] {σ : F ≃+* F} {x : F}
    (hx : σ x = x) : x ∈ FixedPoints.subfield (Subgroup.zpowers σ) F := by
  intro τ
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (F ≃+* F) x :=
    Subgroup.zpowers_le.mpr hx
  exact hle τ.2

private theorem qd42_sl_map_subtype_injective {F : Type} [Field F] (K : Subfield F) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) K.subtype) := by
  intro X Y h
  apply Subtype.ext
  ext i j
  have := congrArg (fun Z : SL F => Z.1 i j) h
  exact this

private theorem qd42_exists_torus_moved {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (a : Fˣ) (ha : ¬IsSquare a) {σ : F ≃+* F} (hσa : σ (a : F) = a)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hσℓ : orderOf σ = ℓ) :
    ∃ w ∈ Torus F a, w ^ ((torusSize (Nat.card F) / 2) /
        ℓ ^ (torusSize (Nat.card F) / 2).factorization ℓ) = 1 ∧
      MatrixCover.slFieldEquiv F σ w ≠ w := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  obtain ⟨M', hM'⟩ : ∃ M', M' = (torusSize (Nat.card F) / 2) /
      ℓ ^ (torusSize (Nat.card F) / 2).factorization ℓ := ⟨_, rfl⟩
  rw [← hM'] at hcon
  set K : Subfield F := FixedPoints.subfield (Subgroup.zpowers σ) F with hKdef
  have hcardF : Nat.card F = Nat.card K ^ ℓ := by
    rw [CFSG.Semidihedral.FixedFieldData.nat_card_eq_fixedSubfield_card_pow F
      (Subgroup.zpowers σ), Nat.card_zpowers, hσℓ]
  have hoddK : Odd (Nat.card K) :=
    hodd.of_dvd_nat (hcardF ▸ dvd_pow_self _ hℓ.ne_zero)
  have h3K : 3 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rcases hoddK with ⟨k, hk⟩
    omega
  have haK : (a : F) ∈ K := qd42_mem_fixedPoints_zpowers hσa
  set aK : Kˣ := Units.mk0 ⟨(a : F), haK⟩ (by
    intro h
    exact a.ne_zero (congrArg Subtype.val h)) with haKdef
  have haKsq : ¬IsSquare aK := by
    rintro ⟨r, hr⟩
    apply ha
    refine ⟨Units.map (K.subtype : K →* F) r, Units.ext ?_⟩
    have h1 : ((aK : K) : F) = ((r : K) : F) * ((r : K) : F) := by
      have := congrArg (fun x : Kˣ => ((x : K) : F)) hr
      simpa using this
    exact h1
  set ι := Matrix.SpecialLinearGroup.map (n := Fin 2) K.subtype with hι
  have hιinj : Function.Injective ι := qd42_sl_map_subtype_injective K
  have hcardT : Nat.card ((Torus K aK).map ι) = torusSize (Nat.card K) := by
    rw [Subgroup.card_map_of_injective hιinj, torus_card K aK hoddK haKsq]
  have : IsCyclic (Torus F a) := torus_cyclic F a hodd ha
  set H : Subgroup (SL F) :=
    ((powMonoidHom M' : Torus F a →* Torus F a).ker).map (Torus F a).subtype with hHdef
  have hM'dvd : M' ∣ torusSize (Nat.card F) := by
    rw [hM']
    exact (Nat.ordCompl_dvd _ ℓ).trans (Nat.div_dvd_of_dvd
      ⟨_, torusSize_two_mul_half hodd⟩)
  have hcardH : Nat.card H = M' := by
    rw [hHdef, Subgroup.card_map_of_injective (Torus F a).subtype_injective,
      IsCyclic.card_powMonoidHom_ker, torus_card F a hodd ha]
    exact Nat.gcd_eq_right hM'dvd
  have hHT : H ≤ (Torus K aK).map ι := by
    rintro _ ⟨w, hw, rfl⟩
    have hw1 : (w : SL F) ^ M' = 1 := by
      have h1 : w ^ M' = 1 := hw
      have := congrArg (fun x : Torus F a => (x : SL F)) h1
      simpa using this
    have hfix := hcon w w.2 hw1
    have hentry : ∀ i j : Fin 2, σ ((w : SL F).1 i j) = (w : SL F).1 i j := by
      intro i j
      have := congrArg (fun Z : SL F => Z.1 i j) hfix
      exact this
    have hmem : ∀ i j : Fin 2, (w : SL F).1 i j ∈ K := fun i j =>
      qd42_mem_fixedPoints_zpowers (hentry i j)
    let X₀ : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => ⟨(w : SL F).1 i j, hmem i j⟩
    have hX₀ : K.subtype.mapMatrix X₀ = (w : SL F).1 := by
      ext i j
      rfl
    have hdet : X₀.det = 1 := by
      apply Subtype.ext
      have h1 := RingHom.map_det K.subtype X₀
      rw [hX₀, (w : SL F).2] at h1
      exact h1
    let X : SL K := ⟨X₀, hdet⟩
    have hιX : ι X = (w : SL F) := Subtype.ext hX₀
    obtain ⟨h01, h11⟩ := (mem_torus_iff F a (w : SL F)).mp w.2
    have hXT : X ∈ Torus K aK := by
      rw [mem_torus_iff]
      constructor
      · apply Subtype.ext
        change (w : SL F).1 0 1 = -(a : F) * (w : SL F).1 1 0
        exact h01
      · apply Subtype.ext
        change (w : SL F).1 1 1 = (w : SL F).1 0 0
        exact h11
    exact ⟨X, hXT, hιX⟩
  have hdvd := Subgroup.card_dvd_of_le hHT
  rw [hcardH, hcardT, hM', hcardF] at hdvd
  exact qd42_not_ordCompl_dvd_torusSize hoddK h3K hℓ hℓ2 hdvd

section Model

variable {F : Type} [Field F] {a : Fˣ} {A : Subgroup (F ≃+* F)}
  {hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a}

private def qd42_slFieldHom (F : Type) [Field F] : (F ≃+* F) →* MulAut (SL F) where
  toFun := MatrixCover.slFieldEquiv F
  map_one' := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    ext i j
    rfl
  map_mul' := MatrixCover.slFieldEquiv_mul F

private theorem qd42_c2_eq_one_of_odd {m : OriginalH F a A hfix} (hodd : Odd (orderOf m)) :
    m.left.right = 1 := by
  have hpow : (c2Hom m) ^ orderOf m = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases C2_cases (c2Hom m) with h | h
  · exact h
  · exfalso
    rw [h, ← ofAdd_nsmul] at hpow
    obtain ⟨k, hk⟩ := hodd
    rw [hk] at hpow
    revert hpow
    simp only [ofAdd_eq_one]
    rw [nsmul_eq_mul]
    push_cast
    rw [show (2 * (k : ZMod 2) + 1) * 1 = 1 by
      rw [show (2 : ZMod 2) = 0 from rfl]; ring]
    decide

private theorem qd42_actOn_torus {m : OriginalH F a A hfix} (hm : m ∈ cenU F a A hfix)
    (hc2 : m.left.right = 1) {w : SL F} (hw : w ∈ Torus F a) :
    actOn m w = MatrixCover.slFieldEquiv F m.right w := by
  have hX : m.left.left ∈ Torus F a := (mem_cenU_iff m).mp hm
  have hστ : MatrixCover.slFieldEquiv F m.right w ∈ Torus F a :=
    torus_field_invariant F a (m.right : F ≃+* F) (hfix m.right) ⟨w, hw⟩
  simp only [actOn, hc2, map_one, MulAut.one_apply]
  change m.left.left * MatrixCover.slFieldEquiv F m.right w * m.left.left⁻¹ = _
  rw [torus_mul_comm hX hστ, mul_inv_cancel_right]

private theorem qd42_slFieldHom_eq (σ : F ≃+* F) :
    qd42_slFieldHom F σ = MatrixCover.slFieldEquiv F σ := rfl

private theorem qd42_right_eq_one [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) (hA : Odd (Nat.card A)) {X : Subgroup (OriginalH F a A hfix)}
    (hXC : X ≤ cenU F a A hfix) (hXo : ∀ x ∈ X, Odd (orderOf x))
    (hWX : (Wsl a).map (originalSlInH F a A hfix) ≤ X) {y : OriginalH F a A hfix}
    (hyX : y ∈ X) (hyc : ∀ z ∈ ⁅X, X⁆, z * y = y * z) : y.right = 1 := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  by_contra hσ1
  have hσo : Odd (orderOf y.right) := hA.of_dvd_nat (orderOf_dvd_natCard y.right)
  have hσ1' : orderOf y.right ≠ 1 := fun h => hσ1 (orderOf_eq_one_iff.mp h)
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = (orderOf y.right).minFac := ⟨_, rfl⟩
  have hℓ : ℓ.Prime := hℓdef ▸ Nat.minFac_prime hσ1'
  have hℓσ : ℓ ∣ orderOf y.right := hℓdef ▸ Nat.minFac_dvd _
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hσo) (even_iff_two_dvd.mpr hℓσ)
  have hm0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  have hσm : orderOf y.right ∣ orderOf y := orderOf_map_dvd SemidirectProduct.rightHom y
  obtain ⟨b, hb⟩ : ∃ b, b = orderOf y / ℓ ^ (orderOf y).factorization ℓ := ⟨_, rfl⟩
  have hy'X : y ^ b ∈ X := X.pow_mem hyX b
  have hy'c : ∀ z ∈ ⁅X, X⁆, z * y ^ b = y ^ b * z := fun z hz =>
    ((Commute.pow_right (hyc z hz) b) : Commute z (y ^ b)).eq
  have hy'right : (y ^ b).right = y.right ^ b := map_pow SemidirectProduct.rightHom y b
  have hσ'1 : y.right ^ b ≠ 1 := by
    intro h
    have h1 : orderOf y.right ∣ b := orderOf_dvd_of_pow_eq_one h
    rw [hb] at h1
    exact Nat.not_dvd_ordCompl hℓ hm0 (hℓσ.trans h1)
  have hσ'pow : (y.right ^ b) ^ (ℓ ^ (orderOf y).factorization ℓ) = 1 := by
    rw [← pow_mul, mul_comm, hb, Nat.ordProj_mul_ordCompl_eq_self]
    exact orderOf_dvd_iff_pow_eq_one.mp hσm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).mp (orderOf_dvd_of_pow_eq_one hσ'pow)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, pow_zero] at hj
      exact absurd (orderOf_eq_one_iff.mp hj) hσ'1
    · exact h
  obtain ⟨M', hM'⟩ : ∃ M', M' = (torusSize (Nat.card F) / 2) /
      ℓ ^ (torusSize (Nat.card F) / 2).factorization ℓ := ⟨_, rfl⟩
  have hM'odd : Odd M' := by
    rw [hM']
    exact (torusSize_half_odd hodd).of_dvd_nat (Nat.ordCompl_dvd _ ℓ)
  have hcop : Nat.Coprime (ℓ ^ j) M' := by
    rw [hM']
    exact Nat.Coprime.pow_left j (Nat.coprime_ordCompl hℓ (torusSize_half_odd hodd).pos.ne')
  have hy'C : y ^ b ∈ cenU F a A hfix := hXC hy'X
  have hy'c2 : (y ^ b).left.right = 1 := qd42_c2_eq_one_of_odd (hXo _ hy'X)
  obtain ⟨f, hfdef⟩ : ∃ f : MulAut (SL F),
      f = MatrixCover.slFieldEquiv F ((y.right ^ b : A) : F ≃+* F) := ⟨_, rfl⟩
  have hconj : ∀ w ∈ Torus F a, y ^ b * originalSlInH F a A hfix w * (y ^ b)⁻¹ =
      originalSlInH F a A hfix (f w) := by
    intro w hw
    rw [conj_slIn, qd42_actOn_torus hy'C hy'c2 hw, hy'right, hfdef]
  have hfT : ∀ w ∈ Torus F a, f w ∈ Torus F a := fun w hw => by
    rw [hfdef]
    exact torus_field_invariant F a _ (hfix _) ⟨w, hw⟩
  have hfix' : ∀ w ∈ Torus F a, w ^ M' = 1 → f w = w := by
    intro w hw hwM
    have hwo : Odd (orderOf w) := hM'odd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hwM)
    have hwW : w ∈ Wsl a := (mem_Wsl_iff hodd a ha w).mpr ⟨hw, hwo⟩
    have hwX : originalSlInH F a A hfix w ∈ X := hWX ⟨w, hwW, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : SL F, g = f w * w⁻¹ := ⟨_, rfl⟩
    have hgT : g ∈ Torus F a := hg ▸ (Torus F a).mul_mem (hfT w hw) ((Torus F a).inv_mem hw)
    have hgcomm : originalSlInH F a A hfix g ∈ ⁅X, X⁆ := by
      have h1 := Subgroup.commutator_mem_commutator hy'X hwX
      rw [commutatorElement_def, hconj w hw] at h1
      rw [hg, map_mul, map_inv]
      exact h1
    have hfg : f g = g := by
      have h1 := hy'c _ hgcomm
      have h2 : y ^ b * originalSlInH F a A hfix g * (y ^ b)⁻¹ = originalSlInH F a A hfix g := by
        rw [← h1, mul_inv_cancel_right]
      rw [hconj g hgT] at h2
      exact slIn_injective h2
    have hfw : f w = g * w := by rw [hg, inv_mul_cancel_right]
    have hiter : ∀ n : ℕ, (f ^ n) w = g ^ n * w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfg, hfw, pow_succ, mul_assoc]
    have hgo : g ^ (ℓ ^ j) = 1 := by
      have h1 := hiter (ℓ ^ j)
      have h2 : f ^ (ℓ ^ j) = 1 := by
        rw [hfdef, ← qd42_slFieldHom_eq, ← map_pow, ← Subgroup.coe_pow, ← hj, pow_orderOf_eq_one,
          Subgroup.coe_one, map_one]
      rw [h2, MulAut.one_apply] at h1
      have := congrArg (· * w⁻¹) h1
      simpa using this.symm
    have hgM : g ^ M' = 1 := by
      have hc : Commute (f w) w⁻¹ := torus_mul_comm (hfT w hw) ((Torus F a).inv_mem hw)
      rw [hg, hc.mul_pow, ← map_pow, hwM, map_one, inv_pow, hwM, inv_one, one_mul]
    have hg1 : g = 1 := by
      have h1 : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hgo) (orderOf_dvd_of_pow_eq_one hgM)
      exact orderOf_eq_one_iff.mp h1
    rw [hfw, hg1, one_mul]
  have hσ''ℓ : orderOf ((y.right ^ b) ^ (ℓ ^ (j - 1))) = ℓ := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hℓ.ne_zero) (hj ▸ pow_dvd_pow ℓ (Nat.sub_le j 1)), hj,
      Nat.pow_div (Nat.sub_le j 1) hℓ.pos, show j - (j - 1) = 1 by omega, pow_one]
  have hfix'' : ∀ w ∈ Torus F a, w ^ M' = 1 →
      MatrixCover.slFieldEquiv F (((y.right ^ b) ^ (ℓ ^ (j - 1)) : A) : F ≃+* F) w = w := by
    intro w hw hwM
    have h1 : ∀ n : ℕ, (f ^ n) w = w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hfix' w hw hwM]
    rw [Subgroup.coe_pow, ← qd42_slFieldHom_eq, map_pow, qd42_slFieldHom_eq, ← hfdef]
    exact h1 _
  obtain ⟨w, hwT, hwM, hw⟩ := qd42_exists_torus_moved hodd a ha (hfix _) hℓ hℓ2
    (by rw [Subgroup.orderOf_coe]; exact hσ''ℓ)
  rw [← hM'] at hwM
  exact hw (hfix'' w hwT hwM)

private theorem qd42_actOn_mem_Wsl [Finite F] (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    {m : OriginalH F a A hfix} (hm : ∀ c ∈ cenU F a A hfix, m * c * m⁻¹ ∈ cenU F a A hfix)
    {X : SL F} (hX : X ∈ Wsl a) : actOn m X ∈ Wsl a := by
  obtain ⟨hXT, hXo⟩ := (mem_Wsl_iff hodd a ha X).mp hX
  have hC : originalSlInH F a A hfix (actOn m X) ∈ cenU F a A hfix := by
    rw [← conj_slIn]
    exact hm _ ((slIn_mem_cenU_iff X).mpr hXT)
  refine (mem_Wsl_iff hodd a ha _).mpr ⟨(slIn_mem_cenU_iff _).mp hC, ?_⟩
  have h1 : orderOf (originalSlInH F a A hfix (actOn m X)) = orderOf X := by
    rw [← conj_slIn, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
      orderOf_injective _ slIn_injective]
  rw [orderOf_injective _ slIn_injective] at h1
  rw [h1]
  exact hXo

end Model

section Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem qd42_commutator_subgroupOf {H₁ H₂ K : Subgroup G} (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) :
    ⁅H₁.subgroupOf K, H₂.subgroupOf K⁆ = (⁅H₁, H₂⁆ : Subgroup G).subgroupOf K := by
  have hc : ⁅H₁, H₂⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (h₁ hx) (h₂ hy)) (K.inv_mem (h₁ hx))) (K.inv_mem (h₂ hy))
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left h₁, inf_of_le_left h₂, inf_of_le_left hc]

private theorem qd42_odd_card_of_forall {H : Subgroup G} (hH : ∀ x ∈ H, Odd (orderOf x)) :
    Odd (Nat.card H) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card H := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have h1 := hH x x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact absurd h1 (by decide)

private theorem qd42_Wsl_le_map_W {σ : Setting G} {F : Type} [Field F] [Finite F]
    {A : Subgroup (F ≃+* F)} {a : Fˣ} {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a}
    {φ : σ.N →* OriginalH F a A hfix}
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix))
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) {J : Subgroup G} (hJ : σ.IsV21Layer J)
    {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    (Wsl a).map (originalSlInH F a A hfix) ≤ (W.subgroupOf σ.N).map φ := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hJN : J ≤ σ.N := hJ.le.trans hφ.L₀_le
  have hpON : pCoreIn σ.p σ.N ≤ σ.ON := hJ.inf_eq ▸ inf_le_right
  have hpbot : ((pCoreIn σ.p σ.N).subgroupOf σ.N).map φ = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [hφ.ker_eq]; exact subgroupOf_mono_of_le hpON _)
  have hmapW : (W.subgroupOf σ.N).map φ =
      ((oddCoreIn σ.C ⊓ J : Subgroup G).subgroupOf σ.N).map φ := by
    have h1 : ((W ⊔ pCoreIn σ.p σ.N : Subgroup G).subgroupOf σ.N).map φ =
        (W.subgroupOf σ.N).map φ := by
      rw [Subgroup.subgroupOf_sup (hW.1.trans hJN) (hpON.trans σ.ON_le_N), Subgroup.map_sup,
        hpbot, sup_bot_eq]
    have h2 : (((oddCoreIn σ.C ⊓ J) ⊔ pCoreIn σ.p σ.N : Subgroup G).subgroupOf σ.N).map φ =
        ((oddCoreIn σ.C ⊓ J : Subgroup G).subgroupOf σ.N).map φ := by
      rw [Subgroup.subgroupOf_sup (inf_le_right.trans hJN) (hpON.trans σ.ON_le_N),
        Subgroup.map_sup, hpbot, sup_bot_eq]
    rw [← h1, hW.2.2.2, h2]
  have hmapJ : (J.subgroupOf σ.N).map φ = layerM F a A hfix := by
    rw [← hφ.map_L₀, hJ.sup_eq, Subgroup.subgroupOf_sup hJN σ.ON_le_N, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq hφ.ker_eq.symm), sup_bot_eq]
  rw [hmapW]
  rintro _ ⟨X, hX, rfl⟩
  have hXT : X ∈ Torus F a := Wsl_le_torus a hX
  have hXM : originalSlInH F a A hfix X ∈ (J.subgroupOf σ.N).map φ := by
    rw [hmapJ]
    exact ⟨X, rfl⟩
  obtain ⟨g, hg, hgX⟩ := hXM
  have hx₂ : (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N) * ⟨σ.x₂, hφ.x₂_mem⟩ = 1 := Subtype.ext hφ.x₂_mul_self
  have hU : ∀ v ∈ J.subgroupOf σ.N,
      (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N) * v * (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)⁻¹ ∈ J.subgroupOf σ.N := by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hJ.normal hφ.x₂_mem) v).mp hv
    simpa using this
  have hc : φ g * φ ⟨σ.x₂, hφ.x₂_mem⟩ = φ ⟨σ.x₂, hφ.x₂_mem⟩ * φ g := by
    rw [hφ.map_x₂, hgX]
    exact Subgroup.mem_centralizer_singleton_iff.mp ((slIn_mem_cenU_iff X).mpr hXT)
  obtain ⟨v, hvJ, hvφ, hvc⟩ := exists_commute_lift φ hφ.odd_card_ker hx₂ hU hg hc
  have hvC : (v : G) ∈ σ.C := (mem_C_iff σ v.2).mpr (congrArg Subtype.val hvc)
  set K₀ : Subgroup G := (((σ.C ⊓ J).subgroupOf σ.N) ⊓
    ((Wsl a).map (originalSlInH F a A hfix)).comap φ).map σ.N.subtype with hK₀
  have hK₀C : K₀ ≤ σ.C := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp hk.1).1
  have hK₀n : σ.C ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro c hcC
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨k, hk, rfl⟩
    have hcN : c ∈ σ.N := C_le_N σ hcC
    obtain ⟨hk1, hk2⟩ := hk
    have hkCJ : (k : G) ∈ σ.C ⊓ J := Subgroup.mem_subgroupOf.mp hk1
    have hmem1 : (⟨c, hcN⟩ * k * (⟨c, hcN⟩ : σ.N)⁻¹ : σ.N) ∈ (σ.C ⊓ J).subgroupOf σ.N := by
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨σ.C.mul_mem (σ.C.mul_mem hcC hkCJ.1) (σ.C.inv_mem hcC),
        (Subgroup.mem_normalizer_iff.mp (hJ.normal hcN) k).mp hkCJ.2⟩
    have hmem2 : (⟨c, hcN⟩ * k * (⟨c, hcN⟩ : σ.N)⁻¹ : σ.N) ∈
        ((Wsl a).map (originalSlInH F a A hfix)).comap φ := by
      have hcU : φ ⟨c, hcN⟩ ∈ cenU F a A hfix := by
        rw [cenU, ← hφ.map_C]
        exact ⟨⟨c, hcN⟩, hcC, rfl⟩
      obtain ⟨Y, hY, hYk⟩ := hk2
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, ← hYk, conj_slIn]
      exact ⟨_, qd42_actOn_mem_Wsl hodd ha (fun c' hc' => (cenU F a A hfix).mul_mem
        ((cenU F a A hfix).mul_mem hcU hc') ((cenU F a A hfix).inv_mem hcU)) hY, rfl⟩
    exact ⟨_, ⟨hmem1, hmem2⟩, by simp⟩
  have hK₀odd : Odd (Nat.card K₀) := by
    apply qd42_odd_card_of_forall
    rintro _ ⟨k, ⟨-, Y, hY, hYk⟩, rfl⟩
    obtain ⟨-, hYo⟩ := (mem_Wsl_iff hodd a ha Y).mp hY
    have hφk : orderOf (φ k) = orderOf Y := by
      rw [← hYk, orderOf_injective _ slIn_injective]
    have hker : k ^ orderOf Y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hφk, pow_orderOf_eq_one]
    rw [hφ.ker_eq, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hker
    have hko : Odd (orderOf ((k : G) ^ orderOf Y)) :=
      (odd_card_oddCoreIn σ.N).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hker)
    have hdvd : orderOf (k : G) ∣ orderOf Y * orderOf ((k : G) ^ orderOf Y) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    exact (hYo.mul hko).of_dvd_nat hdvd
  have hvO : (v : G) ∈ oddCoreIn σ.C :=
    le_oddCoreIn hK₀C hK₀n hK₀odd ⟨v, ⟨Subgroup.mem_subgroupOf.mpr
      ⟨hvC, Subgroup.mem_subgroupOf.mp hvJ⟩, X, hX, (hvφ.trans hgX).symm⟩, rfl⟩
  exact ⟨v, Subgroup.mem_subgroupOf.mpr ⟨hvO, Subgroup.mem_subgroupOf.mp hvJ⟩, hvφ.trans hgX⟩

private theorem qd42_lemmaII42Input_of_modelMap {σ : Setting G} {F : Type} [Field F] [Finite F]
    {A : Subgroup (F ≃+* F)} {a : Fˣ} {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a}
    {φ : σ.N →* OriginalH F a A hfix}
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix))
    (hodd : Odd (Nat.card F)) (hA : Odd (Nat.card A)) (ha : ¬IsSquare a)
    {J : Subgroup G} (hJ : σ.IsV21Layer J) : V4.LemmaII42Input σ J := by
  intro W hW X hXC hWX y hyX hyc
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hXN : X ≤ σ.N := hXC.trans ((oddCoreIn_le σ.C).trans (C_le_N σ))
  set Xb := (X.subgroupOf σ.N).map φ with hXb
  have hXbC : Xb ≤ cenU F a A hfix := by
    rw [cenU, ← hφ.map_C]
    exact Subgroup.map_mono (subgroupOf_mono_of_le (hXC.trans (oddCoreIn_le σ.C)) _)
  have hXbo : ∀ x ∈ Xb, Odd (orderOf x) := by
    rintro _ ⟨g, hg, rfl⟩
    have hgC : (g : G) ∈ oddCoreIn σ.C := hXC (Subgroup.mem_subgroupOf.mp hg)
    exact (odd_card_oddCoreIn σ.C).of_dvd_nat ((orderOf_map_dvd φ g).trans (by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard _ hgC))
  have hWXb : (Wsl a).map (originalSlInH F a A hfix) ≤ Xb :=
    (qd42_Wsl_le_map_W hφ hodd ha hJ hW).trans (Subgroup.map_mono (subgroupOf_mono_of_le hWX _))
  have hyN : y ∈ σ.N := hXN hyX
  have hyXb : φ ⟨y, hyN⟩ ∈ Xb := ⟨⟨y, hyN⟩, hyX, rfl⟩
  have hyc' : ∀ z ∈ ⁅Xb, Xb⁆, z * φ ⟨y, hyN⟩ = φ ⟨y, hyN⟩ * z := by
    rw [hXb, ← Subgroup.map_commutator, qd42_commutator_subgroupOf hXN hXN]
    rintro _ ⟨z, hz, rfl⟩
    have hk : (⟨y, hyN⟩ * z * (⟨y, hyN⟩ : σ.N)⁻¹ * z⁻¹ : σ.N) ∈ φ.ker := by
      rw [hφ.ker_eq, Subgroup.mem_subgroupOf]
      simpa using hyc z (Subgroup.mem_subgroupOf.mp hz)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    have h1 := mul_inv_eq_one.mp hk
    calc φ z * φ ⟨y, hyN⟩ = φ ⟨y, hyN⟩ * φ z * (φ ⟨y, hyN⟩)⁻¹ * φ ⟨y, hyN⟩ := by rw [h1]
      _ = φ ⟨y, hyN⟩ * φ z := by group
  have hright := qd42_right_eq_one hodd ha hA hXbC hXbo hWXb hyXb hyc'
  have hyM : φ ⟨y, hyN⟩ ∈ (σ.L₀.subgroupOf σ.N).map φ := by
    rw [hφ.map_L₀]
    exact mem_layerM_of_odd _ (hXbo _ hyXb) hright
  exact Subgroup.mem_sup_left (hφ.mem_of_map_mem hφ.ON_le hyM)

end Transport

theorem frontier_lemmaII42Input {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsV21Layer J →
      V4.LemmaII42Input (frontierSetting S fS t p f) J := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, hA, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hpodd.pow
  intro J hJ
  exact qd42_lemmaII42Input_of_modelMap hφ hodd hA ha hJ

end

end CFSG.Semidihedral.AllPrime
