module

public import CFSG.CGT.Stroth77.Section224CExtension

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem two_torsion_solution_familyOne (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (w w' : Torus Z.τ.k) (hw2 : (2 : ℤ) • w = 0) (hw2' : (2 : ℤ) • w' = 0)
    (hU10 : Z.τ.action.u 1 0 = 0) (hU11 : Z.τ.action.u 1 1 = 0)
    (hU12 : Z.τ.action.u 1 2 = 1)
    (hU20 : Z.τ.action.u 2 0 = 0) (hU21 : Z.τ.action.u 2 1 = 1)
    (hU22 : Z.τ.action.u 2 2 = 0)
    (hR : ∀ i j, Z.τ.action.ρ i j = Type100.ρM i j)
    (hV10 : Z.τ.action.uv 1 0 ≡ 2 [ZMOD 4])
    (hV11 : Odd (Z.τ.action.uv 1 1))
    (hUeq : w' = matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u w)
    (hReq : w' = matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ w)
    (hVeq : matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv w = w)
    (hne : w ≠ 0) :
    w = (2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k) ∧
      w' = (2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k) := by
  classical
  have hm2 : 2 ≤ Z.τ.m := by
    have := hk 0
    simpa [StrothTypeIndex.m] using this
  have hm1 : 1 ≤ Z.τ.m := by omega
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  obtain ⟨ε, hε, hwε0⟩ := (Torus.two_zsmul_eq_zero_iff hk1all w).mp hw2
  obtain ⟨ε', hε', hw'ε0⟩ := (Torus.two_zsmul_eq_zero_iff hk1all w').mp hw2'
  set v : Fin 3 → ℤ := fun i => ε i * 2 ^ (Z.τ.k i - 1) with hv
  set v' : Fin 3 → ℤ := fun i => ε' i * 2 ^ (Z.τ.k i - 1) with hv'
  have hwε : w = Torus.ofInt Z.τ.k v := by simpa [v] using hwε0
  have hw'ε : w' = Torus.ofInt Z.τ.k v' := by simpa [v'] using hw'ε0
  have hk1 : Z.τ.k 1 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_eq]
    simp [hrel]
  have hk2 : Z.τ.k 2 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hu_int : Torus.ofInt Z.τ.k v' =
      Torus.ofInt Z.τ.k (Z.τ.action.u *ᵥ v) := by
    rw [← matAct_ofInt]
    rw [← hw'ε, ← hwε]
    exact hUeq
  have hu1 : ε' 1 = ε 2 := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hu_int) 1
    have h' : ε' 1 * 2 ^ Z.τ.m ≡ ε 2 * 2 ^ Z.τ.m [ZMOD 2 ^ (Z.τ.m + 1)] := by
      simpa [v, v', hk1, hk2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hU10, hU11, hU12, Nat.add_sub_cancel] using h
    exact int_eq_of_modEq_two (hε' 1) (hε 2)
      (int_modEq_two_of_mul_two_pow_modEq h')
  have hu2 : ε' 2 = ε 1 := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hu_int) 2
    have h' : ε' 2 * 2 ^ Z.τ.m ≡ ε 1 * 2 ^ Z.τ.m [ZMOD 2 ^ (Z.τ.m + 1)] := by
      simpa [v, v', hk1, hk2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hU20, hU21, hU22, Nat.add_sub_cancel] using h
    exact int_eq_of_modEq_two (hε' 2) (hε 1)
      (int_modEq_two_of_mul_two_pow_modEq h')
  have hr_int : Torus.ofInt Z.τ.k v' =
      Torus.ofInt Z.τ.k (Z.τ.action.ρ *ᵥ v) := by
    rw [← matAct_ofInt]
    rw [← hw'ε, ← hwε]
    exact hReq
  have hr2 : ε' 2 ≡ ε 1 - ε 2 [ZMOD 2] := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hr_int) 2
    have h' : ε' 2 * 2 ^ Z.τ.m ≡ ε 1 * 2 ^ Z.τ.m + -(ε 2 * 2 ^ Z.τ.m)
        [ZMOD 2 ^ (Z.τ.m + 1)] := by
      simpa [v, v', hk1, hk2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hR, Type100.ρM, ofCols_apply, Nat.add_sub_cancel] using h
    have h'' : ε' 2 * 2 ^ Z.τ.m ≡ (ε 1 - ε 2) * 2 ^ Z.τ.m
        [ZMOD 2 ^ (Z.τ.m + 1)] := by
      rwa [show ε 1 * 2 ^ Z.τ.m + -(ε 2 * 2 ^ Z.τ.m) =
        (ε 1 - ε 2) * 2 ^ Z.τ.m by ring] at h'
    exact int_modEq_two_of_mul_two_pow_modEq h''
  have hε2 : ε 2 = 0 := by
    have h' : ε 1 ≡ ε 1 - ε 2 [ZMOD 2] := by simpa [hu2] using hr2
    have hdvd : (2 : ℤ) ∣ 0 - ε 2 := by
      have := Int.modEq_iff_dvd.mp h'
      simpa using this
    exact int_eq_zero_of_modEq_two (hε 2) (Int.modEq_iff_dvd.mpr hdvd)
  have hr0 : ε' 0 = ε 0 := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hr_int) 0
    have h' : ε' 0 * 2 ^ (Z.τ.k 0 - 1) ≡ ε 0 * 2 ^ (Z.τ.k 0 - 1)
        [ZMOD 2 ^ Z.τ.k 0] := by
      simpa [v, v', hR, Type100.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, hε2] using h
    exact int_eq_of_modEq_two (hε' 0) (hε 0)
      (int_modEq_two_of_mul_two_pow_pred_modEq hm1 h')
  have hv_int : Torus.ofInt Z.τ.k v =
      Torus.ofInt Z.τ.k (Z.τ.action.uv *ᵥ v) := by
    rw [← matAct_ofInt]
    rw [← hwε]
    exact hVeq.symm
  have hε0 : ε 0 = 0 := by
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hV10
    have huv10 : Z.τ.action.uv 1 0 = 2 * (1 - 2 * t) := by
      linear_combination -ht
    obtain ⟨r, hr⟩ := hV11
    have h := (Torus.ofInt_eq_ofInt_iff.mp hv_int) 1
    have h' : ε 1 * 2 ^ Z.τ.m ≡
        ((1 - 2 * t) * ε 0 + (2 * r + 1) * ε 1) * 2 ^ Z.τ.m
          [ZMOD 2 ^ (Z.τ.m + 1)] := by
      have hpow : (2 : ℤ) * 2 ^ (Z.τ.m - 1) = 2 ^ Z.τ.m := by
        rw [← pow_succ', Nat.sub_add_cancel hm1]
      have heq : (2 * (1 - 2 * t)) * (ε 0 * 2 ^ (Z.τ.k 0 - 1)) +
          (2 * r + 1) * (ε 1 * 2 ^ Z.τ.m) =
          ((1 - 2 * t) * ε 0 + (2 * r + 1) * ε 1) * 2 ^ Z.τ.m := by
        have hk0 : Z.τ.k 0 = Z.τ.m := rfl
        rw [hk0, ← hpow]
        ring
      simpa [v, hk1, Matrix.mulVec, dotProduct, Fin.sum_univ_three, huv10, hr,
        hε2, Nat.add_sub_cancel, heq] using h
    have hmod : (1 - 2 * t) * ε 0 + (2 * r + 1) * ε 1 ≡ ε 1 [ZMOD 2] :=
      int_modEq_two_of_mul_two_pow_modEq h'.symm
    have hodd : (2 * r + 1) * ε 1 ≡ ε 1 [ZMOD 2] := by
      have hzero : 2 * (r * ε 1) ≡ 0 [ZMOD 2] :=
        Int.modEq_zero_iff_dvd.mpr ⟨r * ε 1, by ring⟩
      have hsplit : (2 * r + 1) * ε 1 = 2 * (r * ε 1) + ε 1 := by ring
      rw [hsplit]
      simpa using hzero.add (Int.ModEq.refl (ε 1))
    have hA : (1 - 2 * t) * ε 0 ≡ 0 [ZMOD 2] := by
      have hsub := hmod.sub hodd
      simpa [add_sub_cancel_right] using hsub
    rcases hε 0 with h0 | h1
    · exact h0
    · exfalso
      rw [h1, mul_one] at hA
      obtain ⟨u', hu'⟩ : ∃ u', 1 - 2 * t = 2 * u' + 1 := ⟨-t, by ring⟩
      rw [hu'] at hA
      have h2 : (2 : ℤ) ∣ 2 * u' + 1 := Int.modEq_zero_iff_dvd.mp hA
      omega
  have hε1 : ε 1 = 1 := by
    rcases hε 1 with h0 | h1
    · exfalso
      apply hne
      rw [hwε]
      have hvec : v = 0 := by
        funext i
        fin_cases i <;> simp [v, hε0, h0, hε2]
      rw [hvec]
      simp
    · exact h1
  have ha_ofInt : (Torus.a : Torus Z.τ.k) = Torus.ofInt Z.τ.k ![0, 1, 0] := by
    funext i
    fin_cases i <;> simp [Torus.a, gen, Torus.ofInt_apply, Fin.isValue]
  have hb_ofInt : (Torus.b : Torus Z.τ.k) = Torus.ofInt Z.τ.k ![0, 0, 1] := by
    funext i
    fin_cases i <;> simp [Torus.b, gen, Torus.ofInt_apply, Fin.isValue]
  have hv_eq : v = (2 : ℤ) ^ Z.τ.m • (![0, 1, 0] : Fin 3 → ℤ) := by
    funext i
    fin_cases i <;>
      simp [v, hk1, hk2, hε0, hε1, hε2, Nat.add_sub_cancel]
  have hv'_eq : v' = (2 : ℤ) ^ Z.τ.m • (![0, 0, 1] : Fin 3 → ℤ) := by
    funext i
    fin_cases i <;>
      simp [v', hk1, hk2, hε0, hε1, hε2, hu1, hu2, hr0, Nat.add_sub_cancel]
  constructor
  · calc w = Torus.ofInt Z.τ.k v := hwε
      _ = Torus.ofInt Z.τ.k ((2 : ℤ) ^ Z.τ.m • (![0, 1, 0] : Fin 3 → ℤ)) := by
          rw [hv_eq]
      _ = (2 : ℤ) ^ Z.τ.m • Torus.ofInt Z.τ.k (![0, 1, 0] : Fin 3 → ℤ) :=
          Torus.ofInt_zsmul _ _
      _ = (2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k) := by rw [← ha_ofInt]
  · calc w' = Torus.ofInt Z.τ.k v' := hw'ε
      _ = Torus.ofInt Z.τ.k ((2 : ℤ) ^ Z.τ.m • (![0, 0, 1] : Fin 3 → ℤ)) := by
          rw [hv'_eq]
      _ = (2 : ℤ) ^ Z.τ.m • Torus.ofInt Z.τ.k (![0, 0, 1] : Fin 3 → ℤ) :=
          Torus.ofInt_zsmul _ _
      _ = (2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k) := by rw [← hb_ofInt]

theorem deviation_form_diag_familyOne (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D)
    (hU10 : Z.τ.action.u 1 0 = 0) (hU11 : Z.τ.action.u 1 1 = 0)
    (hU12 : Z.τ.action.u 1 2 = 1)
    (hU20 : Z.τ.action.u 2 0 = 0) (hU21 : Z.τ.action.u 2 1 = 1)
    (hU22 : Z.τ.action.u 2 2 = 0)
    (hR : ∀ i j, Z.τ.action.ρ i j = Type100.ρM i j)
    (hV10 : Z.τ.action.uv 1 0 ≡ 2 [ZMOD 4])
    (hV11 : Odd (Z.τ.action.uv 1 1))
    (huv0 : Even (Z.τ.action.uv 0 1))
    (huv2 : Even (Z.τ.action.uv 2 1)) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ Z.τ.m) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ Z.τ.m) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  classical
  have hm1 : 1 ≤ Z.τ.m := by
    have := hk 0
    have : 2 ≤ Z.τ.m := by simpa [StrothTypeIndex.m] using this
    omega
  have hs : s ∈ Z.centralizerInMho := hF hsF
  have hc_mem : (Z.dataD.c : G) ∈ omegaIn (Z.τ.n - 1) Z.D := by
    refine mem_omegaIn_of_pow_eq_one Z.dataD.c.2 ?_
    have hn : Z.τ.n - 1 = Z.τ.m := by omega
    rw [hn, ← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, Z.dataD.orderOf_c]
  have hcs : s * (Z.dataD.c : G) = (Z.dataD.c : G) * s :=
    (Subgroup.mem_centralizer_iff.mp (hcent hsF) _ hc_mem).symm
  have hφc : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 := by
    rw [deviation_apply]
    calc s * (Z.dataD.c : G) * s⁻¹ * (Z.dataD.c : G)⁻¹
        = (Z.dataD.c : G) * s * s⁻¹ * (Z.dataD.c : G)⁻¹ := by rw [hcs]
      _ = 1 := by group
  have hΦc0 : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩) = 0 := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul.2⟩ : Z.D) = 1 :=
      Subtype.ext hφc
    rw [h1]
    simp
  have huL : Z.dataD.u ∈ X.L := Z.hL ▸ Z.dataD.u_mem_L
  have huvL : Z.dataD.uv ∈ X.L := Z.hL ▸ Z.dataD.uv_mem_L
  have hρL : Z.dataD.ρ ∈ X.L := Z.hL ▸ Z.dataD.ρ_mem_L
  obtain ⟨du, hduD, hdu⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hsF hsD huL
  obtain ⟨duv, hduvD, hduv⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hsF hsD huvL
  obtain ⟨dr, hdrD, hdr⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hsF hsD
      (X.L.inv_mem hρL)
  have huinv : (Z.dataD.u)⁻¹ = Z.dataD.u := inv_eq_of_mul_eq_one_right Z.dataD.u_sq
  have huvinv : (Z.dataD.uv)⁻¹ = Z.dataD.uv :=
    inv_eq_of_mul_eq_one_right Z.dataD.uv_sq
  have hdu' : Z.dataD.u * s * (Z.dataD.u)⁻¹ = s * du := by
    simpa [huinv] using hdu
  have hduv' : Z.dataD.uv * s * (Z.dataD.uv)⁻¹ = s * duv := by
    simpa [huvinv] using hduv
  have hdr' : Z.dataD.ρ * s * (Z.dataD.ρ)⁻¹ = s * dr := by
    simpa using hdr
  have hcolU : matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u
      (Torus.a : Torus Z.τ.k) =
      (Z.τ.action.u 0 1) • (Torus.c : Torus Z.τ.k) + Torus.b := by
    rw [show (Torus.a : Torus Z.τ.k) = gen Z.τ.k 1 from rfl, matAct_gen_eq]
    simp [hU11, hU21]
  have hcolR : matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ
      (Torus.a : Torus Z.τ.k) = Torus.b := by
    rw [show (Torus.a : Torus Z.τ.k) = gen Z.τ.k 1 from rfl, matAct_gen_eq]
    simp [hR, Type100.ρM, ofCols_apply]
  have hcolV : matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv
      (Torus.a : Torus Z.τ.k) =
      (Z.τ.action.uv 0 1) • (Torus.c : Torus Z.τ.k) +
        (Z.τ.action.uv 1 1) • (Torus.a : Torus Z.τ.k) +
          (Z.τ.action.uv 2 1) • (Torus.b : Torus Z.τ.k) := by
    rw [show (Torus.a : Torus Z.τ.k) = gen Z.τ.k 1 from rfl, matAct_gen_eq]
  have hua : conjBy Z.dataD.u_mem (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) =
      (⟨Z.dataD.c, Z.dataD.c.2⟩ : Z.D) ^ (Z.τ.action.u 0 1) *
        ⟨Z.dataD.b, Z.dataD.b.2⟩ := by
    have h := Z.dataD.u_conj (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)
    rw [Z.dataD.e_a] at h
    rw [show Z.τ.action.φu (Torus.a : Torus Z.τ.k) =
        (Z.τ.action.u 0 1) • Torus.c + Torus.b from hcolU] at h
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [h, ofMul_mul, ofMul_zpow, map_add, map_zsmul, Z.dataD.e_c, Z.dataD.e_b]
  have hρa : conjBy Z.dataD.ρ_mem (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) =
      ⟨Z.dataD.b, Z.dataD.b.2⟩ := by
    have h := Z.dataD.ρ_conj (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)
    rw [Z.dataD.e_a] at h
    rw [show Z.τ.action.φρ (Torus.a : Torus Z.τ.k) = Torus.b from hcolR] at h
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [h, Z.dataD.e_b]
  have huva : conjBy Z.dataD.uv_mem (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) =
      (⟨Z.dataD.c, Z.dataD.c.2⟩ : Z.D) ^ (Z.τ.action.uv 0 1) *
        (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ (Z.τ.action.uv 1 1) *
          (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ (Z.τ.action.uv 2 1) := by
    have h := Z.dataD.uv_conj (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)
    rw [Z.dataD.e_a] at h
    rw [show Z.τ.action.φuv (Torus.a : Torus Z.τ.k) =
        (Z.τ.action.uv 0 1) • Torus.c + (Z.τ.action.uv 1 1) • Torus.a +
          (Z.τ.action.uv 2 1) • Torus.b from hcolV] at h
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [h, ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow,
      map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      Z.dataD.e_c, Z.dataD.e_a, Z.dataD.e_b]
  have hdev_u : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
      matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u
        (deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)) := by
    have h := deviationTorus_conj_eq Z hs hduD Z.dataD.u_mem hdu'
      (M := Z.τ.action.u) (hM := Z.τ.action.compat_u) (hmat := Z.dataD.u_conj)
      (x := Z.dataD.a) Z.dataD.a.2
    rw [hua] at h
    have hcb : deviationTorus Z s hs (Additive.ofMul
        ((⟨Z.dataD.c, Z.dataD.c.2⟩ : Z.D) ^ (Z.τ.action.u 0 1) *
          ⟨Z.dataD.b, Z.dataD.b.2⟩)) =
        deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) := by
      rw [ofMul_mul, ofMul_zpow, map_add, map_zsmul, hΦc0, smul_zero, zero_add]
    rw [hcb] at h
    exact h
  have hdev_r : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ
        (deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)) := by
    have h := deviationTorus_conj_eq Z hs hdrD Z.dataD.ρ_mem hdr'
      (M := Z.τ.action.ρ) (hM := Z.τ.action.compat_ρ) (hmat := Z.dataD.ρ_conj)
      (x := Z.dataD.a) Z.dataD.a.2
    rw [hρa] at h
    exact h
  have hdev_uv : matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv
      (deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)) =
      deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) := by
    have h := deviationTorus_conj_eq Z hs hduvD Z.dataD.uv_mem hduv'
      (M := Z.τ.action.uv) (hM := Z.τ.action.compat_uv) (hmat := Z.dataD.uv_conj)
      (x := Z.dataD.a) Z.dataD.a.2
    rw [huva] at h
    have hcalc : deviationTorus Z s hs (Additive.ofMul
        ((⟨Z.dataD.c, Z.dataD.c.2⟩ : Z.D) ^ (Z.τ.action.uv 0 1) *
          (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ (Z.τ.action.uv 1 1) *
            (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ (Z.τ.action.uv 2 1))) =
        deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) := by
      rw [ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow,
        map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hΦc0, smul_zero, zero_add]
      have hw2 : (2 : ℤ) • deviationTorus Z s hs
          (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) = 0 :=
        deviationTorus_two_zsmul Z s hs _
      have hw2' : (2 : ℤ) • deviationTorus Z s hs
          (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) = 0 :=
        deviationTorus_two_zsmul Z s hs _
      have hodd : ∀ {z : ℤ}, Odd z → ∀ {x : Torus Z.τ.k}, (2 : ℤ) • x = 0 → z • x = x := by
        intro z hz x hx
        obtain ⟨r, rfl⟩ := hz
        rw [add_zsmul, mul_zsmul', hx, smul_zero, zero_add, one_zsmul]
      have heven : ∀ {z : ℤ}, Even z → ∀ {x : Torus Z.τ.k}, (2 : ℤ) • x = 0 → z • x = 0 := by
        intro z hz x hx
        obtain ⟨r, rfl⟩ := hz
        rw [show r + r = 2 * r by ring, mul_zsmul', hx, smul_zero]
      rw [hodd hV11 hw2, heven huv2 hw2', add_zero]
    rw [hcalc] at h
    exact h.symm
  have hne : deviationTorus Z s hs
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) ≠ 0 := by
    intro hw0
    apply hsD
    have hΦa0 : deviationTorus Z s hs
        (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) = 0 := hw0
    have hΦb0 : deviationTorus Z s hs
        (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) = 0 := by
      rw [hdev_u, hΦa0, map_zero]
    have hΦall : ∀ x : Z.D, deviationTorus Z s hs (Additive.ofMul x) = 0 := by
      intro x
      obtain ⟨W, hW⟩ := Torus.exists_ofInt (Z.dataD.e (Additive.ofMul x))
      have hdec : Additive.ofMul x =
          Z.dataD.e.symm (W 0 • (Torus.c : Torus Z.τ.k) +
            W 1 • (Torus.a : Torus Z.τ.k) + W 2 • (Torus.b : Torus Z.τ.k)) := by
        apply Z.dataD.e.injective
        rw [AddEquiv.apply_symm_apply, ← hW, Torus.ofInt_eq_zsmul_gens]
      have hc' : Z.dataD.e.symm (Torus.c : Torus Z.τ.k) =
          Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩ := by
        rw [← Z.dataD.e_c, AddEquiv.symm_apply_apply]
      have ha' : Z.dataD.e.symm (Torus.a : Torus Z.τ.k) =
          Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩ := by
        rw [← Z.dataD.e_a, AddEquiv.symm_apply_apply]
      have hb' : Z.dataD.e.symm (Torus.b : Torus Z.τ.k) =
          Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩ := by
        rw [← Z.dataD.e_b, AddEquiv.symm_apply_apply]
      rw [hdec]
      simp only [map_add, map_zsmul, hc', ha', hb', hΦc0, hΦa0, hΦb0, smul_zero, add_zero]
    apply Z.mem_of_mem_centralizer (hF hsF).1.1
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hΦall ⟨d, hd⟩
    rw [deviationTorus_apply] at h
    have h1 : ((deviation Z s hs (Additive.ofMul ⟨d, hd⟩)).toMul : G) = 1 := by
      have h' : Z.dataD.e (Additive.ofMul ⟨((deviation Z s hs
          (Additive.ofMul ⟨d, hd⟩)).toMul : G), omegaIn_le 1 Z.D
            (deviation Z s hs (Additive.ofMul ⟨d, hd⟩)).toMul.2⟩) =
          Z.dataD.e (Additive.ofMul (1 : Z.D)) := by
        rw [h]
        simp
      have hx := Additive.ofMul.injective (Z.dataD.e.injective h')
      simpa using congrArg Subtype.val hx
    have h2 : s * d * s⁻¹ * d⁻¹ = 1 := by
      simpa [deviation_apply] using h1
    have h3 : s * d * s⁻¹ = d := by
      have := congrArg (· * d) h2
      simpa [mul_assoc] using this
    have h4 : s * d = d * s := by
      have := congrArg (· * s) h3
      simpa [mul_assoc] using this
    exact h4.symm
  have hw2a : (2 : ℤ) • deviationTorus Z s hs
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) = 0 := deviationTorus_two_zsmul Z s hs _
  have hw2b : (2 : ℤ) • deviationTorus Z s hs
      (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) = 0 := deviationTorus_two_zsmul Z s hs _
  obtain ⟨hwval, hw'val⟩ :=
    two_torsion_solution_familyOne Z hk hrel _ _ hw2a hw2b
      hU10 hU11 hU12 hU20 hU21 hU22 hR hV10 hV11 hdev_u hdev_r hdev_uv hne
  have hφa : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ Z.τ.m) := by
    have h : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) =
        (2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k) := hwval
    rw [deviationTorus_apply] at h
    have h2 : Z.dataD.e (Additive.ofMul (Z.dataD.a ^ (2 ^ Z.τ.m))) =
        (2 ^ Z.τ.m : ℕ) • (Torus.a : Torus Z.τ.k) := by
      rw [Z.dataD.e_pow, Z.dataD.e_a]
    have h' : Z.dataD.e (Additive.ofMul ⟨((deviation Z s (hF hsF)
        (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G), omegaIn_le 1 Z.D
          (deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a,
            Z.dataD.a.2⟩)).toMul.2⟩) =
        Z.dataD.e (Additive.ofMul (Z.dataD.a ^ (2 ^ Z.τ.m))) := by
      rw [h, h2, show (2 : ℤ) ^ Z.τ.m = ((2 ^ Z.τ.m : ℕ) : ℤ) by push_cast; ring,
        natCast_zsmul]
    have hx := Additive.ofMul.injective (Z.dataD.e.injective h')
    simpa using congrArg Subtype.val hx
  have hφb : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ Z.τ.m) := by
    have h : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
        (2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k) := hw'val
    rw [deviationTorus_apply] at h
    have h2 : Z.dataD.e (Additive.ofMul (Z.dataD.b ^ (2 ^ Z.τ.m))) =
        (2 ^ Z.τ.m : ℕ) • (Torus.b : Torus Z.τ.k) := by
      rw [Z.dataD.e_pow, Z.dataD.e_b]
    have h' : Z.dataD.e (Additive.ofMul ⟨((deviation Z s (hF hsF)
        (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G), omegaIn_le 1 Z.D
          (deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b,
            Z.dataD.b.2⟩)).toMul.2⟩) =
        Z.dataD.e (Additive.ofMul (Z.dataD.b ^ (2 ^ Z.τ.m))) := by
      rw [h, h2, show (2 : ℤ) ^ Z.τ.m = ((2 ^ Z.τ.m : ℕ) : ℤ) by push_cast; ring,
        natCast_zsmul]
    have hx := Additive.ofMul.injective (Z.dataD.e.injective h')
    simpa using congrArg Subtype.val hx
  exact ⟨hφc, hφa, hφb, fun d => deviation_sq_mem Z s (hF hsF) d⟩


theorem deviation_form_diag_t101 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {n : ℕ} (hτ : Z.τ = StrothTypeIndex.t101 n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (n + 1)) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (n + 1)) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t101 n, dataD, hL, hcentS⟩ with hZ'
  have hres := deviation_form_diag_familyOne Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by intro i j; rfl)
    (by
      show (-2 : ℤ) ≡ 2 [ZMOD 4]
      norm_num)
    (by
      show Odd (1 : ℤ)
      norm_num)
    (by
      show Even (2 : ℤ)
      norm_num)
    (by
      show Even ((2 : ℤ) + 2 ^ (n + 1))
      simp +decide [parity_simps])
  exact hres


theorem deviation_form_diag_t110 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {t : ℕ} (hτ : Z.τ = StrothTypeIndex.t110 t)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (t + 2)) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (t + 2)) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t110 t, dataD, hL, hcentS⟩ with hZ'
  have hres := deviation_form_diag_familyOne Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by intro i j; rfl)
    (by
      show (-2 + (2 : ℤ) ^ (t + 2)) ≡ 2 [ZMOD 4]
      have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ (t + 2) := by
        have h : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ (t + 2) := pow_dvd_pow 2 (by omega)
        norm_num at h ⊢
        exact h
      rw [Int.modEq_iff_dvd]
      have h : (4 : ℤ) ∣ 2 - (-2 + (2 : ℤ) ^ (t + 2)) := by
        rw [show 2 - (-2 + (2 : ℤ) ^ (t + 2)) = 4 - (2 : ℤ) ^ (t + 2) by ring]
        exact dvd_sub (dvd_refl (4 : ℤ)) h4
      exact h)
    (by
      show Odd (1 : ℤ)
      norm_num)
    (by
      show Even (2 : ℤ)
      norm_num)
    (by
      show Even (2 : ℤ)
      norm_num)
  exact hres

theorem deviation_form_diag_t111 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {t : ℕ} (hτ : Z.τ = StrothTypeIndex.t111 t)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (t + 2)) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (t + 2)) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t111 t, dataD, hL, hcentS⟩ with hZ'
  have hres := deviation_form_diag_familyOne Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by intro i j; rfl)
    (by
      show (-2 + (2 : ℤ) ^ (t + 2)) ≡ 2 [ZMOD 4]
      have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ (t + 2) := by
        have h : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ (t + 2) := pow_dvd_pow 2 (by omega)
        norm_num at h ⊢
        exact h
      rw [Int.modEq_iff_dvd]
      have h : (4 : ℤ) ∣ 2 - (-2 + (2 : ℤ) ^ (t + 2)) := by
        rw [show 2 - (-2 + (2 : ℤ) ^ (t + 2)) = 4 - (2 : ℤ) ^ (t + 2) by ring]
        exact dvd_sub (dvd_refl (4 : ℤ)) h4
      exact h)
    (by
      show Odd (1 : ℤ)
      norm_num)
    (by
      show Even (2 : ℤ)
      norm_num)
    (by
      show Even ((2 : ℤ) + 2 ^ (t + 2))
      simp +decide [parity_simps])
  exact hres


theorem deviation_form_diag_t120 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {m : ℕ} (hm : 3 ≤ m) (hτ : Z.τ = StrothTypeIndex.t120 m hm)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ m) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ m) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t120 m hm, dataD, hL, hcentS⟩ with hZ'
  have hodd : Odd (Type120.iV (m + 1)) := by
    obtain ⟨hi, -⟩ := Type120.data m (by omega : 1 ≤ m)
    rw [hi]
    exact ⟨4 * Type120.GV (m + 1) + 9, by ring⟩
  have hres := deviation_form_diag_familyOne Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
      Type120.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
      Type120.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
      Type120.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
      Type120.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
      Type120.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
      Type120.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by intro i j; rfl)
    (by
      have hval : Z'.τ.action.uv 1 0 = 2 := by
        simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
          Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval])
    (by
      have hval : Z'.τ.action.uv 1 1 = -(5 * Type120.iV (m + 1)) := by
        simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
          Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      simpa [neg_mul] using Odd.mul (⟨-3, by ring⟩ : Odd (-5 : ℤ)) hodd)
    (by
      have hval : Z'.τ.action.uv 0 1 =
          2 * Type120.FV (m + 1) * Type120.iV (m + 1) := by
        simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
          Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      exact ⟨Type120.FV (m + 1) * Type120.iV (m + 1), by ring⟩)
    (by
      have hval : Z'.τ.action.uv 2 1 = 2 * Type120.iV (m + 1) := by
        simp [Z', StrothTypeIndex.action, Type120.actionPaper, Type120.action,
          Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      exact ⟨Type120.iV (m + 1), by ring⟩)
  exact hres


theorem deviation_form_diag_t121 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {m : ℕ} (hm : 3 ≤ m) (hτ : Z.τ = StrothTypeIndex.t121 m hm)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ m) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ m) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t121 m hm, dataD, hL, hcentS⟩ with hZ'
  have hodd : Odd (Type120.iV (m + 1)) := by
    obtain ⟨hi, -⟩ := Type120.data m (by omega : 1 ≤ m)
    rw [hi]
    exact ⟨4 * Type120.GV (m + 1) + 9, by ring⟩
  have hres := deviation_form_diag_familyOne Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
      Type121.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
      Type121.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
      Type121.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
      Type121.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
      Type121.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
      Type121.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by intro i j; rfl)
    (by
      have hval : Z'.τ.action.uv 1 0 = 2 := by
        simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
          Type121.uvM, Type121.uvA, Type121.tM, Type121.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval])
    (by
      have hval : Z'.τ.action.uv 1 1 = -(5 * Type120.iV (m + 1)) := by
        simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
          Type121.uvM, Type121.uvA, Type121.tM, Type121.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      simpa [neg_mul] using Odd.mul (⟨-3, by ring⟩ : Odd (-5 : ℤ)) hodd)
    (by
      have hval : Z'.τ.action.uv 0 1 =
          2 * Type120.FV (m + 1) * Type120.iV (m + 1) := by
        simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
          Type121.uvM, Type121.uvA, Type121.tM, Type121.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      exact ⟨Type120.FV (m + 1) * Type120.iV (m + 1), by ring⟩)
    (by
      have hval : Z'.τ.action.uv 2 1 =
          2 * Type120.iV (m + 1) + (2 : ℤ) ^ m := by
        simp [Z', StrothTypeIndex.action, Type121.actionPaper, Type121.action,
          Type121.uvM, Type121.uvA, Type121.tM, Type121.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      refine even_iff_two_dvd.mpr (dvd_add ⟨Type120.iV (m + 1), by ring⟩ ?_)
      have h : (2 : ℤ) ^ 1 ∣ (2 : ℤ) ^ m := pow_dvd_pow 2 (by omega)
      simpa using h)
  exact hres


theorem deviation_form_diag_t130 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {m : ℕ} (hm : 3 ≤ m) (hτ : Z.τ = StrothTypeIndex.t130 m hm)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ m) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ m) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t130 m hm, dataD, hL, hcentS⟩ with hZ'
  have hodd : Odd (Type120.iV (m + 1)) := by
    obtain ⟨hi, -⟩ := Type120.data m (by omega : 1 ≤ m)
    rw [hi]
    exact ⟨4 * Type120.GV (m + 1) + 9, by ring⟩
  have hres := deviation_form_diag_familyOne Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
      Type130.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
      Type130.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
      Type130.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
      Type130.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
      Type130.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
      Type130.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by intro i j; rfl)
    (by
      have hval : Z'.τ.action.uv 1 0 = 2 + (2 : ℤ) ^ m := by
        simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
          Type130.uvM, Type130.uvA, Type130.tM, Type130.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      rw [Int.modEq_iff_dvd]
      have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ m := by
        have h : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ m := pow_dvd_pow 2 (by omega)
        norm_num at h ⊢
        exact h
      rw [show 2 - (2 + (2 : ℤ) ^ m) = -(2 : ℤ) ^ m by ring]
      exact dvd_neg.mpr h4)
    (by
      have hval : Z'.τ.action.uv 1 1 = -(5 * Type120.iV (m + 1)) := by
        simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
          Type130.uvM, Type130.uvA, Type130.tM, Type130.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      simpa [neg_mul] using Odd.mul (⟨-3, by ring⟩ : Odd (-5 : ℤ)) hodd)
    (by
      have hval : Z'.τ.action.uv 0 1 =
          2 * Type120.FV (m + 1) * Type120.iV (m + 1) := by
        simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
          Type130.uvM, Type130.uvA, Type130.tM, Type130.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      exact ⟨Type120.FV (m + 1) * Type120.iV (m + 1), by ring⟩)
    (by
      have hval : Z'.τ.action.uv 2 1 = 2 * Type120.iV (m + 1) := by
        simp [Z', StrothTypeIndex.action, Type130.actionPaper, Type130.action,
          Type130.uvM, Type130.uvA, Type130.tM, Type130.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      exact ⟨Type120.iV (m + 1), by ring⟩)
  exact hres


theorem deviation_form_diag_t131 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {m : ℕ} (hm : 3 ≤ m) (hτ : Z.τ = StrothTypeIndex.t131 m hm)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ m) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ m) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t131 m hm, dataD, hL, hcentS⟩ with hZ'
  have hodd : Odd (Type120.iV (m + 1)) := by
    obtain ⟨hi, -⟩ := Type120.data m (by omega : 1 ≤ m)
    rw [hi]
    exact ⟨4 * Type120.GV (m + 1) + 9, by ring⟩
  have hres := deviation_form_diag_familyOne Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
      Type131.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
      Type131.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
      Type131.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
      Type131.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
      Type131.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
      Type131.uM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by intro i j; rfl)
    (by
      have hval : Z'.τ.action.uv 1 0 = 2 + (2 : ℤ) ^ m := by
        simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
          Type131.uvM, Type131.uvA, Type131.tM, Type131.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      rw [Int.modEq_iff_dvd]
      have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ m := by
        have h : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ m := pow_dvd_pow 2 (by omega)
        norm_num at h ⊢
        exact h
      rw [show 2 - (2 + (2 : ℤ) ^ m) = -(2 : ℤ) ^ m by ring]
      exact dvd_neg.mpr h4)
    (by
      have hval : Z'.τ.action.uv 1 1 = -(5 * Type120.iV (m + 1)) := by
        simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
          Type131.uvM, Type131.uvA, Type131.tM, Type131.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      simpa [neg_mul] using Odd.mul (⟨-3, by ring⟩ : Odd (-5 : ℤ)) hodd)
    (by
      have hval : Z'.τ.action.uv 0 1 =
          2 * Type120.FV (m + 1) * Type120.iV (m + 1) := by
        simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
          Type131.uvM, Type131.uvA, Type131.tM, Type131.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      exact ⟨Type120.FV (m + 1) * Type120.iV (m + 1), by ring⟩)
    (by
      have hval : Z'.τ.action.uv 2 1 =
          2 * Type120.iV (m + 1) + (2 : ℤ) ^ m := by
        simp [Z', StrothTypeIndex.action, Type131.actionPaper, Type131.action,
          Type131.uvM, Type131.uvA, Type131.tM, Type131.ρM, ofCols_apply,
          SigmaFourAction.ofMatEq]
      rw [hval]
      refine even_iff_two_dvd.mpr (dvd_add ⟨Type120.iV (m + 1), by ring⟩ ?_)
      have h : (2 : ℤ) ^ 1 ∣ (2 : ℤ) ^ m := pow_dvd_pow 2 (by omega)
      simpa using h)
  exact hres


theorem deviation_form_diag_familyOne_all (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D)
    (hfam : (∃ m : ℕ, Z.τ = StrothTypeIndex.t100 m) ∨
      (∃ n : ℕ, Z.τ = StrothTypeIndex.t101 n) ∨
      (∃ t : ℕ, Z.τ = StrothTypeIndex.t110 t) ∨
      (∃ t : ℕ, Z.τ = StrothTypeIndex.t111 t) ∨
      (∃ (m : ℕ) (hm : 3 ≤ m), Z.τ = StrothTypeIndex.t120 m hm) ∨
      (∃ (m : ℕ) (hm : 3 ≤ m), Z.τ = StrothTypeIndex.t121 m hm) ∨
      (∃ (m : ℕ) (hm : 3 ≤ m), Z.τ = StrothTypeIndex.t130 m hm) ∨
      (∃ (m : ℕ) (hm : 3 ≤ m), Z.τ = StrothTypeIndex.t131 m hm)) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ Z.τ.m) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ Z.τ.m) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  rcases hfam with ⟨m, hτ⟩ | ⟨n, hτ⟩ | ⟨t, hτ⟩ | ⟨t, hτ⟩ |
    ⟨m, hm, hτ⟩ | ⟨m, hm, hτ⟩ | ⟨m, hm, hτ⟩ | ⟨m, hm, hτ⟩
  · have hmexp : Z.τ.m = m := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  · have hmexp : Z.τ.m = n + 1 := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag_t101 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  · have hmexp : Z.τ.m = t + 2 := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag_t110 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  · have hmexp : Z.τ.m = t + 2 := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag_t111 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  · have hmexp : Z.τ.m = m := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag_t120 Z hk hrel hm hτ F hDF hF hN hidx hcent hsF hsD
  · have hmexp : Z.τ.m = m := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag_t121 Z hk hrel hm hτ F hDF hF hN hidx hcent hsF hsD
  · have hmexp : Z.τ.m = m := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag_t130 Z hk hrel hm hτ F hDF hF hN hidx hcent hsF hsD
  · have hmexp : Z.τ.m = m := by
      rw [hτ]
      rfl
    rw [hmexp]
    exact deviation_form_diag_t131 Z hk hrel hm hτ F hDF hF hN hidx hcent hsF hsD
end CFSG.CGT.Stroth77

end
