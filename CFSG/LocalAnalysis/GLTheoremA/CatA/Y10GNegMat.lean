module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Ug
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNeg

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GU6

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem ringEquiv_eq_id_of_iterate_five [Finite F] (hF : Nat.card F = 16) (σ : F ≃+* F)
    (h5 : ∀ x : F, (σ : F → F)^[5] x = x) (x : F) : σ x = x := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcomm : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
    RingHom.ext_zmod _ _
  let e : F ≃ₐ[ZMod 2] F :=
    AlgEquiv.ofRingEquiv (f := σ) (fun r => by
      have h := congrArg (fun g : ZMod 2 →+* F => g r) hcomm
      simpa using h)
  have hpow : ∀ (k : ℕ) (y : F), (e ^ k) y = (σ : F → F)^[k] y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', AlgEquiv.mul_apply, ih]
      rw [Function.iterate_succ_apply']
      rfl
  have he5 : e ^ 5 = 1 := by
    ext y
    rw [hpow, AlgEquiv.one_apply]
    exact h5 y
  have hfin : IsGalois (ZMod 2) F := inferInstance
  have hcard : Nat.card (F ≃ₐ[ZMod 2] F) = 4 := by
    rw [IsGalois.card_aut_eq_finrank]
    have h2 : Module.finrank (ZMod 2) F = 4 := by
      haveI : Fintype F := Fintype.ofFinite F
      have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
      rw [← Nat.card_eq_fintype_card, hF, ZMod.card] at hc
      have : (2 : ℕ) ^ 4 = 2 ^ (Module.finrank (ZMod 2) F) := by
        rw [← hc]; norm_num
      exact (Nat.pow_right_injective (le_refl 2) this).symm
    exact h2
  have h5d : orderOf e ∣ 5 := orderOf_dvd_of_pow_eq_one he5
  have h4d : orderOf e ∣ 4 := by
    have := orderOf_dvd_natCard e
    rwa [hcard] at this
  have h1 : orderOf e = 1 := by
    have : orderOf e ∣ Nat.gcd 5 4 := Nat.dvd_gcd h5d h4d
    simpa using this
  have he : e = 1 := orderOf_eq_one_iff.1 h1
  have := congrArg (fun f : F ≃ₐ[ZMod 2] F => f x) he
  exact this


theorem exists_fifth_root_ne_one [Finite F] (hF : Nat.card F = 16) :
    ∃ ζ : F, ζ ^ 5 = 1 ∧ ζ ≠ 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcard : Nat.card Fˣ = 15 := by
    rw [Nat.card_units, hF]
  have h5 : 5 ∣ Nat.card Fˣ := by rw [hcard]; norm_num
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 h5
  refine ⟨(u : F), ?_, ?_⟩
  · have h1 : u ^ 5 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · intro h
    have h' : u = 1 := Units.ext h
    rw [h', orderOf_one] at hu
    norm_num at hu

theorem commutant_scalar [Finite F] (hF : Nat.card F = (2 ^ 2) ^ 2) (M : GL (Fin 6) F)
    (hM : ∀ x ∈ StatedSU 6 (2 ^ 2) F, M * x = x * M) :
    ∃ c : F, (M : Matrix (Fin 6) (Fin 6) F) = c • 1 := by
  obtain ⟨ζ, hζ5, hζ1⟩ := exists_fifth_root_ne_one (F := F) (by rw [hF]; norm_num)
  have hMM : ∀ x ∈ StatedSU 6 (2 ^ 2) F,
      (M : Matrix (Fin 6) (Fin 6) F) * (x : Matrix (Fin 6) (Fin 6) F) =
        (x : Matrix (Fin 6) (Fin 6) F) * (M : Matrix (Fin 6) (Fin 6) F) := by
    intro x hx
    have := congrArg Units.val (hM x hx)
    simpa using this
  have hζ3 : ζ ^ 3 ≠ 1 := by
    intro h3
    have h2 : ζ ^ 2 = 1 := by
      have h := hζ5
      rw [show (5 : ℕ) = 2 + 3 by rfl, pow_add, h3, mul_one] at h
      exact h
    apply hζ1
    have : ζ ^ 3 = ζ := by
      rw [show (3 : ℕ) = 1 + 2 by rfl, pow_add, h2, mul_one, pow_one]
    rw [← this, h3]
  have hoff : ∀ i j : Fin 6, i ≠ j → (M : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
    intro i j hij
    let t : Fin 6 → F := fun k => if k = i then ζ else if k = j then ζ ^ 4 else 1
    have ht : ∀ k, t k ≠ 0 := by
      intro k
      simp only [t]
      split_ifs
      · intro h; rw [h] at hζ5; norm_num at hζ5
      · intro h
        have h4 : ζ ^ 4 = 0 := h
        rw [pow_eq_zero_iff (by norm_num)] at h4
        rw [h4] at hζ5; norm_num at hζ5
      · exact one_ne_zero
    have ht5 : ∀ k, t k ^ 5 = 1 := by
      intro k
      simp only [t]
      split_ifs
      · exact hζ5
      · rw [← pow_mul, show 4 * 5 = 5 * 4 by norm_num, pow_mul, hζ5, one_pow]
      · exact one_pow 5
    have hdet : ∏ k, t k = 1 := by
      have hfac : ∀ k, t k = (if k = i then ζ else 1) * (if k = j then ζ ^ 4 else 1) := by
        intro k
        by_cases hki : k = i
        · subst hki
          simp [t, hij]
        · by_cases hkj : k = j
          · subst hkj; simp [t, hki]
          · simp [t, hki, hkj]
      simp_rw [hfac]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i, Finset.prod_ite_eq' Finset.univ j]
      simp only [Finset.mem_univ, if_true]
      rw [← pow_succ', show 4 + 1 = 5 by norm_num, hζ5]
    have hD := diagU_mem_SU hF ht ht5 hdet
    have hcomm := hMM _ hD
    rw [diagU_val] at hcomm
    have hentry := congrFun (congrFun hcomm i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    have hti : t i ≠ t j := by
      have h1 : t i = ζ := by simp [t]
      have h2 : t j = ζ ^ 4 := by
        have hji : j ≠ i := Ne.symm hij
        simp [t, hji]
      rw [h1, h2]
      intro h
      have hz : ζ ≠ 0 := by rintro rfl; norm_num at hζ5
      have h3 : ζ ^ 3 = 1 := by
        apply mul_left_cancel₀ hz
        linear_combination -h
      exact hζ3 h3
    have h0 : (M : Matrix (Fin 6) (Fin 6) F) i j * (t i - t j) = 0 := by
      linear_combination (-1 : F) * hentry
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 hti)
  have hmeq : ∀ i j : Fin 6, (M : Matrix (Fin 6) (Fin 6) F) i i = (M : Matrix (Fin 6) (Fin 6) F) j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have hP := hMM _ (permU_mem_SU hF (Equiv.swap i j) (fun s => Equiv.swap_apply_self i j s))
      rw [permU_val] at hP
      have hentry := congrFun (congrFun hP i) j
      have hMP : ((M : Matrix (Fin 6) (Fin 6) F) * permM (F := F) (Equiv.swap i j)) i j =
          (M : Matrix (Fin 6) (Fin 6) F) i i * permM (F := F) (Equiv.swap i j) i j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · intro k _ hk
          rw [hoff i k (fun h => hk h.symm), zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
      have hPM : (permM (F := F) (Equiv.swap i j) * (M : Matrix (Fin 6) (Fin 6) F)) i j =
          permM (F := F) (Equiv.swap i j) i j * (M : Matrix (Fin 6) (Fin 6) F) j j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · intro k _ hk
          rw [hoff k j hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hPij : permM (F := F) (Equiv.swap i j) i j = 1 := by
        simp [permM, Equiv.swap_apply_right]
      rw [hMP, hPM, hPij, mul_one, one_mul] at hentry
      exact hentry
  refine ⟨(M : Matrix (Fin 6) (Fin 6) F) 0 0, ?_⟩
  ext i k
  by_cases hik : i = k
  · subst hik
    simp [hmeq i 0]
  · rw [hoff i k hik, Matrix.smul_apply, Matrix.one_apply_ne hik, smul_zero]


theorem ringAut_pow_apply (φ : F ≃+* F) (k : ℕ) (y : F) :
    ((φ : RingAut F) ^ k) y = (⇑φ)^[k] y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Function.iterate_succ_apply, ← ih]
    rfl

theorem iterate_five_eq_id [Finite F] (hF : Nat.card F = 16) (φ : F ≃+* F) {ζ : F}
    (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (hζ : (⇑φ)^[5] ζ = ζ) (x : F) : (⇑φ)^[5] x = x := by
  rw [← ringAut_pow_apply]
  exact apply_eq_of_fix_fifth hF ((φ : RingAut F) ^ 5) hζ5 hζ1
    (by rw [ringAut_pow_apply, hζ]) x


@[expose] def U6SevenFree : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [CharP F 2] [Finite F], Nat.card F = (2 ^ 2) ^ 2 →
    ∀ A : GL (Fin 6) F,
      ((A : Matrix (Fin 6) (Fin 6) F).map (fun x : F => x ^ 4))ᵀ * (A : Matrix (Fin 6) (Fin 6) F) = 1 →
      (∃ c : F, (A : Matrix (Fin 6) (Fin 6) F) ^ 5 = c • 1) →
      (¬ ∃ c : F, (A : Matrix (Fin 6) (Fin 6) F) = c • 1) →
      ∀ y : GL (Fin 6) F, y ∈ StatedSU 6 (2 ^ 2) F → orderOf y = 7 → A * y = y * A → False


@[expose] def U6Core : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [CharP F 2] [Finite F], Nat.card F = (2 ^ 2) ^ 2 →
    ∀ B : GL (Fin 6) F,
      ((B : Matrix (Fin 6) (Fin 6) F).map (fun x : F => x ^ 4))ᵀ * (B : Matrix (Fin 6) (Fin 6) F) = 1 →
      B ^ 5 = 1 → (¬ ∃ c : F, (B : Matrix (Fin 6) (Fin 6) F) = c • 1) →
      ∀ y : GL (Fin 6) F, y ∈ StatedSU 6 (2 ^ 2) F → orderOf y = 7 → B * y = y * B → False

theorem det_map_pow_four {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n F) :
    (M.map (fun x : F => x ^ 4)).det = M.det ^ 4 := by
  have hfun : (fun x : F => x ^ 4) = ⇑(iterateFrobenius F 2 2 : F →+* F) :=
    funext (fun x => (CFSG.LocalAnalysis.GLTheoremA.SFM12.frob_apply4 x).symm)
  rw [hfun]
  have h := RingHom.map_det (iterateFrobenius F 2 2 : F →+* F) M
  rw [CFSG.LocalAnalysis.GLTheoremA.SFM12.frob_apply4] at h
  exact h.symm

theorem u6SevenFree_of_core (hcore : U6Core) : U6SevenFree := by
  intro F _ _ _ _ hF A hU hA5 hAs y hy hyo hcomm
  obtain ⟨c, hc⟩ := hA5
  set M : Matrix (Fin 6) (Fin 6) F := (A : Matrix (Fin 6) (Fin 6) F) with hMdef
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hdetA0 : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).1 A.isUnit
    exact this.ne_zero
  have hdetA : M.det ^ 5 = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_transpose, det_map_pow_four, Matrix.det_one] at h
    rw [← h]
    ring
  have hc6 : c ^ 6 = 1 := by
    have h1 : M.det ^ 5 = c ^ 6 := by
      have h := congrArg Matrix.det (show M ^ 5 = c • 1 from hc)
      rw [Matrix.det_pow, Matrix.det_smul, Matrix.det_one, mul_one] at h
      simpa using h
    rw [← h1, hdetA]
  have hc3 : c ^ 3 = 1 := by
    have : (c ^ 3 - 1) ^ 2 = 0 := by linear_combination hc6 + (1 - c ^ 3) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linear_combination this
  set B : GL (Fin 6) F := A ^ 3 with hBdef
  have hBmat : (B : Matrix (Fin 6) (Fin 6) F) = M ^ 3 := by
    rw [hBdef, Units.val_pow_eq_pow_val]
  have hB5 : B ^ 5 = 1 := by
    apply Units.ext
    rw [hBdef, ← pow_mul, Units.val_pow_eq_pow_val, Units.val_one]
    have : M ^ (3 * 5) = (M ^ 5) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [this, show (M ^ 5) = c • 1 from hc, smul_pow, one_pow, hc3, one_smul]
  have hfun : (fun x : F => x ^ 4) = ⇑(iterateFrobenius F 2 2 : F →+* F) :=
    funext (fun x => (CFSG.LocalAnalysis.GLTheoremA.SFM12.frob_apply4 x).symm)
  have hUB : ((B : Matrix (Fin 6) (Fin 6) F).map (fun x : F => x ^ 4))ᵀ * (B : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [hBmat, hfun, Matrix.map_pow, Matrix.transpose_pow]
    have hU' : ((M.map (⇑(iterateFrobenius F 2 2 : F →+* F)))ᵀ) * M = 1 := by
      rw [← hfun]
      exact hU
    have hMU' : M * (M.map (⇑(iterateFrobenius F 2 2 : F →+* F)))ᵀ = 1 := mul_eq_one_comm.1 hU'
    have hcomm' : Commute ((M.map (⇑(iterateFrobenius F 2 2 : F →+* F)))ᵀ) M := hU'.trans hMU'.symm
    rw [← hcomm'.mul_pow, hU', one_pow]
  have hcB : Commute (A : GL (Fin 6) F) y := hcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc6
  have hBns : ¬ ∃ d : F, (B : Matrix (Fin 6) (Fin 6) F) = d • 1 := by
    rintro ⟨d, hd⟩
    rw [hBmat] at hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hd
      have h0 := congrArg Matrix.det hd
      rw [Matrix.det_pow, Matrix.det_zero] at h0
      exact pow_ne_zero 3 hdetA0 h0
    have hM2 : M ^ 2 = (d⁻¹ * c) • (1 : Matrix (Fin 6) (Fin 6) F) := by
      have h1 : d • M ^ 2 = c • (1 : Matrix (Fin 6) (Fin 6) F) := by
        calc d • M ^ 2 = M ^ 2 * (d • (1 : Matrix (Fin 6) (Fin 6) F)) := by
              rw [Matrix.mul_smul, Matrix.mul_one]
          _ = M ^ 2 * M ^ 3 := by rw [hd]
          _ = M ^ 5 := by rw [← pow_add]
          _ = c • 1 := hc
      calc M ^ 2 = d⁻¹ • (d • M ^ 2) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
        _ = d⁻¹ • (c • (1 : Matrix (Fin 6) (Fin 6) F)) := by rw [h1]
        _ = (d⁻¹ * c) • (1 : Matrix (Fin 6) (Fin 6) F) := by rw [smul_smul]
    have he0 : d⁻¹ * c ≠ 0 := mul_ne_zero (inv_ne_zero hd0) hc0
    have hM1 : M = ((d⁻¹ * c)⁻¹ * d) • (1 : Matrix (Fin 6) (Fin 6) F) := by
      have h3 : M ^ 3 = (d⁻¹ * c) • M := by
        calc M ^ 3 = M * M ^ 2 := pow_succ' M 2
          _ = M * ((d⁻¹ * c) • (1 : Matrix (Fin 6) (Fin 6) F)) := by rw [hM2]
          _ = (d⁻¹ * c) • M := by rw [Matrix.mul_smul, Matrix.mul_one]
      have h4 : (d⁻¹ * c) • M = d • (1 : Matrix (Fin 6) (Fin 6) F) := by rw [← h3, hd]
      calc M = (d⁻¹ * c)⁻¹ • ((d⁻¹ * c) • M) := by rw [smul_smul, inv_mul_cancel₀ he0, one_smul]
        _ = (d⁻¹ * c)⁻¹ • (d • (1 : Matrix (Fin 6) (Fin 6) F)) := by rw [h4]
        _ = ((d⁻¹ * c)⁻¹ * d) • (1 : Matrix (Fin 6) (Fin 6) F) := by rw [smul_smul]
    exact hAs ⟨_, hM1⟩
  have hcB3 : B * y = y * B := (Commute.pow_left hcomm 3)
  exact hcore F hF B hUB hB5 hBns y hy hyo hcB3

end CFSG.LocalAnalysis.GLTheoremA.Y10GNeg
