module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs

public section

namespace CFSG.QuasithinUnique.Fin257

namespace L3

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover

open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def dMat (t₁ t₂ : Fˣ) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![(t₁ : F), (t₂ : F), (((t₁ * t₂)⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩

theorem coe_dMat (t₁ t₂ : Fˣ) : (dMat t₁ t₂ : Matrix (Fin 3) (Fin 3) F) =
    Matrix.diagonal ![(t₁ : F), (t₂ : F), (((t₁ * t₂)⁻¹ : Fˣ) : F)] := rfl

theorem isDiag_dMat (t₁ t₂ : Fˣ) : Matrix.IsDiag (dMat t₁ t₂ : Matrix (Fin 3) (Fin 3) F) := by
  rw [coe_dMat]
  exact Matrix.isDiag_diagonal _

theorem dMat_mul (t₁ t₂ s₁ s₂ : Fˣ) :
    (dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) F) * dMat s₁ s₂ = dMat (t₁ * s₁) (t₂ * s₂) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp
  ring

theorem dMat_one : (dMat 1 1 : Matrix.SpecialLinearGroup (Fin 3) F) = 1 := by
  apply Subtype.ext
  rw [coe_dMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem dMat_pow (t₁ t₂ : Fˣ) (k : ℕ) :
    (dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) F) ^ k = dMat (t₁ ^ k) (t₂ ^ k) := by
  induction k with
  | zero => simp [dMat_one]
  | succ k ih => rw [pow_succ, ih, dMat_mul, pow_succ, pow_succ]

theorem dMat_mul_wMat (t₁ t₂ : Fˣ) (c : F) :
    (dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) F) * wMat c =
      wMat ((t₁ : F) * t₁ * t₂ * c) * dMat t₁ t₂ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dMat]
  change Matrix.diagonal _ * wM c = wM _ * Matrix.diagonal _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, Matrix.mul_apply, Matrix.diagonal_apply]
  field_simp

theorem dP_conj_wP [CharP F 2] (t₁ t₂ : Fˣ) (c : F) :
    proj 3 F (dMat t₁ t₂) * wP c * (proj 3 F (dMat t₁ t₂))⁻¹ = wP ((t₁ : F) * t₁ * t₂ * c) := by
  have h : proj 3 F (dMat t₁ t₂) * wP c = wP ((t₁ : F) * t₁ * t₂ * c) * proj 3 F (dMat t₁ t₂) := by
    have := congrArg (proj 3 F) (dMat_mul_wMat t₁ t₂ c)
    rwa [map_mul, map_mul] at this
  rw [h]
  group

theorem proj_dMat_eq_one {t₁ t₂ : Fˣ} (h : proj 3 F (dMat t₁ t₂) = 1) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧ (t₁ : F) = c ∧ (t₂ : F) = c := by
  obtain ⟨c, hc, hmat⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  refine ⟨c, hc, ?_, ?_⟩
  · have := congrFun (congrFun hmat 0) 0
    simpa [coe_dMat] using this
  · have := congrFun (congrFun hmat 1) 1
    simpa [coe_dMat] using this

theorem wP_injective [CharP F 2] {a b : F} (h : wP a = wP b) : a = b := by
  have h1 : wP (a + b) = 1 := by
    rw [wP_add, h, wP_mul_self]
  have h2 := (wP_eq_one_iff (a + b)).mp h1
  linear_combination h2 + (-(b : F)) * (CharP.cast_eq_zero F 2)

theorem exists_torus_element [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) {t : Fˣ}
    (ht : orderOf t = p) :
    ∃ h ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)), (∃ k : ℕ, orderOf h = p ^ k) ∧
      ¬ ⁅(V1 : Subgroup (projectiveSL 3 F)), V2⁆ ≤ Subgroup.centralizer ({h} : Set (projectiveSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htp : t ^ p = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  refine ⟨proj 3 F (dMat t 1), ?_, ?_, ?_⟩
  · rw [(sylow_normalizers (K := F) (n := 3) 2 (by norm_num)).2.1]
    refine ⟨dMat t 1, ?_, rfl⟩
    intro i j hij
    have := isDiag_dMat (F := F) t 1 (ne_of_gt hij)
    exact this
  · have hpow : (proj 3 F (dMat t 1)) ^ p = 1 := by
      rw [← map_pow, dMat_pow, htp, one_pow, dMat_one, map_one]
    have hd : orderOf (proj 3 F (dMat t 1)) ∣ p := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  · intro hle
    have hw : wP (1 : F) ∈ ⁅(V1 : Subgroup (projectiveSL 3 F)), V2⁆ := by
      have h1 : xP (1 : F) ∈ (V1 : Subgroup (projectiveSL 3 F)) :=
        ⟨1, 0, by rw [wP_zero (F := F), mul_one]⟩
      have h2 : yP (1 : F) ∈ (V2 : Subgroup (projectiveSL 3 F)) :=
        ⟨1, 0, by rw [wP_zero (F := F), mul_one]⟩
      have := Subgroup.commutator_mem_commutator h1 h2
      rwa [commutatorElement_xP_yP, mul_one] at this
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    have h3 : proj 3 F (dMat t 1) * wP (1 : F) * (proj 3 F (dMat t 1))⁻¹ = wP 1 := by
      rw [← hc]
      group
    rw [dP_conj_wP] at h3
    have h4 := wP_injective h3
    have h5 : ((t : F) - 1) ^ 2 = 0 := by
      simp only [Units.val_one, mul_one] at h4
      linear_combination h4 + (1 - (t : F)) * (CharP.cast_eq_zero F 2)
    have h6 : (t : F) = 1 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h5
      linear_combination this
    have h7 : t = 1 := Units.ext (by simpa using h6)
    rw [h7, orderOf_one] at ht
    exact hp.one_lt.ne ht

theorem exists_prime_ne_three_dvd (n : ℕ) (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ p ∣ 2 ^ n - 1 := by
  have h8 : (2 ^ n - 1) % 8 = 7 := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    have h1 : 2 ^ (j + 3) = 8 * 2 ^ j := by ring
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    omega
  have hm0 : 2 ^ n - 1 ≠ 0 := by
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨k, r, hr3, hkr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  by_cases hr1 : r = 1
  · exfalso
    subst hr1
    have h3k : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ]; omega
    rw [mul_one] at hkr
    have := h3k k
    omega
  · have hr0 : r ≠ 0 := by
      rintro rfl
      exact hm0 (by simpa using hkr)
    refine ⟨r.minFac, Nat.minFac_prime hr1, ?_, ?_⟩
    · intro h
      exact hr3 (h ▸ Nat.minFac_dvd r)
    · exact (Nat.minFac_dvd r).trans (Dvd.intro_left _ hkr.symm)

theorem exists_P0_ne_three [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {t : Fˣ}
    (ht : orderOf t = p) :
    ∃ P₀ : Subgroup (projectiveSL 3 F), IsElemAbelian p P₀ ∧ Nat.card P₀ = p ^ 2 := by
  have htp : t ^ p = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr hp3
  have key : ∀ i j : ℕ, (proj 3 F (dMat t 1)) ^ i * (proj 3 F (dMat 1 t)) ^ j =
      proj 3 F (dMat (t ^ i) (t ^ j)) := by
    intro i j
    rw [← map_pow, ← map_pow, ← map_mul, dMat_pow, dMat_pow, dMat_mul]
    simp
  have hab : proj 3 F (dMat t 1) * proj 3 F (dMat 1 t) = proj 3 F (dMat 1 t) * proj 3 F (dMat t 1) := by
    rw [← map_mul, ← map_mul, dMat_mul, dMat_mul]
    simp
  have ha : (proj 3 F (dMat t 1)) ^ p = 1 := by
    rw [← map_pow, dMat_pow, htp, one_pow, dMat_one, map_one]
  have hb : (proj 3 F (dMat 1 t)) ^ p = 1 := by
    rw [← map_pow, dMat_pow, htp, one_pow, dMat_one, map_one]
  have hind : ∀ i j : ℕ, (proj 3 F (dMat t 1)) ^ i * (proj 3 F (dMat 1 t)) ^ j = 1 →
      p ∣ i ∧ p ∣ j := by
    intro i j hij
    rw [key] at hij
    obtain ⟨c, hc3, hi, hj⟩ := proj_dMat_eq_one hij
    have hi' : (t ^ i) ^ 3 = 1 := by
      rw [show t ^ i = c from Units.ext hi]
      exact hc3
    have hj' : (t ^ j) ^ 3 = 1 := by
      rw [show t ^ j = c from Units.ext hj]
      exact hc3
    rw [← pow_mul] at hi' hj'
    have hi'' := ht ▸ orderOf_dvd_of_pow_eq_one hi'
    have hj'' := ht ▸ orderOf_dvd_of_pow_eq_one hj'
    exact ⟨hcop.dvd_of_dvd_mul_right hi'', hcop.dvd_of_dvd_mul_right hj''⟩
  obtain ⟨P₀, h1, h2, -, -⟩ := exists_elemAbelian_pair hp hab ha hb hind
  exact ⟨P₀, h1, h2⟩

@[expose] def cMat : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem coe_cMat : ((cMat : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem cMat_pow_three : (cMat : Matrix.SpecialLinearGroup (Fin 3) F) ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_three]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_cMat, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem cMat_mul_dMat {ω : Fˣ} (hω : ω ^ 3 = 1) :
    (cMat : Matrix.SpecialLinearGroup (Fin 3) F) * dMat ω 1 =
      scalarElement ω hω * (dMat ω 1 * cMat) := by
  have hω' : (ω : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
  have hne : (ω : F) ≠ 0 := ω.ne_zero
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, coe_dMat, coe_cMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  field_simp
  exact hω'.symm

theorem cMat_pow_entry (j : ℕ) (hj : j % 3 ≠ 0) :
    (((cMat : Matrix.SpecialLinearGroup (Fin 3) F) ^ j : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by
  have h := pow_mod_eq (cMat_pow_three (F := F)) j
  rw [h]
  have : j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases this with h1 | h1 <;> rw [h1] <;>
    simp [coe_cMat, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem exists_P0_three [Finite F] [CharP F 2] {ω : Fˣ} (hω : orderOf ω = 3) :
    ∃ P₀ : Subgroup (projectiveSL 3 F), IsElemAbelian 3 P₀ ∧ Nat.card P₀ = 3 ^ 2 := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hab : proj 3 F (dMat ω 1) * proj 3 F cMat = proj 3 F cMat * proj 3 F (dMat ω 1) := by
    have h := congrArg (proj 3 F) (cMat_mul_dMat (F := F) hω3)
    rw [map_mul, map_mul, map_mul,
      (proj_eq_one_iff).mpr (scalarElement_mem_scalars ω hω3), one_mul] at h
    exact h.symm
  have ha : (proj 3 F (dMat ω 1)) ^ 3 = 1 := by
    rw [← map_pow, dMat_pow, hω3, one_pow, dMat_one, map_one]
  have hb : (proj 3 F (cMat : Matrix.SpecialLinearGroup (Fin 3) F)) ^ 3 = 1 := by
    rw [← map_pow, cMat_pow_three, map_one]
  have hind : ∀ i j : ℕ, (proj 3 F (dMat ω 1)) ^ i * (proj 3 F (cMat : Matrix.SpecialLinearGroup
      (Fin 3) F)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
    intro i j hij
    rw [← map_pow, ← map_pow, ← map_mul, dMat_pow] at hij
    by_cases hj : j % 3 = 0
    · have hcj : (cMat : Matrix.SpecialLinearGroup (Fin 3) F) ^ j = 1 := by
        rw [pow_mod_eq cMat_pow_three j, hj, pow_zero]
      rw [hcj, mul_one] at hij
      obtain ⟨c, hc3, hc1, hc2⟩ := proj_dMat_eq_one hij
      have h1 : ((1 : Fˣ) ^ i : Fˣ) = 1 := one_pow i
      rw [h1] at hc2
      have : ((ω ^ i : Fˣ) : F) = 1 := by rw [hc1, ← hc2]; simp
      have h2 : ω ^ i = 1 := Units.ext (by simpa using this)
      exact ⟨hω ▸ orderOf_dvd_of_pow_eq_one h2, Nat.dvd_of_mod_eq_zero hj⟩
    · exfalso
      obtain ⟨c, hc3, hmat⟩ := mem_scalars.mp (proj_eq_one_iff.mp hij)
      have h1 := congrFun (congrFun hmat 0) 0
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_dMat, Matrix.diagonal_mul] at h1
      have h2 := cMat_pow_entry (F := F) j hj
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
      rw [h2] at h1
      simp at h1
      exact c.ne_zero h1.symm
  obtain ⟨P₀, h1, h2, -, -⟩ := exists_elemAbelian_pair Nat.prime_three hab ha hb hind
  exact ⟨P₀, h1, h2⟩

theorem torus_L3 [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (∃ P₀ : Subgroup (projectiveSL 3 F), IsElemAbelian p P₀ ∧ Nat.card P₀ = p ^ 2) ∧
      ∃ h ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
          Set (projectiveSL 3 F)), (∃ k : ℕ, orderOf h = p ^ k) ∧
        ¬ ⁅(V1 : Subgroup (projectiveSL 3 F)), V2⁆ ≤
          Subgroup.centralizer ({h} : Set (projectiveSL 3 F)) := by
  have hcard : Nat.card Fˣ = 2 ^ n - 1 := by rw [Nat.card_units, hF]
  by_cases hn2 : n = 2
  · subst hn2
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card Fˣ := by rw [hcard]; norm_num
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨P₀, hP₀⟩ := exists_P0_three (F := F) hω
    obtain ⟨h, hh, hk, hc⟩ := exists_torus_element (F := F) Nat.prime_three hω
    exact ⟨3, Nat.prime_three, by norm_num, ⟨P₀, hP₀⟩, h, hh, hk, hc⟩
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_ne_three_dvd n hn3
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2 : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
      obtain ⟨k, hk⟩ := hpd
      omega
    have : Fact p.Prime := ⟨hp⟩
    have hpc : p ∣ Nat.card Fˣ := by rw [hcard]; exact hpd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hpc
    obtain ⟨P₀, hP₀⟩ := exists_P0_ne_three (F := F) hp hp3 ht
    obtain ⟨h, hh, hk, hc⟩ := exists_torus_element (F := F) hp ht
    exact ⟨p, hp, hp2, ⟨P₀, hP₀⟩, h, hh, hk, hc⟩

end L3

end CFSG.QuasithinUnique.Fin257
