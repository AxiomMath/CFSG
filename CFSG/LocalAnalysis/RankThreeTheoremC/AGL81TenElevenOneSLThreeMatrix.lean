module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiFixed
import CFSG.RankThree.PartTwo.Sec4.LThreePiRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThreeGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K] {p f : ℕ}

theorem exists_conj_eq_of_cube {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {y₁ y₂ : GL (Fin 3) K}
    (h₁ : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1)
    (h₂ : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ g : GL (Fin 3) K, g⁻¹ * y₂ * g = y₁ := by
  set v : Fin 3 → K := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v] at this
  have hP₁ := isUnit_colMat (linearIndependent_cyclic hℓ h₁ hv)
  have hP₂ := isUnit_colMat (linearIndependent_cyclic hℓ h₂ hv)
  have e₁ := mul_colMat_cyclic h₁ v
  have e₂ := mul_colMat_cyclic h₂ v
  set P₁ := colMat ![v, (y₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ v,
    ((y₁ : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v]
  set P₂ := colMat ![v, (y₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ v,
    ((y₂ : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v]
  have k₂ : ((hP₂.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (y₂ : Matrix (Fin 3) (Fin 3) K) * P₂ = companionThree ℓ := by
    rw [Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, IsUnit.val_inv_mul, Matrix.one_mul]
  have k₁ : P₁ * companionThree ℓ * ((hP₁.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      y₁ := by
    rw [← e₁, Matrix.mul_assoc, IsUnit.mul_val_inv, Matrix.mul_one]
  refine ⟨hP₂.unit * hP₁.unit⁻¹, Units.ext ?_⟩
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    IsUnit.unit_spec, IsUnit.unit_spec, ← k₁, ← k₂]
  simp only [Matrix.mul_assoc]

theorem exists_slThree_conj_eq_of_cube (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {y₁ y₂ : GL (Fin 3) K}
    (h₁ : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1)
    (h₂ : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ m ∈ slPi true 3 (p ^ f) K, m⁻¹ * y₂ * m = y₁ := by
  obtain ⟨g, hg⟩ := exists_conj_eq_of_cube hℓ h₁ h₂
  have hdet := range_detCent hK hq (mem_glPi_true _ y₁) hℓ h₁
  have hgd : GeneralLinearGroup.det g⁻¹ ∈ rootsOfUnity (qSubPi true (p ^ f)) K :=
    det_mem_rootsOfUnity hK (mem_glPi_true _ _)
  obtain ⟨⟨u, hu⟩, hu'⟩ : (⟨_, hgd⟩ : rootsOfUnity (qSubPi true (p ^ f)) K) ∈
      (detCent hK y₁).range := by
    rw [hdet]
    exact mem_top _
  have hdu : GeneralLinearGroup.det u = GeneralLinearGroup.det g⁻¹ :=
    congrArg Subtype.val hu'
  have huy : u * y₁ = y₁ * u := mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2
  refine ⟨g * u, ?_, ?_⟩
  · rw [mem_slPi_true, ← GeneralLinearGroup.val_det_apply, map_mul, hdu, ← map_mul,
      mul_inv_cancel, map_one, Units.val_one]
  · calc (g * u)⁻¹ * y₂ * (g * u) = u⁻¹ * (g⁻¹ * y₂ * g) * u := by group
      _ = u⁻¹ * (y₁ * u) := by rw [hg, mul_assoc]
      _ = y₁ := by rw [← huy]; group

theorem exists_pow_mod_three {f₀ : ℕ} (hq₀ : ModThree true (p ^ f₀)) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard true (p ^ f₀)) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) :
    ∃ r : ℕ, r % 3 = 1 ∧ ∀ c, ψ c = c ^ r := by
  have h1 : (p ^ f₀) % 3 = 1 := hq₀
  rcases hψ with rfl | rfl
  · exact ⟨p ^ f₀, h1, hφ⟩
  · refine ⟨(p ^ f₀) ^ 2, by rw [Nat.pow_mod, h1], fun c => ?_⟩
    rw [ringAut_sq_apply, hφ, hφ, ← pow_mul, pow_two]
    rfl

theorem exists_slThree_frob_conj (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {ψ : K ≃+* K} {r : ℕ} (hr : r % 3 = 1) (hψ : ∀ c, ψ c = c ^ r) {ℓ : K}
    (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {y : GL (Fin 3) K}
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ m ∈ slPi true 3 (p ^ f) K, m⁻¹ * frobGL ψ y * m * y⁻¹ ∈ StatedScalars (Fin 3) K := by
  have hℓ0 : ℓ ≠ 0 := fun h => hℓ 0 (by rw [h]; ring)
  set μ : Kˣ := Units.mk0 (ℓ ^ (r / 3)) (pow_ne_zero _ hℓ0) with hμ
  have hψℓ : ψ ℓ = (μ : K) ^ 3 * ℓ := by
    have e : r = 3 * (r / 3) + 1 := by omega
    calc ψ ℓ = ℓ ^ (3 * (r / 3) + 1) := by rw [hψ, ← e]
      _ = (ℓ ^ (r / 3)) ^ 3 * ℓ := by ring
      _ = (μ : K) ^ 3 * ℓ := by rw [hμ, Units.val_mk0]
  set s := GeneralLinearGroup.scalar (Fin 3) μ with hs
  have hcs : ∀ g : GL (Fin 3) K, g * s = s * g := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ g).eq
  set y₂ := frobGL ψ y * s⁻¹ with hy₂
  have hF3 : ((frobGL ψ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = ψ ℓ • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, coe_frobGL, Units.val_pow_eq_pow_val, hy]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h₂ : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1 := by
    have hc : Commute (frobGL ψ y) s⁻¹ := (show Commute (frobGL ψ y) s from hcs _).inv_right
    rw [← Units.val_pow_eq_pow_val, hy₂, hc.mul_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      hF3, ← map_inv, ← map_pow, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      hψℓ, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    congr 1
    have := μ.ne_zero
    field_simp
  obtain ⟨m, hm, hmy⟩ := exists_slThree_conj_eq_of_cube hK hq hℓ hy h₂
  refine ⟨m, hm, ⟨μ, ?_⟩⟩
  have hyinv : y⁻¹ = m⁻¹ * y₂⁻¹ * m := by rw [← hmy]; group
  rw [← hs, hyinv, hy₂]
  calc s = m⁻¹ * (frobGL ψ y * s) * (frobGL ψ y)⁻¹ * m := by
        rw [hcs (frobGL ψ y), show m⁻¹ * (s * frobGL ψ y) * (frobGL ψ y)⁻¹ * m = m⁻¹ * s * m by
          group, hcs m⁻¹]
        group
    _ = m⁻¹ * frobGL ψ y * m * (m⁻¹ * (frobGL ψ y * s⁻¹)⁻¹ * m) := by group

@[expose] def transvOne (c : K) : GL (Fin 3) K :=
  ⟨!![1, c, 0; 0, 1, 0; 0, 0, 1], !![1, -c, 0; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_transvOne (c : K) :
    ((transvOne c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, c, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem not_forall_frobGL_eq_conj {q : ℕ} {ψ : K ≃+* K} {c : K} (hc : ψ c ≠ c)
    (y : GL (Fin 3) K) : ¬ ∀ s ∈ slPi true 3 q K, frobGL ψ s = y * s * y⁻¹ := by
  intro h
  have hmem : ∀ d : K, transvOne d ∈ slPi true 3 q K := fun d => by
    rw [mem_slPi_true, coe_transvOne, det_fin_three]
    simp
  have hfr : ∀ d : K, ((frobGL ψ (transvOne d) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, ψ d, 0; 0, 1, 0; 0, 0, 1] := fun d => by
    rw [coe_frobGL, coe_transvOne]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  set M : Matrix (Fin 3) (Fin 3) K := (y : Matrix (Fin 3) (Fin 3) K)
  set Mi : Matrix (Fin 3) (Fin 3) K := ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hMMi : M * Mi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hT : ∀ d : K, (!![1, d, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) =
      1 + d • ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) - 1) := fun d => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h1 := congrArg Units.val (h _ (hmem 1))
  rw [hfr, map_one, Units.val_mul, Units.val_mul, coe_transvOne] at h1
  have hc' := congrArg Units.val (h _ (hmem c))
  rw [hfr, Units.val_mul, Units.val_mul, coe_transvOne, hT c] at hc'
  have hconj : M * (1 + c • ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) - 1)) *
      Mi = 1 + c • ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) - 1) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMMi, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hMMi, ← h1]
  rw [hconj, ← hT] at hc'
  have := congrFun (congrFun hc' 0) 1
  simp at this
  exact hc this

theorem qSubPi_cube_div_eq {q : ℕ} (hq : q % 3 = 1) (h1 : 1 < q) :
    qSubPi true (q ^ 3) / qSubPi true q = q ^ 2 + q + 1 ∧ ¬ 9 ∣ q ^ 2 + q + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hm : 0 < m := by omega
  refine ⟨?_, ?_⟩
  · change ((m + 1) ^ 3 - 1) / (m + 1 - 1) = _
    have e : (m + 1) ^ 3 = m * ((m + 1) ^ 2 + (m + 1) + 1) + 1 := by ring
    rw [e, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hm]
  · intro h9
    have h3 : (m + 1) % 9 = 1 ∨ (m + 1) % 9 = 4 ∨ (m + 1) % 9 = 7 := by omega
    have hmod : ((m + 1) ^ 2 + (m + 1) + 1) % 9 = 3 := by
      rcases h3 with h | h | h <;> simp [Nat.add_mod, Nat.pow_mod, h]
    omega

theorem mem_zpowers_of_commute_irred (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {y : GL (Fin 3) K}
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) {t : GL (Fin 3) K}
    (ht : t ∈ slPi true 3 (p ^ f) K) (htc : t * y = y * t) (ht3 : orderOf t = 3)
    {k : GL (Fin 3) K} (hk : k ∈ slPi true 3 (p ^ f) K) (hky : k * y = y * k) {n : ℕ}
    (hkn : k ^ 3 ^ n = 1) : k ∈ zpowers t := by
  have := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcyc, hcard⟩ := centralizer_slPi_cyclic hK hq (mem_glPi_true _ y) hℓ hy
  set Q := slPi true 3 (p ^ f) K ⊓ centralizer {y}
  obtain ⟨hdiv, h9⟩ := qSubPi_cube_div_eq (q := p ^ f) hq
    (Nat.one_lt_pow (by have := hK.one_le; omega) hK.prime.one_lt)
  rw [hdiv] at hcard
  have hkQ : k ∈ Q := mem_inf.mpr ⟨hk, mem_centralizer_singleton_iff.mpr hky⟩
  have htQ : t ∈ Q := mem_inf.mpr ⟨ht, mem_centralizer_singleton_iff.mpr htc⟩
  have hk3 : k ^ 3 = 1 := by
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hkn)
    have hbQ : 3 ^ b ∣ (p ^ f) ^ 2 + p ^ f + 1 := by
      rw [← hb, ← hcard]
      exact Subgroup.orderOf_dvd_natCard Q hkQ
    have hb1 : b ≤ 1 := by
      by_contra hb2
      exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ b)).trans hbQ)
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hb]
    exact pow_dvd_pow 3 hb1 |>.trans (by norm_num)
  exact mem_zpowers_of_pow_three_eq_one hcyc ht3 htQ hkQ hk3

theorem diagTau_commute_diagUnits {τ : K} (hτ : τ ^ 3 = 1) (a b c : Kˣ) :
    diagTau hτ * diagUnits a b c = diagUnits a b c * diagTau hτ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  rw [diagTau_eq_diagUnits hτ hτ0, diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b,
    mul_comm c]

theorem diagTau_not_mem_statedScalars' {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    diagTau hτ ∉ StatedScalars (Fin 3) K := by
  rintro ⟨t, ht⟩
  have h00 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) ht
  have h22 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) ht
  simp only [coe_diagTau_eq_diagonal, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h00 h22
  simp at h00 h22
  rw [h22, Units.val_one] at h00
  exact hτ1 h00.symm

theorem det_diagUnits_one_one (a : Kˣ) : GeneralLinearGroup.det (diagUnits a 1 1) = a := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp

theorem exists_slThree_conj_diagTau (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : GL (Fin 3) K}
    (hxL : x ∈ slPi true 3 (p ^ f) K) (hxs : x ∉ StatedScalars (Fin 3) K) (hx : orderOf x = 3) :
    ∃ u ∈ slPi true 3 (p ^ f) K, u⁻¹ * x * u = diagTau hτ := by
  have hxZ : x ∉ zPi true 3 (p ^ f) K := fun h =>
    hxs (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)
  obtain ⟨g, -, hg⟩ := rank3II_4_10_three hK hq hτ hτ1 hxL hxZ hx
  set D := diagUnits (GeneralLinearGroup.det g)⁻¹ 1 1 with hD
  refine ⟨g * D, ?_, ?_⟩
  · rw [mem_slPi_true, ← GeneralLinearGroup.val_det_apply, map_mul, hD, det_diagUnits_one_one,
      mul_inv_cancel, Units.val_one]
  · calc (g * D)⁻¹ * x * (g * D) = D⁻¹ * (g⁻¹ * x * g) * D := by group
      _ = D⁻¹ * (diagTau hτ * D) := by rw [hg, mul_assoc]
      _ = diagTau hτ := by rw [diagTau_commute_diagUnits, ← hD]; group

theorem exists_commute_diagTau_conj (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x : GL (Fin 3) K} {μ : Kˣ}
    (hμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) (μ ^ 3)) :
    ∃ u ∈ slPi true 3 (p ^ f) K, u ∉ StatedScalars (Fin 3) K ∧ u ^ 3 = 1 ∧ u * x = x * u := by
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  have hq' : true = false → ModThree false (p ^ f) := fun h => absurd h (by decide)
  have hτL := diagTau_mem_slPi hπ hq' hτ
  have hτs := diagTau_not_mem_statedScalars' hτ hτ1
  by_cases hxs : x ∈ StatedScalars (Fin 3) K
  · exact ⟨diagTau hτ, hτL, hτs, diagTau_pow_three hτ,
      commute_of_mem_statedScalars hxs (diagTau hτ)⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, g, -, hD⟩ :=
    exists_diag_normal_form hK hq hτ hτ1 (mem_glPi_true _ x) hxs hμ
  have hzs := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  refine ⟨g * diagTau hτ * g⁻¹, conj_mem_slPi hπ (mem_glPi_true _ g) hτL, ?_, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    apply hτs
    refine ⟨c, ?_⟩
    have : diagTau hτ = g⁻¹ * (g * diagTau hτ * g⁻¹) * g := by group
    rw [this, ← hc, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c g⁻¹).eq]
    group
  · rw [show (g * diagTau hτ * g⁻¹) ^ 3 = g * diagTau hτ ^ 3 * g⁻¹ by
      simp only [pow_succ, pow_zero, one_mul]; group, diagTau_pow_three, mul_one, mul_inv_cancel]
  ·
    have hcD : ∀ D : GL (Fin 3) K, D = diagTau hτ ∨ (∃ e : Kˣ, D = diagE e) →
        diagTau hτ * D = D * diagTau hτ := by
      rintro D (rfl | ⟨e, rfl⟩)
      · rfl
      · exact diagTau_commute_diagUnits hτ e 1 1
    have hxz : diagTau hτ * (g⁻¹ * (x * z) * g) = g⁻¹ * (x * z) * g * diagTau hτ := by
      rcases hD with hD | ⟨e, -, hD⟩
      · rw [hD]
      · rw [hD]
        exact hcD _ (Or.inr ⟨e, rfl⟩)
    have hzc : ∀ g' : GL (Fin 3) K, g' * z = z * g' := fun g' =>
      commute_of_mem_statedScalars hzs g'
    have h1 : g * diagTau hτ * g⁻¹ * (x * z) = x * z * (g * diagTau hτ * g⁻¹) := by
      calc g * diagTau hτ * g⁻¹ * (x * z) = g * (diagTau hτ * (g⁻¹ * (x * z) * g)) * g⁻¹ := by
            group
        _ = g * (g⁻¹ * (x * z) * g * diagTau hτ) * g⁻¹ := by rw [hxz]
        _ = x * z * (g * diagTau hτ * g⁻¹) := by group
    calc g * diagTau hτ * g⁻¹ * x = g * diagTau hτ * g⁻¹ * (x * z) * z⁻¹ := by group
      _ = x * z * (g * diagTau hτ * g⁻¹) * z⁻¹ := by rw [h1]
      _ = x * (z * (g * diagTau hτ * g⁻¹)) * z⁻¹ := by group
      _ = x * (g * diagTau hτ * g⁻¹ * z) * z⁻¹ := by rw [hzc (g * diagTau hτ * g⁻¹)]
      _ = x * (g * diagTau hτ * g⁻¹) := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
