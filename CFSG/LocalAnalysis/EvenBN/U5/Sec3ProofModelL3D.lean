module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore
import CFSG.LocalAnalysis.SteinbergSFLinearUnitaryThreeBaseField
import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
import CFSG.RankThree.PartOne.AUTSL.Interface

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5.S8c

open Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.SeitzReduction.LinearPilot
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

theorem nt_field (f : ℕ) (hf : 2 ≤ f) (N : ℕ)
    (hN : N * Nat.gcd 3 (2 ^ f + 1) = (2 ^ f) ^ 3 * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 2 - 1))
    (hd : N ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1))) : False := by
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hN hd
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqeven : 2 ∣ q := by
    rw [hq]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨s, hs⟩ : ∃ s, s = q ^ 2 - 1 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = q ^ 3 - 1 := ⟨_, rfl⟩
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have hq3 : 64 ≤ q ^ 3 := by nlinarith
  have hs1 : s + 1 = q ^ 2 := by omega
  have hr1 : r + 1 = q ^ 3 := by omega
  rw [← hs, ← hr] at hd
  rw [← hs] at hN
  have hsp : 0 < s := by omega
  have hqp : 0 < q ^ 3 := by omega
  obtain ⟨c, hc⟩ := hd
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hgp : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  set g := Nat.gcd 3 (q + 1) with hgdef
  have hmain : (r * g) * (q ^ 3 * s) = ((r + 2) * c) * (q ^ 3 * s) := by
    have h1 : q ^ 3 * (s * r) * g = N * c * g := by rw [hc]
    have h2 : N * c * g = c * (N * g) := by ring
    rw [h2, hN] at h1
    have h3 : q ^ 3 * (s * r) * g = (r * g) * (q ^ 3 * s) := by ring
    have h4 : c * (q ^ 3 * (q ^ 3 + 1) * s) = ((r + 2) * c) * (q ^ 3 * s) := by
      rw [← hr1]; ring
    rw [← h3, h1, h4]
  have hcancel : r * g = (r + 2) * c := Nat.eq_of_mul_eq_mul_right (by positivity) hmain
  have hdvd : (r + 2) ∣ r * g := ⟨c, hcancel⟩
  have hodd : Odd r := by
    rw [Nat.odd_iff]
    have : 2 ∣ q ^ 3 := dvd_pow hqeven (by norm_num)
    omega
  have hcop : Nat.Coprime (r + 2) r := by
    have h2r : Nat.Coprime 2 r := (Nat.coprime_two_left).2 hodd
    simpa [Nat.coprime_add_self_left, Nat.coprime_comm] using h2r
  have hdg : (r + 2) ∣ g := hcop.dvd_of_dvd_mul_left hdvd
  have := Nat.le_of_dvd hgp hdg
  omega

theorem nt_dual (f : ℕ) (hf : 1 ≤ f) (N : ℕ) (hv : N.factorization 2 = 3 * f)
    (hN0 : N ≠ 0) (hd : N ∣ 2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) : False := by
  have h1 : 2 ^ (3 * f) ∣ N := by
    have := Nat.ordProj_dvd N 2
    rwa [hv] at this
  have h2 : 2 ^ (3 * f) ∣ 2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1) := h1.trans hd
  have h3 : 2 ^ (2 * f) * 2 ^ f ∣ 2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1) := by
    rwa [← pow_add, show 2 * f + f = 3 * f by ring]
  have h4 : 2 ^ f ∣ (2 ^ (2 * f)) ^ 2 - 1 :=
    Nat.dvd_of_mul_dvd_mul_left (by positivity) h3
  have h5 : 2 ∣ (2 ^ (2 * f)) ^ 2 - 1 := (dvd_pow_self 2 (by omega)).trans h4
  have h6 : 2 ∣ (2 ^ (2 * f)) ^ 2 := by
    have : 2 ∣ 2 ^ (2 * f) := dvd_pow_self 2 (by omega)
    exact dvd_pow this (by norm_num)
  have h7 : 1 ≤ (2 ^ (2 * f)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

section Matrices

variable {K : Type} [Field K]

@[expose] def tmat (t : K) : Matrix (Fin 3) (Fin 3) K := !![1 + t, t, 0; t, 1 + t, 0; 0, 0, 1]

theorem tmat_mul (h2 : (2 : K) = 0) (t s : K) : tmat t * tmat s = tmat (t + s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tmat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | rfl | (linear_combination (t * s) * h2) | skip

theorem tmat_zero : tmat (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmat]

theorem tmat_transpose (t : K) : (tmat t)ᵀ = tmat t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmat]

theorem tmat_det (h2 : (2 : K) = 0) (t : K) : (tmat t).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [tmat]
  linear_combination t * h2

theorem map_tmat (φ : K →+* K) (t : K) : (tmat t).map φ = tmat (φ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmat]

variable [CharP K 2]

@[expose] def tSL (t : K) : SpecialLinearGroup (Fin 3) K := ⟨tmat t, tmat_det CharTwo.two_eq_zero t⟩

theorem coe_tSL (t : K) : (tSL t : Matrix (Fin 3) (Fin 3) K) = tmat t := rfl

theorem tSL_mul (t s : K) : tSL t * tSL s = tSL (t + s) := by
  ext i j
  have h := congrFun (congrFun (tmat_mul (K := K) CharTwo.two_eq_zero t s) i) j
  simpa [coe_tSL, SpecialLinearGroup.coe_mul] using h

theorem tSL_zero : tSL (0 : K) = 1 := by
  ext i j
  have h := congrFun (congrFun (tmat_zero (K := K)) i) j
  simpa [coe_tSL] using h

theorem tSL_self (t : K) : tSL t * tSL t = 1 := by
  rw [tSL_mul, CharTwo.add_self_eq_zero, tSL_zero]

theorem tSL_inv (t : K) : (tSL t)⁻¹ = tSL t := inv_eq_of_mul_eq_one_right (tSL_self t)

theorem transpose_tSL (t : K) : (tSL t).transpose = tSL t := by
  ext i j
  have h := congrFun (congrFun (tmat_transpose t) i) j
  simpa [coe_tSL, SpecialLinearGroup.coe_transpose] using h

theorem map_tSL (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.map σ.toRingHom (tSL t) = tSL (σ t) := by
  ext i j
  have h := congrFun (congrFun (map_tmat σ.toRingHom t) i) j
  simpa [coe_tSL, SpecialLinearGroup.map_apply_coe] using h

theorem proj_tSL_ne_one {t : K} (ht : t ≠ 0) : proj 3 K (tSL t) ≠ 1 := by
  intro h
  rw [proj_eq_one_iff, mem_scalars] at h
  obtain ⟨c, -, hc⟩ := h
  have := congrFun (congrFun hc 0) 1
  simp [coe_tSL, tmat, scalar_apply, diagonal_apply] at this
  exact ht this

theorem fieldAut_dualAut_proj_tSL (σ : K ≃+* K) (t : K) :
    (fieldAut 3 K σ * dualAut 3 K) (proj 3 K (tSL t)) = proj 3 K (tSL (σ t)) := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj, tSL_inv, transpose_tSL, map_tSL]

end Matrices

section Dihedral

variable {f : ℕ} {K : Type} [Field K]

theorem dihedral_in_P (h : UnitaryFieldData 2 f K) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    ∃ u : projectiveSL 3 K, u * u = 1 ∧ u * (fieldAut 3 K σ * dualAut 3 K) u ≠ 1 ∧
      (u * (fieldAut 3 K σ * dualAut 3 K) u) * (u * (fieldAut 3 K σ * dualAut 3 K) u) = 1 ∧
      u * (fieldAut 3 K σ * dualAut 3 K) u ∈ unitaryCore 2 f K 3 := by
  haveI : CharP K 2 := h.charP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have ht0 : c + σ c ≠ 0 := by
    intro h0
    apply hc
    rw [← hσ]
    have h1 : σ c = c := by
      have : σ c = -c := by linear_combination h0
      rw [this, CharTwo.neg_eq]
    exact h1
  have hbt : h.bar (c + σ c) = c + σ c := by
    have hbc : h.bar c = σ c := (hσ c).symm
    have hbσc : h.bar (σ c) = c := by rw [hσ c, h.bar_bar]
    rw [map_add, hbc, hbσc, add_comm]
  refine ⟨proj 3 K (tSL c), ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, tSL_self, map_one]
  · rw [fieldAut_dualAut_proj_tSL, ← map_mul, tSL_mul]
    exact proj_tSL_ne_one ht0
  · rw [fieldAut_dualAut_proj_tSL, ← map_mul, tSL_mul, ← map_mul, tSL_self, map_one]
  · rw [fieldAut_dualAut_proj_tSL, ← map_mul, tSL_mul, mem_unitaryCore]
    refine ⟨SpecialLinearGroup.toGL (tSL (c + σ c)), ?_, conjAut_toGL _⟩
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [SpecialLinearGroup.coe_GL_coe_matrix]
      exact (tSL (c + σ c)).2
    · rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_tSL, map_tmat, hbt, tmat_transpose,
        tmat_mul CharTwo.two_eq_zero, CharTwo.add_self_eq_zero, tmat_zero]

end Dihedral

section Cores

variable {f : ℕ}

theorem perfect_of_lieModel {G : Type} [Group G] {B : Subgroup G}
    (hB : LieModel B .PSU 3 2 f) : ⁅B, B⁆ = B :=
  CFSG.ComponentClassification.RankTwoHypIIY.commutator_eq_self_of_isSimpleGroup
    (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hB) (fun hc => by
      obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hB
      exact hab (hc a b))

theorem le_perfectCore_of_fix {G : Type} [Group G] {B : Subgroup G}
    (hB : LieModel B .PSU 3 2 f) (α : MulAut G) (hfix : ∀ b ∈ B, α b = b) :
    B ≤ perfectCore (autFixSubgroup α) :=
  le_perfectCore_of_perfect (fun b hb => (mem_autFixSubgroup).2 (hfix b hb)) (perfect_of_lieModel hB)

variable {K : Type} [Field K]

theorem card_fixedField_of_bar [Finite K] (hK : Nat.card K = 2 ^ (2 * f)) (σ : K ≃+* K)
    (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 = 1) :
    Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ) =
      2 ^ f := by
  have h := CFSG.SeitzReduction.LinearPilot.card_fixedField_sq hK hσ1 hσ2
  rw [hK, pow_mul'] at h
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) h

theorem field_false [Finite K] (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ (2 * f)) (σ : K ≃+* K)
    (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 = 1) (B : Subgroup (projectiveSL 3 K))
    (hB : LieModel B .PSU 3 2 f) (hfix : ∀ b ∈ B, fieldAut 3 K σ b = b) : False := by
  have hcore := le_perfectCore_of_fix hB (fieldAut 3 K σ) hfix
  rw [perfectCore_autFixSubgroup_fieldAut hK (by norm_num) σ hσ2] at hcore
  set k := CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ with hk
  set j := CFSG.RankThree.PartOne.linearSubfieldInclusion 3 k with hj
  have hkcard : Nat.card k = 2 ^ f := card_fixedField_of_bar hK σ hσ1 hσ2
  have h1 : Nat.card B ∣ Nat.card (projectiveSL 3 k) :=
    (Subgroup.card_dvd_of_le hcore).trans
      (Subgroup.card_dvd_of_surjective (MonoidHom.rangeRestrict_surjective j))
  have h2 : Nat.card (projectiveSL 3 k) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) :=
    Subgroup.card_dvd_of_surjective (proj_surjective 3 k)
  have h3 := h1.trans h2
  rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalTwoPart.card_SL_three, hkcard] at h3
  exact nt_field f hf _ (CFSG.LocalAnalysis.EvenBN.GMSK.card_mul_gcd_of_lieModel_PSU3 hB) h3

theorem dual_false [Finite K] [CharP K 2] (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ (2 * f))
    (B : Subgroup (projectiveSL 3 K)) (hB : LieModel B .PSU 3 2 f)
    (hfix : ∀ b ∈ B, dualAut 3 K b = b) : False := by
  obtain ⟨j, hj, hjr⟩ :=
    CFSG.LocalAnalysis.SymplecticFourStandard.LinearUnitaryThree.exists_SL_two_fixed_dualAut
      (F := K)
  have hle : B ≤ j.range := by
    rw [hjr]
    intro b hb
    exact hfix b hb
  have h1 : Nat.card B ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rw [Nat.card_congr (MonoidHom.ofInjective hj).symm.toEquiv]
  rw [CFSG.LocalAnalysis.SymplecticFourStandard.LinearUnitaryThree.card_SL_two, hK] at h1
  haveI := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_PSU3 hB
  exact nt_dual f hf (Nat.card B)
    (CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_PSU3 hB)
    Nat.card_pos.ne' h1

theorem lieModel_unitaryPSU (h : UnitaryFieldData 2 f K) (hadm : CFSG.Open.StatedLieAdmissible .PSU 3 2 f) :
    LieModel (unitaryPSU h 3) .PSU 3 2 f := by
  haveI := h.finite
  refine Or.inl ⟨by decide, hadm, ?_⟩
  exact ⟨K, inferInstance, h.finite, by rw [h.card, ← pow_mul, mul_comm],
    ⟨unitaryPSUEquiv h (by norm_num)⟩⟩

theorem graphField_eq [Finite K] (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = h.bar x) (B : Subgroup (projectiveSL 3 K)) (hB : LieModel B .PSU 3 2 f)
    (hfix : ∀ b ∈ B, (fieldAut 3 K σ * dualAut 3 K) b = b) : B = unitaryCore 2 f K 3 := by
  have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h32
    have h2f : 2 ^ f = 2 ^ 1 := by simpa using congrArg Prod.snd h32
    have := Nat.pow_right_injective (le_refl 2) h2f
    omega
  have hcore := le_perfectCore_of_fix hB _ hfix
  rw [perfectCore_autFixSubgroup_graphField h (by norm_num) hnq σ hσ] at hcore
  obtain ⟨E, -⟩ := exists_unitaryCoreEquiv (n := 3) h (by norm_num) σ hσ
  have hLM := lieModel_unitaryPSU h (CFSG.Blueprint.LieModel.admissible hB)
  have hgp : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hcardU : Nat.card (unitaryPSU h 3) = Nat.card B :=
    Nat.eq_of_mul_eq_mul_right hgp
      ((CFSG.LocalAnalysis.EvenBN.GMSK.card_mul_gcd_of_lieModel_PSU3 hLM).trans
        (CFSG.LocalAnalysis.EvenBN.GMSK.card_mul_gcd_of_lieModel_PSU3 hB).symm)
  exact Subgroup.eq_of_le_of_card_ge hcore (by rw [← Nat.card_congr E.toEquiv, hcardU])
end Cores

section Canonical

variable {f : ℕ}

theorem transport_conj {X P : Type} [Group X] [Group P] (e₀ : X ≃* P) (τ : MulAut X)
    (y γ : MulAut P) (hγ : MulAut.congr e₀ τ = γ * y * γ⁻¹) (x : X) :
    (e₀.trans γ⁻¹) (τ x) = y ((e₀.trans γ⁻¹) x) := by
  have h1 : e₀ (τ x) = (MulAut.congr e₀ τ) (e₀ x) := by
    simp [MulAut.congr_apply]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, hγ]
  simp [MulAut.mul_apply]

theorem canonical_form (hf : 2 ≤ f) {X : Type} [Group X] {A : Subgroup X}
    (hX : LieModel X .PSL 3 2 (2 * f)) (hA : LieModel A .PSU 3 2 f)
    {τ : MulAut X} (hτ : orderOf τ = 2) (hfix : ∀ a ∈ A, τ a = a)
    (hout : τ ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K) (σ : K ≃+* K)
      (e : X ≃* projectiveSL 3 K), (∀ x, σ x = h.bar x) ∧
      (∀ x, e (τ x) = (fieldAut 3 K σ * dualAut 3 K) (e x)) ∧
      A.map e.toMonoidHom = unitaryCore 2 f K 3 := by
  obtain ⟨K, hF, hfin, hK, ⟨e₀⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hX
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, hK⟩
  haveI : CharP K 2 := h.charP
  have hy2 : (MulAut.congr e₀ τ) ^ 2 = 1 := by
    have : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
    rw [← map_pow, this, map_one]
  have hyout : MulAut.congr e₀ τ ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    rintro ⟨p, hp⟩
    apply hout
    refine ⟨e₀.symm p, (MulAut.congr e₀).injective ?_⟩
    rw [← hp]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hbar : ∀ σ : K ≃+* K, (∀ x, σ x = x ^ 2 ^ (2 * f / 2)) → ∀ x, σ x = h.bar x :=
    fun σ hσ x => by
      rw [hσ x, h.bar_apply, Nat.mul_div_cancel_left f (by norm_num : 0 < 2)]
  have hB : ∀ e : X ≃* projectiveSL 3 K, LieModel (A.map e.toMonoidHom) .PSU 3 2 f := fun e =>
    LieModel.of_mulEquiv (A.equivMapOfInjective e.toMonoidHom e.injective) hA
  have hBfix : ∀ (e : X ≃* projectiveSL 3 K) (y : MulAut (projectiveSL 3 K)),
      (∀ x, e (τ x) = y (e x)) → ∀ b ∈ A.map e.toMonoidHom, y b = b := by
    rintro e y hey b ⟨a, ha, rfl⟩
    change y (e a) = e a
    rw [← hey, hfix a ha]
  rcases CFSG.LocalAnalysis.EvenBN.LinearThree.exists_conj_canonical_of_not_mem_range
      (f := 2 * f) (by omega) hK hy2 hyout with
    ⟨-, σ, hσx, γ, hγ⟩ | ⟨γ, hγ⟩ | ⟨-, σ, hσx, γ, hγ⟩
  · exfalso
    have hσ := hbar σ hσx
    have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [hσ, hσ, h.bar_bar]
    have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun x => by
      rw [pow_two, RingAut.mul_apply, hσσ]
      rfl
    have hσ1 : σ ≠ 1 := by
      obtain ⟨c, hc⟩ := h.exists_bar_ne
      intro h1
      apply hc
      rw [← hσ, h1]
      rfl
    have hey := transport_conj e₀ τ (fieldAut 3 K σ) γ hγ
    exact field_false hf hK σ hσ1 hσ2 _ (hB _) (hBfix _ _ hey)
  · exfalso
    have hey := transport_conj e₀ τ (dualAut 3 K) γ hγ
    exact dual_false (by omega) hK _ (hB _) (hBfix _ _ hey)
  · have hσ := hbar σ hσx
    have hey := transport_conj e₀ τ (fieldAut 3 K σ * dualAut 3 K) γ hγ
    exact ⟨K, hF, h, σ, _, hσ, hey, graphField_eq hf h σ hσ _ (hB _) (hBfix _ _ hey)⟩

end Canonical

end CFSG.LocalAnalysis.EvenBN.U5.S8c

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace CaseBParts

theorem l3Dihedral : L3DihedralStatement := by
  intro f hf X _ A hX hA τ hτ hfix hout
  obtain ⟨K, _, h, σ, e, hσ, hey, hAe⟩ := S8c.canonical_form hf hX hA hτ hfix hout
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := S8c.dihedral_in_P h σ hσ
  have hτu : τ (e.symm u) = e.symm ((LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K) u) := by
    apply e.injective
    rw [hey, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine ⟨e.symm u, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hu1, map_one]
  · rw [hτu, ← map_mul]
    intro h1
    apply hu2
    apply e.symm.injective
    rw [h1, map_one]
  · rw [hτu, ← map_mul, ← map_mul, hu3, map_one]
  · rw [hτu, ← map_mul]
    have hmem : u * (LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K) u ∈ A.map e.toMonoidHom := by
      rw [hAe]
      exact hu4
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 hmem
    have : e.symm (u * (LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K) u) = a := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact hae.symm
    rw [this]
    exact ha

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
