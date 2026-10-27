module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsModelAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.RootCenter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryExcluded
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ShultStronglyClosedTI

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (e : MulAut G) (r : G) :
    e * MulAut.conj r * e⁻¹ = MulAut.conj (e r) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem exists_pow_three_eq_of_pow_eq_one {M : Type*} [Group M] [Finite M] [IsCyclic M]
    {x : M} (hx : x ^ (Nat.card M / Nat.gcd 3 (Nat.card M)) = 1) : ∃ y : M, y ^ 3 = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
  have hord : orderOf g = Nat.card M := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  have hm0 : 0 < Nat.card M := Nat.card_pos
  have hδm : Nat.gcd 3 (Nat.card M) ∣ Nat.card M := Nat.gcd_dvd_right 3 _
  have hδ0 : 0 < Nat.gcd 3 (Nat.card M) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  obtain ⟨k, hk⟩ := hδm
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hmk : Nat.card M / Nat.gcd 3 (Nat.card M) = k :=
    Nat.div_eq_of_eq_mul_left hδ0 (hk.trans (mul_comm _ _))
  rw [hmk] at hx
  have hpow : g ^ (i * (k : ℤ)) = 1 := by rw [_root_.zpow_mul, zpow_natCast]; exact hx
  have hdiv := orderOf_dvd_iff_zpow_eq_one.mpr hpow
  rw [hord] at hdiv
  have hδi : (Nat.gcd 3 (Nat.card M) : ℤ) ∣ i := by
    nth_rewrite 1 [hk] at hdiv
    push_cast at hdiv
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hk0)).mp hdiv
  obtain ⟨j, rfl⟩ := hδi
  have hbez : (Nat.gcd 3 (Nat.card M) : ℤ) =
      3 * Nat.gcdA 3 (Nat.card M) + Nat.card M * Nat.gcdB 3 (Nat.card M) :=
    Nat.gcd_eq_gcd_ab 3 _
  have hgm : g ^ (Nat.card M : ℤ) = 1 := by rw [zpow_natCast, ← hord, pow_orderOf_eq_one]
  refine ⟨g ^ (Nat.gcdA 3 (Nat.card M) * j), ?_⟩
  rw [← zpow_natCast, ← _root_.zpow_mul, hbez, show (3 * Nat.gcdA 3 (Nat.card M) +
      (Nat.card M : ℤ) * Nat.gcdB 3 (Nat.card M)) * j = Nat.gcdA 3 (Nat.card M) * j * (3 : ℕ) +
      (Nat.card M : ℤ) * (Nat.gcdB 3 (Nat.card M) * j) by push_cast; ring,
    _root_.zpow_add, _root_.zpow_mul g (Nat.card M : ℤ), hgm, _root_.one_zpow, mul_one]

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

section Model

variable [Finite K] [CharP K 2]

theorem sublineAutHom_heisL_mem {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    (y : normOne J ⋊[normOneAction J] conjGroup J) (z : hermitianUnipotentCoord J) :
    sublineAutHom J C hJ hC y (heisL J C hJ z) ∈ (heisL J C hJ).range := by
  rw [← SemidirectProduct.inl_left_mul_inr_right y, map_mul, MulAut.mul_apply]
  have hright : sublineAutHom J C hJ hC (SemidirectProduct.inr y.right) (heisL J C hJ z) ∈
      (heisL J C hJ).range := by
    rcases (mem_conjGroup_iff (J := J)).mp y.right.2 with h | h
    · have hy : y.right = 1 := Subtype.ext h
      rw [hy, map_one, map_one, MulAut.one_apply]
      exact ⟨z, rfl⟩
    · have hy : y.right = ⟨J.conj, Subgroup.mem_zpowers _⟩ := Subtype.ext h
      rw [hy, sublineAutHom_bar_heisL hf hcard hfixed hJ hC]
      exact ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ := hright
  rw [← hz', sublineAutHom_inl_heisL hJ hC]
  exact ⟨_, rfl⟩

theorem eq_one_of_sublineAutHom_eq_conj {f : ℕ} (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {y : normOne J ⋊[normOneAction J] conjGroup J} {z : hermitianUnipotentCoord J}
    (h : sublineAutHom J C hJ hC y = MulAut.conj (heisL J C hJ z)) : z = 1 ∧ y = 1 := by
  set X := sublineHom J hJ (lowerSL _ (Multiplicative.ofAdd 1))
  have hXmem : (X : J.specialSubgroup ⧸ C) ∈ lowerRootL J C hJ := ⟨_, rfl⟩
  have hfix := sublineAutHom_apply_of_mem hJ hC y (lowerRootL_le_sublineL hJ hXmem)
  rw [h, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hfix
  set Q := hermitianUnipotentSU J hJ z
  have hmk : ((Q * X : J.specialSubgroup) : J.specialSubgroup ⧸ C) =
      ((X * Q : J.specialSubgroup) : J.specialSubgroup ⧸ C) := by
    change heisL J C hJ z * (X : J.specialSubgroup ⧸ C) = (X : J.specialSubgroup ⧸ C) *
      heisL J C hJ z
    exact hfix
  obtain ⟨c, hc, -, -⟩ := exists_scalar_of_mk_eq hC hmk
  have hQ : ((Q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1] := rfl
  have hX : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; 1, 0, 1] := by
    rw [coe_sublineHom_lowerSL]
    simp
  simp only [Subgroup.coe_mul, Units.val_mul, hQ, hX] at hc
  have e20 := congrFun (congrFun hc 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] at e20
  subst e20
  have e10 := congrFun (congrFun hc 1) 0
  have e00 := congrFun (congrFun hc 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply] at e10 e00
  have ha : z.1.1 = 0 := by simpa using e10
  have hb : z.1.2 = 0 := by linear_combination e00
  have hz : z = 1 := Subtype.ext (Prod.ext ha hb)
  refine ⟨hz, ?_⟩
  rw [hz, map_one, map_one] at h
  exact (injective_iff_map_eq_one _).mp
    (sublineAutHom_injective hJ hC hcard hfixed) y h

omit [CharP K 2] in
theorem sublineAutHom_inl_pow_three (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (c : normOne J) :
    sublineAutHom J C hJ hC (SemidirectProduct.inl (c⁻¹ ^ 3)) =
      MulAut.conj (QuotientGroup.mk' C (torusHom J hJ c)) := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  obtain ⟨hg, h⟩ := sublineAutHom_mk hJ hC (SemidirectProduct.inl (c⁻¹ ^ 3)) g
  rw [h, MulAut.conj_apply]
  change _ = ((torusHom J hJ c * g * (torusHom J hJ c)⁻¹ : J.specialSubgroup) :
    J.specialSubgroup ⧸ C)
  congr 1
  apply Subtype.ext
  have hT : ((torusHom J hJ c : J.specialSubgroup) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) (c : Kˣ) * diag3 1 (((c⁻¹ ^ 3 : normOne J)) : Kˣ) 1 := by
    rw [coe_torusHom]
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diag3, coe_diag3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalar_apply]
    field_simp
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, OneMemClass.coe_one,
    map_one, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv, hT, _root_.mul_inv_rev]
  have hcomm := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (c : Kˣ)
    (diag3 1 (((c⁻¹ ^ 3 : normOne J)) : Kˣ) 1 * (g : GL (Fin 3) K) *
      (diag3 1 (((c⁻¹ ^ 3 : normOne J)) : Kˣ) 1)⁻¹)
  calc diag3 1 (((c⁻¹ ^ 3 : normOne J)) : Kˣ) 1 * (g : GL (Fin 3) K) *
        (diag3 1 (((c⁻¹ ^ 3 : normOne J)) : Kˣ) 1)⁻¹
      = GeneralLinearGroup.scalar (Fin 3) (c : Kˣ) *
          (diag3 1 (((c⁻¹ ^ 3 : normOne J)) : Kˣ) 1 * (g : GL (Fin 3) K) *
            (diag3 1 (((c⁻¹ ^ 3 : normOne J)) : Kˣ) 1)⁻¹) *
          (GeneralLinearGroup.scalar (Fin 3) (c : Kˣ))⁻¹ := by
        rw [← hcomm.eq, mul_inv_cancel_right]
    _ = _ := by group

theorem exists_eq_conj_heisL_mul_sublineAutHom {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {β : MulAut (J.specialSubgroup ⧸ C)} (hβ : ∀ x ∈ upperRootL J C hJ, β x = x) :
    ∃ (z : hermitianUnipotentCoord J) (y : normOne J ⋊[normOneAction J] conjGroup J),
      β = MulAut.conj (heisL J C hJ z) * sublineAutHom J C hJ hC y := by
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have hP := center_psu_eq_bot (2 ^ f) hq hcard hfixed hJ
  have hcen := center_eq_ker_coverToPSU hJ hC hP
  have : Group.IsPerfect J.specialSubgroup :=
    isPerfect_specialSubgroup Nat.prime_two hq hcard hfixed hJ
  obtain ⟨σ, A, hA, hAg⟩ :=
    exists_isometry_psu_of_card Nat.prime_two hq hcard hfixed hJ (coverAutPSU hJ hC hcen β)
  have hfixm : ∀ t : Multiplicative (unitaryCoverFixedField J), ∃ u : Kˣ,
      A * glAut σ ((sublineHom J hJ (upperSL _ t) : J.specialSubgroup) : GL (Fin 3) K) * A⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) u =
        ((sublineHom J hJ (upperSL _ t) : J.specialSubgroup) : GL (Fin 3) K) := by
    intro t
    obtain ⟨hg, hβg⟩ := hAg (sublineHom J hJ (upperSL _ t))
    have hfixβ : β ((sublineHom J hJ (upperSL _ t) : J.specialSubgroup) :
        J.specialSubgroup ⧸ C) =
        ((sublineHom J hJ (upperSL _ t) : J.specialSubgroup) : J.specialSubgroup ⧸ C) :=
      hβ _ ⟨t, rfl⟩
    have h1 := coverAutPSU_apply hJ hC hcen β
      ((sublineHom J hJ (upperSL _ t) : J.specialSubgroup) : J.specialSubgroup ⧸ C)
    rw [hfixβ, coverToPSU_mk, hβg] at h1
    exact psuMk_eq_psuMk_iff.mp h1
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  obtain ⟨u1, hu1⟩ := hfixm (Multiplicative.ofAdd 1)
  have hm1 := mul_scalar_eq_of_conj hu1
  rw [glAut_sublineHom_upperSL, coe_sublineHom_upperSL] at hm1
  simp only [toAdd_ofAdd, map_one] at hm1
  obtain ⟨-, h10, h20⟩ := col_zero_of_fix_upper hJ hA hm1
  rw [← hM] at h10 h20
  have hgram := (J.mem_unitarySubgroup_iff A).mp hA
  have g01 := congrArg (fun B => B 0 1) hgram
  have g02 := congrArg (fun B => B 0 2) hgram
  have g11 := congrArg (fun B => B 1 1) hgram
  have g12 := congrArg (fun B => B 1 2) hgram
  have g22 := congrArg (fun B => B 2 2) hgram
  simp [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, ← hM, h10,
    h20] at g01 g02 g11 g12 g22
  have ha0 : M 0 0 ≠ 0 := by
    rintro h
    simp [h] at g02
  have h21 : M 2 1 = 0 := g01.resolve_left ha0
  simp only [h21, map_zero, mul_zero, zero_mul, add_zero, zero_add] at g11 g12
  have hb0 : M 1 1 ≠ 0 := by
    rintro h
    simp [h] at g11
  have hroot : ∀ x : unitaryCoverFixedField J, M 0 0 * σ (x : K) = (x : K) * M 2 2 := by
    intro x
    obtain ⟨u, hu⟩ := hfixm (Multiplicative.ofAdd x)
    have hm := mul_scalar_eq_of_conj hu
    rw [glAut_sublineHom_upperSL, coe_sublineHom_upperSL] at hm
    simp only [toAdd_ofAdd] at hm
    have e11 := congrFun (congrFun hm 1) 1
    have e02 := congrFun (congrFun hm 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply, ← hM, h10,
      h21] at e11 e02
    have hu1 : (u : K) = 1 := by
      have := e11
      rw [mul_eq_left₀ hb0] at this
      exact this
    rw [hu1, mul_one] at e02
    linear_combination e02
  have hac : M 0 0 = M 2 2 := by simpa using hroot 1
  have hσk : ∀ x : K, J.conj x = x → σ x = x := by
    intro x hx
    have := hroot ⟨x, hx⟩
    rw [← hac] at this
    exact mul_left_cancel₀ ha0 (this.trans (mul_comm _ _))
  have hσmem : σ ∈ conjGroup J := by
    rcases eq_one_or_conj_of_fix hcard hfixed hσk with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  rw [← hac] at g02 g12 g22
  have hna : M 0 0 * J.conj (M 0 0) = 1 := by linear_combination g02
  have hnb : M 1 1 * J.conj (M 1 1) = 1 := by linear_combination g11
  have hca : J.conj (M 0 0) = (M 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hna
  have hcb : J.conj (M 1 1) = (M 1 1)⁻¹ := eq_inv_of_mul_eq_one_right hnb
  have h12 : M 1 2 = -(M 1 1 * J.conj (M 0 1) * M 0 0) := by
    rw [hcb] at g12
    field_simp at g12
    linear_combination g12
  have hzcond : M 0 2 / M 0 0 + J.conj (M 0 2 / M 0 0) +
      M 0 1 / M 1 1 * J.conj (M 0 1 / M 1 1) = 0 := by
    rw [h12] at g22
    simp only [map_neg, map_mul, map_div₀, hca, hcb, J.conj_involutive _] at g22 ⊢
    field_simp at g22 ⊢
    linear_combination g22
  set z : hermitianUnipotentCoord J := ⟨(M 0 1 / M 1 1, M 0 2 / M 0 0), hzcond⟩ with hzdef
  set a : Kˣ := Units.mk0 (M 0 0) ha0
  set d : Kˣ := Units.mk0 (M 1 1) hb0 * a⁻¹
  have hd : d ∈ normOne J := by
    change ((Units.mk0 (M 1 1) hb0 * a⁻¹ : Kˣ) : K) *
      J.conj ((Units.mk0 (M 1 1) hb0 * a⁻¹ : Kˣ) : K) = 1
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, a, map_mul, map_inv₀,
      hca, hcb]
    field_simp
  have hAeq : A = GeneralLinearGroup.scalar (Fin 3) a * hermitianUnipotentGL J z *
      diag3 1 d 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, hermitianUnipotentGL_val,
      hermitianUnipotentMatrix_eq, coe_diag3, ← hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, d, z, scalar_apply, diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three, h10,
        h20, h21, h12, ← hac, map_div₀, hcb]
    all_goals field_simp
  refine ⟨z, ⟨⟨d, hd⟩, ⟨σ, hσmem⟩⟩, eq_of_coverToPSU_comp_eq hJ hC hcen fun x => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
  obtain ⟨hg, hΨ⟩ := sublineAutHom_mk hJ hC ⟨⟨d, hd⟩, ⟨σ, hσmem⟩⟩ g
  obtain ⟨hg', hβg⟩ := hAg g
  rw [MulAut.mul_apply, QuotientGroup.mk'_apply, hΨ, MulAut.conj_apply,
    ← coverAutPSU_apply hJ hC hcen β, coverToPSU_mk, hβg]
  change psuMk J ⟨_, hg'⟩ = psuMk J (hermitianUnipotentSU J hJ z * ⟨_, hg⟩ *
    (hermitianUnipotentSU J hJ z)⁻¹)
  congr 1
  apply Subtype.ext
  change A * glAut σ (g : GL (Fin 3) K) * A⁻¹ =
    hermitianUnipotentGL J z * (diag3 1 d 1 * glAut σ (g : GL (Fin 3) K) * (diag3 1 d 1)⁻¹) *
      (hermitianUnipotentGL J z)⁻¹
  have hcomm := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar a
    (hermitianUnipotentGL J z * (diag3 1 d 1 * glAut σ (g : GL (Fin 3) K) * (diag3 1 d 1)⁻¹) *
      (hermitianUnipotentGL J z)⁻¹)
  rw [hAeq]
  calc GeneralLinearGroup.scalar (Fin 3) a * hermitianUnipotentGL J z * diag3 1 d 1 *
        glAut σ (g : GL (Fin 3) K) *
        (GeneralLinearGroup.scalar (Fin 3) a * hermitianUnipotentGL J z * diag3 1 d 1)⁻¹
      = GeneralLinearGroup.scalar (Fin 3) a *
          (hermitianUnipotentGL J z * (diag3 1 d 1 * glAut σ (g : GL (Fin 3) K) *
            (diag3 1 d 1)⁻¹) * (hermitianUnipotentGL J z)⁻¹) *
          (GeneralLinearGroup.scalar (Fin 3) a)⁻¹ := by group
    _ = _ := by rw [← hcomm.eq, mul_inv_cancel_right]

theorem exists_eq_conj_of_pow_eq_one {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {β : MulAut (J.specialSubgroup ⧸ C)} (hβ : ∀ x ∈ upperRootL J C hJ, β x = x)
    {n : ℕ} (hn : Odd n) (hdvd : n ∣ (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) (hβn : β ^ n = 1) :
    ∃ (z : hermitianUnipotentCoord J) (c : normOne J),
      β = MulAut.conj (heisL J C hJ z * QuotientGroup.mk' C (torusHom J hJ c)) := by
  obtain ⟨z, y, rfl⟩ := exists_eq_conj_heisL_mul_sublineAutHom hf hcard hfixed hJ hC hβ
  set Ψ := sublineAutHom J C hJ hC with hΨ
  have hpow : ∀ k : ℕ, ∃ w : hermitianUnipotentCoord J,
      (MulAut.conj (heisL J C hJ z) * Ψ y) ^ k = MulAut.conj (heisL J C hJ w) * Ψ (y ^ k) := by
    intro k
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ k ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ := sublineAutHom_heisL_mem hf hcard hfixed hJ hC (y ^ k) z
      have hswap : Ψ (y ^ k) * MulAut.conj (heisL J C hJ z) =
          MulAut.conj (heisL J C hJ w') * Ψ (y ^ k) := by
        rw [hw', ← mulAut_mul_conj_mul_inv, inv_mul_cancel_right]
      refine ⟨w * w', ?_⟩
      rw [pow_succ, hw, pow_succ, map_mul, map_mul, map_mul, mul_assoc, ← mul_assoc (Ψ (y ^ k)),
        hswap]
      group
  obtain ⟨w, hw⟩ := hpow n
  rw [hβn] at hw
  have hΨn : Ψ (y ^ n) = MulAut.conj (heisL J C hJ w⁻¹) := by
    rw [map_inv, map_inv]
    exact eq_inv_of_mul_eq_one_right hw.symm
  obtain ⟨-, hyn⟩ := eq_one_of_sublineAutHom_eq_conj hcard hfixed hJ hC hΨn
  have hright : y.right = 1 := by
    have h1 : y.right ^ n = 1 := by
      have := congrArg (SemidirectProduct.rightHom) hyn
      rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at this
    have h2 : y.right ^ 2 = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rcases (mem_conjGroup_iff (J := J)).mp y.right.2 with h | h
      · rw [h, one_pow]
      · rw [h]
        exact conj_sq (J := J)
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    exact h1
  have hy : y = SemidirectProduct.inl y.left := by
    apply SemidirectProduct.ext
    · rfl
    · rw [hright, SemidirectProduct.right_inl]
  have hleft : y.left ^ n = 1 := by
    have : SemidirectProduct.inl (y.left ^ n) =
        (1 : normOne J ⋊[normOneAction J] conjGroup J) := by
      rw [map_pow, ← hy, hyn]
    exact (injective_iff_map_eq_one _).mp SemidirectProduct.inl_injective _ this
  obtain ⟨-, -, -, hcyc, hMcard, -⟩ :=
    unitary_central_cover_subline_automorphism_two_part J f hf hcard hfixed hJ C hC
  have hleft' : y.left ^ (Nat.card (normOne J) / Nat.gcd 3 (Nat.card (normOne J))) = 1 := by
    rw [hMcard]
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul, hleft, one_pow]
  obtain ⟨e, he⟩ := exists_pow_three_eq_of_pow_eq_one hleft'
  refine ⟨z, e⁻¹, ?_⟩
  rw [hy, ← he, show e ^ 3 = (e⁻¹)⁻¹ ^ 3 by rw [inv_inv], sublineAutHom_inl_pow_three hJ hC,
    map_mul]

end Model

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.RootCenter
