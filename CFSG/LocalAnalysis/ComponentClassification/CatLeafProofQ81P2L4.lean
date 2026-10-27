module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Base
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthNormal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4Graph

public section

namespace CFSG.ComponentClassification.CatLeafProof.Q81P2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL TBlocks HBlocks Blocks StabL
open CFSG.ComponentClassification.GSThmB.Cent516

variable {K : Type} [Field K] [Finite K]

theorem ringAut_eq_one_of_card_three (hK : Nat.card K = 3) (a : K ≃+* K) : a = 1 := by
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rwa [Nat.card_eq_fintype_card] at hK
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hcard
  have h := Subsingleton.elim (e.trans a) e
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun h y

omit [Finite K] in
theorem exists_odd_of_frame {A P D : GL (Fin 4) K} {μ : Kˣ}
    (hAP : A * P = GeneralLinearGroup.scalar (Fin 4) μ * (P * D)) {G : Type*} [Group G]
    (φ : G →* SpecialLinearGroup (Fin 4) K)
    (hφ : ∀ g, (φ g : Matrix (Fin 4) (Fin 4) K) * (D : Matrix (Fin 4) (Fin 4) K) =
      (D : Matrix (Fin 4) (Fin 4) K) * φ g)
    {S : Set G} (hS : closure S = ⊤) (hSo : ∀ s ∈ S, Odd (orderOf s)) {x : G} {n : ℕ}
    (hx : orderOf (proj 4 K (φ x)) = n) (hn : 2 ∣ n) :
    ∃ T : Set (projectiveSL 4 K), (∀ t ∈ T, conjAut 4 K A t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  set ρ := (conjAut 4 K P).toMonoidHom.comp ((proj 4 K).comp φ) with hρ
  refine exists_odd_of_hom ρ (fun g => fixed_of_frame hAP (φ g) (hφ g)) hS hSo
    (two_dvd_card_range ρ (x := x) ?_ hn)
  rw [hρ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.orderOf_eq]
  exact hx

theorem exists_odd_conjAut (hK : Nat.card K = 3) {A : GL (Fin 4) K}
    (hsq : conjAut 4 K A ^ 2 = 1) :
    ∃ T : Set (projectiveSL 4 K), (∀ t ∈ T, conjAut 4 K A t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hK2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow Nat.prime_three (by norm_num) hK'
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨hE2, hE2o⟩ := elementary_good Nat.prime_three (by norm_num) hK' 2
  obtain ⟨hE3, hE3o⟩ := elementary_good Nat.prime_three (by norm_num) hK' 3
  have hAA : conjAut 4 K (A * A) * fieldAut 4 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← sq, hsq]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hAA
  have hX : (A : Matrix (Fin 4) (Fin 4) K) * A = (c : K) • 1 := by
    rw [← Units.val_mul, ← hc, GeneralLinearGroup.coe_scalar, scalar_apply,
      smul_one_eq_diagonal]
  have hbd : orderOf (proj 4 K ((bdSL.comp (MonoidHom.inl _ _)) jSL)) = 4 := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply]
    exact (bd_z4z2 h2).1
  by_cases hns : ∀ a : K, (A : Matrix (Fin 4) (Fin 4) K) ≠ a • 1
  · rcases classify_inv hK2 hX (Units.ne_zero c) hns with
      ⟨l, hl0, -, -, P, hP⟩ | ⟨l, hl0, -, -, P, s, hs, hP⟩ | ⟨-, P, hP⟩
    ·
      refine exists_odd_of_frame (P := P) (D := t2GL) (μ := Units.mk0 l hl0) ?_
        (bdSL.comp (MonoidHom.inl _ _)) (fun g => bdSL_comm (g, 1)) hE2 hE2o hbd
        (by norm_num)
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
        Units.val_mk0, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      change (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
        l • ((P : Matrix (Fin 4) (Fin 4) K) * X1 1)
      rw [← hP, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    ·
      have hs0 : s * l⁻¹ ≠ 0 := mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num)
        (inv_ne_zero hl0)
      refine exists_odd_of_frame (P := P) (D := t1GL)
        (μ := Units.mk0 (s * l⁻¹)⁻¹ (inv_ne_zero hs0)) ?_ (blockSL K 3 1) block_comm hE3 hE3o
        (block_involution h2) (dvd_refl 2)
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
        Units.val_mk0, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      change (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
        (s * l⁻¹)⁻¹ • ((P : Matrix (Fin 4) (Fin 4) K) * dOne)
      rw [← hP, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    ·
      refine exists_odd_of_frame (P := P) (D := nGL (c : K) (Units.ne_zero c)) (μ := 1) ?_
        kronSL (fun g => kronSL_comm g (c : K)) hE2 hE2o kron_involution (dvd_refl 2)
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, map_one, Units.val_one, Matrix.one_mul]
      exact hP
  ·
    push Not at hns
    obtain ⟨a, ha⟩ := hns
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact (Matrix.isUnits_det_units A).ne_zero (by rw [ha, det_zero])
    refine exists_odd_of_frame (P := 1) (D := 1) (μ := Units.mk0 a ha0) ?_
      (bdSL.comp (MonoidHom.inl _ _))
      (fun g => by rw [Units.val_one, Matrix.mul_one, Matrix.one_mul]) hE2 hE2o hbd
      (by norm_num)
    simp only [mul_one]
    apply Units.ext
    rw [ha, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0, smul_one_eq_diagonal]

theorem exists_odd_graph_alt (hK : Nat.card K = 3) {A : GL (Fin 4) K}
    (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -A) :
    ∃ T : Set (projectiveSL 4 K),
      (∀ t ∈ T, (conjAut 4 K A * dualAut 4 K) t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hK2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow Nat.prime_three (by norm_num) hK'
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨hE2, hE2o⟩ := elementary_good Nat.prime_three (by norm_num) hK' 2
  have hR := inv_transpose_of (A := A) (s := -1) (by rw [hA, neg_one_smul]) (by norm_num)
  rw [neg_one_smul] at hR
  obtain ⟨P, hPu, hPR⟩ := exists_transpose_mul_mul_eq_formA h2 hR
    (Matrix.isUnits_det_units A⁻¹)
  set P' : GL (Fin 4) K := Matrix.nonsingInvUnit P hPu with hP'
  set ρ := (conjAut 4 K P').toMonoidHom.comp ((proj 4 K).comp sbdSL) with hρ
  refine exists_odd_of_hom ρ (fun g => fixed_of_form (sbdSL g) ?_) hE2 hE2o
    (two_dvd_card_range ρ (x := jSL) ?_ (dvd_refl 2 |>.mul_left 2))
  · change (sbd (g : Matrix (Fin 2) (Fin 2) K) 1)ᵀ * (Pᵀ * _ * P) * sbd _ 1 = Pᵀ * _ * P
    rw [hPR]
    exact sbd_formA _ _ g.2 det_one
  · rw [hρ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.orderOf_eq]
    exact sbd_order h2

theorem exists_odd_graph_sym (hK : Nat.card K = 3) {A : GL (Fin 4) K}
    (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = A) :
    ∃ T : Set (projectiveSL 4 K),
      (∀ t ∈ T, (conjAut 4 K A * dualAut 4 K) t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  classical
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hK2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow Nat.prime_three (by norm_num) hK'
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hRt : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ = (A⁻¹ : GL (Fin 4) K) := by
    have := inv_transpose_of (A := A) (s := 1) (by rw [hA, one_smul]) (by norm_num)
    rwa [one_smul] at this
  obtain ⟨P, w, -, hw, hPR⟩ := Burgoyne.PSL.exists_frame hK2 (by norm_num : 2 ≤ 4) A⁻¹ hRt
    one_ne_zero
  set d := w 3 with hd
  have hw' : w = ![1, 1, 1, d] := by
    funext i
    fin_cases i
    · exact hw 0 (by decide)
    · exact hw 1 (by decide)
    · exact hw 2 (by decide)
    · rfl
  have hG : (P : Matrix (Fin 4) (Fin 4) K)ᵀ * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      P = diagonal ![1, 1, 1, d] := by
    rw [hPR, hw']
  obtain ⟨hdc, hdc', hc3, hc3', hce, hee, hcG, hcG'⟩ := sym_mats (K := K) d
  set cs : SpecialLinearGroup (Fin 4) K := ⟨cyc, hdc⟩ with hcs
  set cs' : SpecialLinearGroup (Fin 4) K := ⟨cyc', hdc'⟩ with hcs'
  set τ := conjAut 4 K P with hτ
  set T : Set (projectiveSL 4 K) := {τ (proj 4 K cs), τ (proj 4 K cs')} with hT
  have hord3 : ∀ M : SpecialLinearGroup (Fin 4) K,
      (M : Matrix (Fin 4) (Fin 4) K) * M * M = 1 → (M : Matrix (Fin 4) (Fin 4) K) 1 0 ≠ 0 →
        orderOf (τ (proj 4 K M)) = 3 := fun M hM hM10 => by
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ (proj_ne_one_of_off (i := 1) (j := 0) (by decide) hM10)
    rw [← map_pow]
    have : M ^ 3 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_pow, pow_three, ← Matrix.mul_assoc, hM,
        Matrix.SpecialLinearGroup.coe_one]
    rw [this, map_one]
  refine ⟨T, ?_, ?_⟩
  · rintro t (rfl | rfl)
    · refine ⟨fixed_of_form cs (by rw [hG]; exact hcG), ?_⟩
      rw [hord3 cs hc3 (by simp [cs, cyc])]
      decide
    · refine ⟨fixed_of_form cs' (by rw [hG]; exact hcG'), ?_⟩
      rw [hord3 cs' hc3' (by simp [cs', cyc'])]
      decide
  · set es : SpecialLinearGroup (Fin 4) K := ⟨eOne, by
      rw [eOne, Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]⟩
      with hes'
    have hes : cs' = es * cs := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      change (cyc' : Matrix (Fin 4) (Fin 4) K) i j = (eOne * cyc : Matrix (Fin 4) (Fin 4) K) i j
      rw [hce]
    have hmem : τ (proj 4 K es) ∈ closure T := by
      have h1 : τ (proj 4 K es) = τ (proj 4 K cs') * (τ (proj 4 K cs))⁻¹ := by
        rw [hes, map_mul, map_mul, mul_inv_cancel_right]
      rw [h1]
      exact mul_mem (subset_closure (Or.inr rfl)) (inv_mem (subset_closure (Or.inl rfl)))
    have hord : orderOf (τ (proj 4 K es)) = 2 := by
      rw [MulEquiv.orderOf_eq]
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow]
        have : es ^ 2 = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
          rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]
          change (eOne * eOne : Matrix (Fin 4) (Fin 4) K) i j = _
          rw [hee]
          rfl
        rw [this, map_one]
      · refine proj_ne_one_of_diag (i := 0) (j := 1) ?_
        change eOne 0 0 ≠ (eOne : Matrix (Fin 4) (Fin 4) K) 1 1
        simp [eOne]
        intro h
        apply h2
        linear_combination -h
    have h := orderOf_dvd_natCard (⟨_, hmem⟩ : closure T)
    rwa [Subgroup.orderOf_mk, hord] at h

theorem exists_odd_L4 (hK : Nat.card K = 3) (α : MulAut (projectiveSL 4 K)) (hα : α ^ 2 = 1) :
    ∃ T : Set (projectiveSL 4 K), (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) (by norm_num : 3 ≤ 4)).2 α
  obtain rfl := ringAut_eq_one_of_card_three hK σ
  rw [map_one, mul_one] at hαeq
  subst hαeq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    exact exists_odd_conjAut hK hα
  · rw [pow_one] at hα ⊢
    rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα with hA | hA
    · exact exists_odd_graph_sym hK hA
    · exact exists_odd_graph_alt hK hA

theorem exists_odd_of_lieModel_psl {L : Type} [Group L] (hL : Blueprint.LieModel L .PSL 4 3 1)
    (β : MulAut L) (hβ : β * β = 1) :
    ∃ T : Set L, (∀ t ∈ T, β t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have hα : MulAut.congr e β ^ 2 = 1 := by rw [← map_pow, sq, hβ, map_one]
  obtain ⟨T, hT, h2⟩ := exists_odd_L4 (by rw [hK, pow_one]) _ hα
  exact exists_odd_congr e β hT h2

end CFSG.ComponentClassification.CatLeafProof.Q81P2
