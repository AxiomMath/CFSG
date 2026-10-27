module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4LeviZ
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.FieldTheory.Finite.Basic
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Matrix

section DiagMatrix

open Matrix

variable {F : Type*} [Field F]

theorem diagonal_mul_transvection_d4 (d : Fin 3 → F) (hd : ∀ i, d i ≠ 0) {i j : Fin 3}
    (hij : i ≠ j) (c : F) :
    diagonal d * (Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin 3) (Fin 3) F) =
      (Matrix.SpecialLinearGroup.transvection hij (d i * c * (d j)⁻¹) :
        Matrix (Fin 3) (Fin 3) F) * diagonal d := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  rw [diagonal_mul, mul_diagonal, single_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [mul_assoc, inv_mul_cancel₀ (hd _), mul_one]
  · rw [mul_zero, zero_mul]

theorem trace_transvection_d4 [CharP F 2] {i j : Fin 3} (hij : i ≠ j) (c : F) :
    trace (Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, trace_add, trace_one,
    trace_single_eq_of_ne _ _ _ hij, add_zero, Fintype.card_fin]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  norm_num
  linear_combination h2

theorem eq_one_of_diag_inner_sl3_d4 [Fintype F] [CharP F 2] (hF : Fintype.card F = 4) {N : F}
    (hN : N ≠ 0) (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      Matrix.SpecialLinearGroup.transvection hij (![1, N, 1] i * c * (![1, N, 1] j)⁻¹) *
        (M * Matrix.SpecialLinearGroup.transvection hij c * M⁻¹)⁻¹ ∈
          center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    N = 1 := by
  set d : Fin 3 → F := ![1, N, 1] with hd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hd, hN]
  set D : Matrix (Fin 3) (Fin 3) F := diagonal d with hD
  set Mi : Matrix (Fin 3) (Fin 3) F := ↑(M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) with hMi
  have hMiM : Mi * (M : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hMi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hMMi : (M : Matrix (Fin 3) (Fin 3) F) * Mi = 1 := by
    rw [hMi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hMiM' : ∀ X : Matrix (Fin 3) (Fin 3) F, Mi * ((M : Matrix (Fin 3) (Fin 3) F) * X) = X :=
    fun X => by rw [← Matrix.mul_assoc, hMiM, Matrix.one_mul]
  set P := Mi * D with hP
  have hdetD : D.det = N := by
    rw [hD, det_diagonal, Fin.prod_univ_three]
    simp [hd]
  have hdetMi : Mi.det = 1 := (M⁻¹).2
  have hPu : IsUnit P := by
    rw [isUnit_iff_isUnit_det, hP, det_mul, hdetD, hdetMi, one_mul]
    exact isUnit_iff_ne_zero.2 hN
  have key : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      P * (Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin 3) (Fin 3) F) =
        (Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin 3) (Fin 3) F) * P := by
    intro i j hij c
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (h i j hij c)
    set E := Matrix.SpecialLinearGroup.transvection hij c with hE
    set E' := Matrix.SpecialLinearGroup.transvection hij (d i * c * (d j)⁻¹) with hE'
    have hZ : (E' : Matrix (Fin 3) (Fin 3) F) =
        r • ((M : Matrix (Fin 3) (Fin 3) F) * (E : Matrix (Fin 3) (Fin 3) F) * Mi) := by
      have e : E' = (E' * (M * E * M⁻¹)⁻¹) * (M * E * M⁻¹) := by group
      rw [e, Matrix.SpecialLinearGroup.coe_mul, ← hr, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.one_mul]
    have h2 : D * (E : Matrix (Fin 3) (Fin 3) F) = (E' : Matrix (Fin 3) (Fin 3) F) * D :=
      diagonal_mul_transvection_d4 d hd0 hij c
    have h3 : P * (E : Matrix (Fin 3) (Fin 3) F) = r • ((E : Matrix (Fin 3) (Fin 3) F) * P) := by
      rw [hP, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hZ, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc, hMiM']
    have hr1 : r = 1 := by
      have e1 : P * (E : Matrix (Fin 3) (Fin 3) F) * P⁻¹ = r • (E : Matrix (Fin 3) (Fin 3) F) := by
        rw [h3, Matrix.smul_mul, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hPu), Matrix.mul_one]
      have e2 := Matrix.trace_conj hPu (E : Matrix (Fin 3) (Fin 3) F)
      rw [e1, trace_smul, trace_transvection_d4, smul_eq_mul, mul_one] at e2
      exact e2
    rw [h3, hr1, one_smul]
  obtain ⟨μ, hμ⟩ := mem_range_scalar_of_commute_transvectionStruct (M := P) fun t => by
    have := key t.i t.j t.hij t.c
    rw [Matrix.SpecialLinearGroup.transvection_coe] at this
    exact this.symm
  have hDM : D = (M : Matrix (Fin 3) (Fin 3) F) * P := by
    rw [hP, ← Matrix.mul_assoc, hMMi, Matrix.one_mul]
  have hNμ : N = μ ^ 3 := by
    rw [← hdetD, hDM, det_mul, ← hμ, M.2, one_mul, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hN (by rw [hNμ]; ring)
  have h3 := FiniteField.pow_card_sub_one_eq_one μ hμ0
  rw [hF] at h3
  rw [hNμ]
  exact h3

end DiagMatrix

section DiagZ

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem exists_order_nine_d4 (hK : Nat.card K = 64) : ∃ μ : Kˣ, μ ^ 9 = 1 ∧ μ ^ 3 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 63 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  refine ⟨g ^ 7, by rw [← pow_mul, show 7 * 9 = orderOf g by rw [hord]]; exact pow_orderOf_eq_one g,
    fun h => ?_⟩
  have h21 : g ^ 21 = 1 := by rw [show 21 = 7 * 3 by rfl, pow_mul]; exact h
  have := orderOf_dvd_of_pow_eq_one h21
  rw [hord] at this
  norm_num at this

omit [Finite K] in
theorem conj_phi_transvection_d4
    {φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) (d4k K σ) →* ModGL TwistTag.D4.tag K}
    (hφ : ∀ γ ∈ RA2, ∀ c : d4k K σ, φ (CFSG.LieType.Steinberg.SL.x 2 (d4k K σ) γ c) =
      pinnedX TwistTag.D4.tag K (a2D4 γ) (c : K))
    (μ : Kˣ) {Nk : d4k K σ} (hNk : (Nk : K) = (μ : K) * σ μ * σ (σ μ))
    {i j : Fin 3} (hij : i ≠ j) (c : d4k K σ) :
    trialityOuterTorus K σ μ * φ (Matrix.SpecialLinearGroup.transvection hij c) *
      (trialityOuterTorus K σ μ)⁻¹ =
        φ (Matrix.SpecialLinearGroup.transvection hij (![1, Nk, 1] i * c * (![1, Nk, 1] j)⁻¹)) := by
  have hx : ∀ {γ : Fin 2 → ℤ}, γ ∈ RA2 → (CFSG.LieType.Universal.SpecialLinear.toStd 2 γ =
      Pi.single i 1 - Pi.single j 1) → ∀ c' : d4k K σ,
        φ (Matrix.SpecialLinearGroup.transvection hij c') =
          pinnedX TwistTag.D4.tag K (a2D4 γ) (c' : K) := fun hγ hst c' => by
    rw [← CFSG.LieType.Steinberg.SL.x_eq hij hst c', hφ _ hγ]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
  · rw [hx (mem_rootsA2_d4.2 (Or.inl rfl)) (by decide), hx (mem_rootsA2_d4.2 (Or.inl rfl))
      (by decide), a2D4_x₂]
    change trialityOuterTorus K σ μ * d4x₂ K c * _ = d4x₂ K _
    rw [ho_conj_d4x₂]
    congr 1
    simp [hNk]
    ring
  · rw [hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inl rfl)))) (by decide),
      hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inl rfl)))) (by decide), a2D4_x₆]
    change trialityOuterTorus K σ μ * d4x₆ K c * _ = d4x₆ K _
    rw [ho_conj_d4x₆]
    congr 1
    simp
  · rw [hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by decide),
      hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by decide), a2D4_y₂]
    change trialityOuterTorus K σ μ * d4y₂ K c * _ = d4y₂ K _
    rw [ho_conj_d4y₂]
    congr 1
    simp [hNk]
  · rw [hx (mem_rootsA2_d4.2 (Or.inr (Or.inl rfl))) (by decide),
      hx (mem_rootsA2_d4.2 (Or.inr (Or.inl rfl))) (by decide), a2D4_x₅]
    change trialityOuterTorus K σ μ * d4x₅ K c * _ = d4x₅ K _
    rw [ho_conj_d4x₅]
    congr 1
    simp [hNk]
  · rw [hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (by decide),
      hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (by decide), a2D4_y₆]
    change trialityOuterTorus K σ μ * d4y₆ K c * _ = d4y₆ K _
    rw [ho_conj_d4y₆]
    congr 1
    simp
  · rw [hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (by decide),
      hx (mem_rootsA2_d4.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (by decide), a2D4_y₅]
    change trialityOuterTorus K σ μ * d4y₅ K c * _ = d4y₅ K _
    rw [ho_conj_d4y₅]
    congr 1
    simp [hNk]
    ring

theorem d4_diag_z
    (hK : Nat.card K = (2 ^ 2) ^ 3) (hσq : ∀ c, σ c = c ^ 2 ^ 2) :
    ∃ y ∈ centralizer (((d4W0 K σ).subgroupOf (d4C K σ) : Subgroup ↥(d4C K σ)) :
      Set ↥(d4C K σ)), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
        ¬ InducesInner y ((d4Lz K σ).subgroupOf (d4C K σ)) := by
  have : CharP K 2 := charP_two_of_card_d4 hK
  have hσ3' := sigma_cube_of_card_d4 σ hK hσq
  have hσ := ringEquiv_cube_d4 σ hσ3'
  have hk : Nat.card (d4k K σ) = 2 ^ 2 := card_d4k_of_card σ (by norm_num) hK hσq
  obtain ⟨μ, hμ9, hμ3⟩ := exists_order_nine_d4 (show Nat.card K = 64 by rw [hK]; norm_num)
  have hNk : σ ((μ : K) * σ μ * σ (σ μ)) = (μ : K) * σ μ * σ (σ μ) :=
    (mem_trialityFixedField).1 (norm_mem_trialityFixedField hσ (μ : K))
  set Nk : d4k K σ := ⟨(μ : K) * σ μ * σ (σ μ), hNk⟩ with hNkdef
  have hN3 : (μ : K) * σ μ * σ (σ μ) = (μ : K) ^ 3 := by
    have h9 : (μ : K) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, hμ9, Units.val_one]
    rw [hσq, hσq]
    calc (μ : K) * (μ : K) ^ 2 ^ 2 * ((μ : K) ^ 2 ^ 2) ^ 2 ^ 2 =
          ((μ : K) ^ 9) ^ 2 * (μ : K) ^ 3 := by ring
      _ = (μ : K) ^ 3 := by rw [h9, one_pow, one_mul]
  have hNk1 : Nk ≠ 1 := by
    intro h
    have h1 : (μ : K) ^ 3 = 1 := by
      rw [← hN3]
      exact congrArg Subtype.val h
    exact hμ3 (Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one]))
  have hNk0 : Nk ≠ 0 := by
    intro h
    have h1 : (μ : K) ^ 3 = 0 := by
      rw [← hN3]
      exact congrArg Subtype.val h
    exact μ.ne_zero ((pow_eq_zero_iff (by norm_num)).1 h1)
  set y : ↥(d4C K σ) := ⟨trialityOuterTorus K σ μ, trialityOuterTorus_mem_d4C σ hσ3' μ⟩ with hy
  refine ⟨y, ?_, ⟨2, ?_⟩, ?_⟩
  ·
    rw [mem_centralizer_iff]
    intro q hq
    refine Subtype.ext ?_
    obtain ⟨p, hp⟩ := exists_trialityTorusHom_eq_d4 σ hσ (d4W0_le_d4H σ hσ (mem_subgroupOf.1 hq))
    change (q : ModGL TwistTag.D4.tag K) * trialityOuterTorus K σ μ =
      trialityOuterTorus K σ μ * q
    rw [← hp, ho_eq_d4, ← map_mul, ← map_mul, mul_comm]
  ·
    refine Subtype.ext ?_
    change trialityOuterTorus K σ μ ^ 3 ^ 2 = 1
    rw [ho_eq_d4, ← map_pow, Prod.pow_mk, show (3 : ℕ) ^ 2 = 9 by norm_num, hμ9, one_pow]
    exact map_one _
  ·
    rintro ⟨l, hl, hinn⟩
    obtain ⟨φ, hφ⟩ := exists_sl3_hom_d4 σ
    have hrange := range_sl3_hom_d4 σ hφ
    have hmem : ∀ g, φ g ∈ d4Lz K σ := fun g => hrange ▸ ⟨g, rfl⟩
    let ψ : Matrix.SpecialLinearGroup (Fin 3) (d4k K σ) →*
        ↥((d4Lz K σ).subgroupOf (d4C K σ)) :=
      (φ.codRestrict (d4C K σ) fun g => d4Lz_le σ (hmem g)).codRestrict _
        fun g => mem_subgroupOf.2 (hmem g)
    have hψ : Function.Surjective ψ := by
      rintro ⟨⟨x, hxC⟩, hx⟩
      have hx' : x ∈ φ.range := hrange ▸ mem_subgroupOf.1 hx
      obtain ⟨g, rfl⟩ := hx'
      exact ⟨g, rfl⟩
    have hψ1 : ∃ g, ψ g ≠ 1 := by
      refine ⟨CFSG.LieType.Steinberg.SL.x 2 (d4k K σ) ![1, 0] 1, fun h => ?_⟩
      have h1 : φ (CFSG.LieType.Steinberg.SL.x 2 (d4k K σ) ![1, 0] 1) = 1 :=
        congrArg (fun y : ↥((d4Lz K σ).subgroupOf (d4C K σ)) => ((y : ↥(d4C K σ)) :
          ModGL TwistTag.D4.tag K)) h
      rw [hφ _ (mem_rootsA2_d4.2 (by decide)), ← pinnedX_zero TwistTag.D4.tag K (a2D4 ![1, 0])]
        at h1
      exact one_ne_zero (pinnedX_injective _ _ _ h1)
    have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 (d4k K σ) le_rfl
    have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hψ1
    have hcom := CFSG.LocalCores.comap_center_eq_of_perfect hq.1 ψ hψ hker
    have hcom' : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (d4k K σ),
        ψ g ∈ center ↥((d4Lz K σ).subgroupOf (d4C K σ)) →
          g ∈ center (Matrix.SpecialLinearGroup (Fin 3) (d4k K σ)) := fun g hg => by
      have := (Subgroup.ext_iff.1 hcom g).1 hg
      exact this
    obtain ⟨M, hM⟩ := hψ ⟨l, hl⟩
    have hlM : (l : ModGL TwistTag.D4.tag K) = φ M :=
      (congrArg (fun z : ↥((d4Lz K σ).subgroupOf (d4C K σ)) => ((z : ↥(d4C K σ)) :
        ModGL TwistTag.D4.tag K)) hM).symm
    have : Fintype (d4k K σ) := Fintype.ofFinite _
    have hcard : Fintype.card (d4k K σ) = 4 := by
      rw [← Nat.card_eq_fintype_card, hk]
      norm_num
    refine hNk1 (eq_one_of_diag_inner_sl3_d4 hcard hNk0 M fun i j hij c => hcom' _ ?_)
    obtain ⟨w, hw, hwe⟩ := hinn ((ψ (Matrix.SpecialLinearGroup.transvection hij c) :
      ↥((d4Lz K σ).subgroupOf (d4C K σ))) : ↥(d4C K σ)) (ψ _).2
    have hw' : w = ψ (Matrix.SpecialLinearGroup.transvection hij (![1, Nk, 1] i * c *
        (![1, Nk, 1] j)⁻¹) * (M * Matrix.SpecialLinearGroup.transvection hij c * M⁻¹)⁻¹) := by
      refine Subtype.ext (Subtype.ext ?_)
      have h1 := congrArg (fun z : ↥(d4C K σ) => (z : ModGL TwistTag.D4.tag K)) hwe
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [h1]
      change _ = φ (Matrix.SpecialLinearGroup.transvection hij (![1, Nk, 1] i * c *
        (![1, Nk, 1] j)⁻¹) * (M * Matrix.SpecialLinearGroup.transvection hij c * M⁻¹)⁻¹)
      rw [map_mul, map_inv, map_mul, map_mul, map_inv,
        ← conj_phi_transvection_d4 σ hφ μ rfl hij c, ← hlM]
      rfl
    rw [← hw']
    exact hw

end DiagZ

end CFSG.ComponentClassification.RankTwoExceptional.D4
