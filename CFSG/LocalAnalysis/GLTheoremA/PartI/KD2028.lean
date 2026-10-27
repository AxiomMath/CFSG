module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB

@[expose] def KD2028 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    (IsHatSix L ∨ IsHatSeven L ∨ IsHatMTwentyTwo L ∨ IsSLThreeExc L ∨
      (IsSUThreeExc L ∧ ¬ IsSUThreeTwoPow L)) →
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      x ∈ Subgroup.normalizer (T : Set L)

section KDMatrices

open Matrix

variable {K : Type} [Field K]

private def kdX (ω : K) : Matrix (Fin 3) (Fin 3) K := diagonal ![ω, ω ^ 2, 1]

private def kdXi (ω : K) : Matrix (Fin 3) (Fin 3) K := diagonal ![ω ^ 2, ω, 1]

private def kdT : Matrix (Fin 3) (Fin 3) K := diagonal ![-1, -1, 1]

private def kdP : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

private def kdU (t : K) : Matrix (Fin 3) (Fin 3) K := !![1, t, 0; 0, 1, 0; 0, 0, 1]

private theorem kdX_mul_kdXi {ω : K} (h : ω ^ 3 = 1) : kdX ω * kdXi ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kdX, kdXi, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h

private theorem kdXi_mul_kdX {ω : K} (h : ω ^ 3 = 1) : kdXi ω * kdX ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kdX, kdXi, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h

private theorem kdX_zero_zero (ω : K) : kdX ω 0 0 = ω := by simp [kdX]

private theorem kdX_pow_three {ω : K} (h : ω ^ 3 = 1) : kdX ω ^ 3 = 1 := by
  have h2 : kdX ω * kdX ω = kdXi ω := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kdX, kdXi, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination h | linear_combination ω * h
  rw [pow_three, h2, kdX_mul_kdXi h]

private theorem kdX_det {ω : K} (h : ω ^ 3 = 1) : (kdX ω).det = 1 := by
  simp [kdX, det_diagonal, Fin.prod_univ_three]
  linear_combination h

private theorem kdT_det : (kdT : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [kdT, det_diagonal, Fin.prod_univ_three]

private theorem kdP_det : (kdP : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [kdP, det_fin_three]

private theorem kdU_det (t : K) : (kdU t).det = 1 := by
  simp [kdU, det_fin_three]

private theorem kdT_mul_kdT : (kdT : Matrix (Fin 3) (Fin 3) K) * kdT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kdT, Matrix.mul_apply, Fin.sum_univ_three]

private theorem kdP_mul_kdP : (kdP : Matrix (Fin 3) (Fin 3) K) * kdP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kdP, Matrix.mul_apply, Fin.sum_univ_three]

private theorem kdT_mul_kdX (ω : K) : kdT * kdX ω = kdX ω * kdT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kdT, kdX, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem kdU_zero : kdU (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kdU, Matrix.one_apply]

private theorem kdU_mul (s t : K) : kdU s * kdU t = kdU (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kdU, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem kdU_mul_neg (t : K) : kdU t * kdU (-t) = 1 := by
  rw [kdU_mul, add_neg_cancel, kdU_zero]

private theorem kdU_neg_mul (t : K) : kdU (-t) * kdU t = 1 := by
  rw [kdU_mul, neg_add_cancel, kdU_zero]

private theorem kdU_sq {t : K} (h2 : (2 : K) = 0) : kdU t * kdU t = 1 := by
  rw [kdU_mul, ← two_mul, h2, zero_mul, kdU_zero]

private theorem kdX_mul_kdU {ω : K} (h : ω ^ 3 = 1) (t : K) :
    kdX ω * kdU t * kdXi ω = kdU (ω ^ 2 * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kdX, kdXi, kdU, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination h

private theorem kdXi_mul_kdU {ω : K} (h : ω ^ 3 = 1) (s : K) :
    kdXi ω * kdU s * kdX ω = kdU (ω * s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kdX, kdXi, kdU, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination h | linear_combination (ω * s) * h

private theorem kd_conj_cancel {P Q M : Matrix (Fin 3) (Fin 3) K} (h : Q * P = 1) :
    Q * (P * M * Q) * P = M := by
  calc Q * (P * M * Q) * P = (Q * P) * M * (Q * P) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [h, Matrix.one_mul, Matrix.mul_one]

private theorem kd_eq_one_of_sq_eq {ω : K} (h3 : ω ^ 3 = 1) (h : ω ^ 2 = ω) : ω = 1 := by
  linear_combination h3 - (1 + ω) * h

private theorem kd_not_comm {ω : K} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M 0 1 = 1) (hc : M * kdX ω = kdX ω * M) : False := by
  have e := congrFun (congrFun hc 0) 1
  simp [kdX, Matrix.mul_apply, Fin.sum_univ_three, hM] at e
  first
  | exact h1 (kd_eq_one_of_sq_eq h3 e)
  | exact h1 (kd_eq_one_of_sq_eq h3 e.symm)

private def kdXgl {ω : K} (h : ω ^ 3 = 1) : GL (Fin 3) K :=
  ⟨kdX ω, kdXi ω, kdX_mul_kdXi h, kdXi_mul_kdX h⟩

private def kdTgl : GL (Fin 3) K := ⟨kdT, kdT, kdT_mul_kdT, kdT_mul_kdT⟩

private def kdPgl : GL (Fin 3) K := ⟨kdP, kdP, kdP_mul_kdP, kdP_mul_kdP⟩

private def kdUgl (t : K) : GL (Fin 3) K := ⟨kdU t, kdU (-t), kdU_mul_neg t, kdU_neg_mul t⟩

private theorem kdXgl_pow_three {ω : K} (h : ω ^ 3 = 1) : kdXgl h ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact kdX_pow_three h)

private theorem kdTgl_sq : kdTgl ^ 2 = (1 : GL (Fin 3) K) :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, sq]; exact kdT_mul_kdT)

private theorem kdTgl_ne_one (h2 : (2 : K) ≠ 0) : kdTgl ≠ (1 : GL (Fin 3) K) := by
  intro e
  have e' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) e
  simp [kdTgl, kdT] at e'
  exact h2 (by linear_combination -e')

private def kdUgrp : Subgroup (GL (Fin 3) K) where
  carrier := {A | ∃ t : K, (A : Matrix (Fin 3) (Fin 3) K) = kdU t}
  mul_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, by rw [Units.val_mul, hs, ht, kdU_mul]⟩
  one_mem' := ⟨0, by rw [Units.val_one, kdU_zero]⟩
  inv_mem' := by
    rintro a ⟨t, ht⟩
    exact ⟨-t, Units.inv_eq_of_mul_eq_one_right (by rw [ht, kdU_mul_neg])⟩

end KDMatrices

private theorem kd_exists_cube_root (K : Type) [Field K] [Finite K] (h3 : Nat.card K % 3 = 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units K]
    have : 0 < Nat.card K := Nat.card_pos
    omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
  rw [orderOf_eq_prime_iff] at hg
  refine ⟨(g : K), ?_, fun e => hg.2 (Units.ext e)⟩
  rw [← Units.val_pow_eq_pow_val, hg.1, Units.val_one]

private theorem kd_two_ne_zero_of_card (K : Type) [Field K] [Finite K] {q : ℕ}
    (hq : Nat.card K = q ^ 2) (hodd : q % 2 = 1) : (2 : K) ≠ 0 := by
  intro h2
  letI := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    haveI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by simpa using h2)
    exact ringChar.eq K 2
  have hev := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, hq] at hev
  have ho : q ^ 2 % 2 = 1 := Nat.odd_iff.mp (Nat.odd_iff.mpr hodd).pow
  omega

private theorem kd_isPGroup_two {G : Type*} [Group G] (T : Subgroup G) (h : ∀ g ∈ T, g ^ 2 = 1) :
    IsPGroup 2 T := by
  intro g
  refine ⟨1, ?_⟩
  show g ^ 2 = 1
  exact Subtype.ext (by simpa using h g.1 g.2)

private theorem kd_odd_case (K : Type) [Field K] (H : Subgroup (GL (Fin 3) K)) {ω : K}
    (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (h2 : (2 : K) ≠ 0) (hx : kdXgl h3 ∈ H)
    (ht : kdTgl ∈ H) (hp : kdPgl ∈ H) :
    ∃ x : ↥H, orderOf x = 3 ∧ x ∉ Subgroup.center ↥H ∧ ∃ T : Subgroup ↥H, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set ↥H) := by
  have hx3 : (⟨kdXgl h3, hx⟩ : ↥H) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact kdXgl_pow_three h3)
  have hx1 : (⟨kdXgl h3, hx⟩ : ↥H) ≠ 1 := by
    intro e
    have e' := congrArg (fun g : ↥H => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) e
    simp [kdXgl, kdX_zero_zero] at e'
    exact h1 e'
  refine ⟨⟨kdXgl h3, hx⟩, orderOf_eq_prime hx3 hx1, ?_,
    Subgroup.zpowers (⟨kdTgl, ht⟩ : ↥H), ?_, ?_, ?_⟩
  · intro hc
    rw [Subgroup.mem_center_iff] at hc
    have hm := congrArg (fun g : ↥H => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (hc ⟨kdPgl, hp⟩)
    simp [kdPgl, kdXgl] at hm
    exact kd_not_comm h3 h1 (M := kdP) (by simp [kdP]) hm
  · intro hT
    have hmem : (⟨kdTgl, ht⟩ : ↥H) ∈ Subgroup.zpowers (⟨kdTgl, ht⟩ : ↥H) :=
      Subgroup.mem_zpowers _
    rw [hT, Subgroup.mem_bot] at hmem
    exact kdTgl_ne_one h2 (congrArg (fun g : ↥H => (g : GL (Fin 3) K)) hmem)
  · apply kd_isPGroup_two
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hsq : (⟨kdTgl, ht⟩ : ↥H) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact kdTgl_sq)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]
  · have hcomm : Commute (⟨kdTgl, ht⟩ : ↥H) ⟨kdXgl h3, hx⟩ :=
      Subtype.ext (Units.ext (kdT_mul_kdX ω))
    have hmem : (⟨kdXgl h3, hx⟩ : ↥H) ∈
        Subgroup.centralizer ((Subgroup.zpowers (⟨kdTgl, ht⟩ : ↥H) : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (hcomm.zpow_left k).eq
    exact Subgroup.centralizer_le_normalizer _ hmem

private theorem kd_char2_case (K : Type) [Field K] (H : Subgroup (GL (Fin 3) K)) {ω : K}
    (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (h2 : (2 : K) = 0) (hx : kdXgl h3 ∈ H)
    (hR : ∀ t : K, kdUgl t ∈ H) :
    ∃ x : ↥H, orderOf x = 3 ∧ x ∉ Subgroup.center ↥H ∧ ∃ T : Subgroup ↥H, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set ↥H) := by
  have hx3 : (⟨kdXgl h3, hx⟩ : ↥H) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact kdXgl_pow_three h3)
  have hx1 : (⟨kdXgl h3, hx⟩ : ↥H) ≠ 1 := by
    intro e
    have e' := congrArg (fun g : ↥H => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) e
    simp [kdXgl, kdX_zero_zero] at e'
    exact h1 e'
  refine ⟨⟨kdXgl h3, hx⟩, orderOf_eq_prime hx3 hx1, ?_, kdUgrp.subgroupOf H, ?_, ?_, ?_⟩
  · intro hc
    rw [Subgroup.mem_center_iff] at hc
    have hm := congrArg (fun g : ↥H => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (hc ⟨kdUgl 1, hR 1⟩)
    simp [kdUgl, kdXgl] at hm
    exact kd_not_comm h3 h1 (M := kdU 1) (by simp [kdU]) hm
  · intro hT
    have hmem : (⟨kdUgl 1, hR 1⟩ : ↥H) ∈ kdUgrp.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr ⟨1, rfl⟩
    rw [hT, Subgroup.mem_bot] at hmem
    have e := congrArg (fun g : ↥H => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1) hmem
    simp [kdUgl, kdU] at e
  · apply kd_isPGroup_two
    intro g hg
    obtain ⟨t, ht⟩ := Subgroup.mem_subgroupOf.mp hg
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one, sq, ht]
    exact kdU_sq h2
  · rw [Subgroup.mem_set_normalizer_iff]
    intro g
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨ω ^ 2 * t, by
        show kdX ω * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * kdXi ω = kdU (ω ^ 2 * t)
        rw [ht, kdX_mul_kdU h3 t]⟩
    · rintro ⟨s, hs⟩
      refine ⟨ω * s, ?_⟩
      have hs' : kdX ω * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * kdXi ω = kdU s := hs
      rw [← kdXi_mul_kdU h3 s, ← hs', kd_conj_cancel (kdXi_mul_kdX h3)]

theorem kd2028_slThree (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    ∃ x : ↥(StatedSL 3 K), orderOf x = 3 ∧ x ∉ Subgroup.center ↥(StatedSL 3 K) ∧
      ∃ T : Subgroup ↥(StatedSL 3 K), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        x ∈ Subgroup.normalizer (T : Set ↥(StatedSL 3 K)) := by
  obtain ⟨ω, h3, h1⟩ := kd_exists_cube_root K hK
  have hx : kdXgl h3 ∈ StatedSL 3 K := Subgroup.subset_closure (kdX_det h3)
  by_cases h2 : (2 : K) = 0
  · exact kd_char2_case K (StatedSL 3 K) h3 h1 h2 hx
      (fun t => Subgroup.subset_closure (kdU_det t))
  · exact kd_odd_case K (StatedSL 3 K) h3 h1 h2 hx (Subgroup.subset_closure kdT_det)
      (Subgroup.subset_closure kdP_det)

open Matrix in
private theorem kdX_unit {K : Type} [Field K] {ω : K} {q : ℕ} (hq0 : q ≠ 0) (h3 : ω ^ 3 = 1)
    (hωq : ω ^ q = ω ^ 2) (hω2 : (ω ^ 2) ^ q = ω) : ((kdX ω).map (· ^ q))ᵀ * kdX ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kdX, Matrix.mul_apply, Fin.sum_univ_three, hωq, hω2, zero_pow hq0] <;>
    linear_combination h3

open Matrix in
private theorem kdT_unit {K : Type} [Field K] {q : ℕ} (hodd : Odd q) (hq0 : q ≠ 0) :
    ((kdT : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * kdT = 1 := by
  have hm : (kdT : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = kdT := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kdT, zero_pow hq0, hodd.neg_one_pow]
  have hT : (kdT : Matrix (Fin 3) (Fin 3) K)ᵀ = kdT := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kdT]
  rw [hm, hT, kdT_mul_kdT]

open Matrix in
private theorem kdP_unit {K : Type} [Field K] {q : ℕ} (hodd : Odd q) (hq0 : q ≠ 0) :
    ((kdP : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * kdP = 1 := by
  have hm : (kdP : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = kdP := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kdP, zero_pow hq0, hodd.neg_one_pow]
  have hP : (kdP : Matrix (Fin 3) (Fin 3) K)ᵀ = kdP := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kdP]
  rw [hm, hP, kdP_mul_kdP]

theorem kd2028_suThree (K : Type) [Field K] [Finite K] (q : ℕ) (hq : Nat.card K = q ^ 2)
    (hq3 : q % 3 = 2) (hqodd : q % 2 = 1) :
    ∃ x : ↥(StatedSU 3 q K), orderOf x = 3 ∧ x ∉ Subgroup.center ↥(StatedSU 3 q K) ∧
      ∃ T : Subgroup ↥(StatedSU 3 q K), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        x ∈ Subgroup.normalizer (T : Set ↥(StatedSU 3 q K)) := by
  have hodd : Odd q := Nat.odd_iff.mpr hqodd
  have hq0 : q ≠ 0 := hodd.pos.ne'
  have hK : Nat.card K % 3 = 1 := by
    rw [hq, Nat.pow_mod, hq3]
  obtain ⟨ω, h3, h1⟩ := kd_exists_cube_root K hK
  have hωq : ω ^ q = ω ^ 2 := by
    have e : q = 3 * (q / 3) + 2 := by omega
    rw [e, pow_add, pow_mul, h3, one_pow, one_mul]
  have hω2 : (ω ^ 2) ^ q = ω := by
    rw [← pow_mul, mul_comm, pow_mul, hωq]
    linear_combination ω * h3
  have h2 : (2 : K) ≠ 0 := kd_two_ne_zero_of_card K hq hqodd
  have hx : kdXgl h3 ∈ StatedSU 3 q K :=
    Subgroup.subset_closure ⟨kdX_det h3, kdX_unit hq0 h3 hωq hω2⟩
  have ht : kdTgl ∈ StatedSU 3 q K := Subgroup.subset_closure ⟨kdT_det, kdT_unit hodd hq0⟩
  have hp : kdPgl ∈ StatedSU 3 q K := Subgroup.subset_closure ⟨kdP_det, kdP_unit hodd hq0⟩
  exact kd_odd_case K (StatedSU 3 q K) h3 h1 h2 hx ht hp

private theorem kd_comm_of_sq {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    {g h : L} (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hm : (g : L ⧸ Subgroup.center L) * (h : L ⧸ Subgroup.center L) =
      (h : L ⧸ Subgroup.center L) * (g : L ⧸ Subgroup.center L)) : g * h = h * g := by
  have hgg : g * g = 1 := by rw [← sq]; exact hg
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hh)
  have hcz : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hm]
    group
  set c := g * h * g⁻¹ * h⁻¹ with hc_def
  have hcen : ∀ y : L, y * c = c * y := fun y => Subgroup.mem_center_iff.mp hcz y
  have hc3 : c ^ 3 = 1 := hZ3 c hcz
  have e1 : g * c * g⁻¹ = c := by rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have e2 : g * c * g⁻¹ = h * g * h * g := by
    have : g * c * g⁻¹ = g * g * (h * g⁻¹ * h⁻¹ * g⁻¹) := by rw [hc_def]; group
    rw [this, hgg, one_mul, hg', hh']
  have e3 : c⁻¹ = h * g * h * g := by
    have : c⁻¹ = h * g * h⁻¹ * g⁻¹ := by rw [hc_def]; group
    rw [this, hg', hh']
  have hcc : c * c = 1 := mul_eq_one_iff_inv_eq.mpr (by rw [e3, ← e2, e1])
  have hc1 : c = 1 := by
    rw [pow_three, hcc, mul_one] at hc3
    exact hc3
  calc g * h = c * (h * g) := by rw [hc_def]; group
    _ = h * g := by rw [hc1, one_mul]

private def kdHatT {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    (W : Subgroup (L ⧸ Subgroup.center L)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) :
    Subgroup L where
  carrier := {g | g ^ 2 = 1 ∧ (g : L ⧸ Subgroup.center L) ∈ W}
  one_mem' := ⟨by rw [one_pow], by rw [QuotientGroup.mk_one]; exact W.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha2, ha⟩ ⟨hb2, hb⟩
    have hab : Commute a b := kd_comm_of_sq hZ3 ha2 hb2 (hWc _ ha _ hb)
    refine ⟨?_, ?_⟩
    · rw [hab.mul_pow, ha2, hb2, one_mul]
    · rw [QuotientGroup.mk_mul]
      exact W.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨ha2, ha⟩
    refine ⟨?_, ?_⟩
    · rw [inv_pow, ha2, inv_one]
    · rw [QuotientGroup.mk_inv]
      exact W.inv_mem ha

private theorem kd_conj_mem {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    (W : Subgroup (L ⧸ Subgroup.center L)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    {x : L} {c : L ⧸ Subgroup.center L} (hxc : (x : L ⧸ Subgroup.center L) = c)
    (hcW : ∀ w ∈ W, c * w * c⁻¹ ∈ W) {g : L} (hg : g ∈ kdHatT hZ3 W hWc) :
    x * g * x⁻¹ ∈ kdHatT hZ3 W hWc := by
  obtain ⟨hg2, hgW⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [show (x * g * x⁻¹) ^ 2 = x * g ^ 2 * x⁻¹ by rw [sq, sq]; group, hg2, mul_one,
      mul_inv_cancel]
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxc]
    exact hcW _ hgW

private theorem kd_hat_core {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    (hexp : ∀ x : L, IsPGroup 3 (Subgroup.zpowers x) → x ^ 3 = 1)
    (W : Subgroup (L ⧸ Subgroup.center L)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hWne : W ≠ ⊥) (c : L ⧸ Subgroup.center L) (hc1 : c ≠ 1)
    (hc3 : c ^ 3 = 1) (hcW : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hcW' : ∀ w ∈ W, c⁻¹ * w * c ∈ W) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  obtain ⟨x, hxc⟩ := QuotientGroup.mk_surjective c
  have hx3c : x ^ 3 ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hxc, hc3]
  have hx9 : x ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZ3 _ hx3c]
  have hp3 : IsPGroup 3 (Subgroup.zpowers x) := by
    intro g
    refine ⟨2, Subtype.ext ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hn]
    show (x ^ n) ^ 9 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx9, one_zpow]
  have hxpow : x ^ 3 = 1 := hexp x hp3
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hc1 (by rw [← hxc, QuotientGroup.mk_one])
  have hxZ : x ∉ Subgroup.center L := fun h =>
    hc1 (by rw [← hxc]; exact (QuotientGroup.eq_one_iff x).mpr h)
  have hT : kdHatT hZ3 W hWc ≠ ⊥ := by
    obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    have hw1' : (w : L ⧸ Subgroup.center L) ≠ 1 := fun h => hw1 (Subtype.ext h)
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective w
    have hg2 : g₀ ^ 2 ∈ Subgroup.center L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hW2 _ hwW]
    have ht2 : (g₀ ^ 3) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact hZ3 _ hg2
    have h3w : ((g₀ : L) : L ⧸ Subgroup.center L) ^ 3 = (g₀ : L ⧸ Subgroup.center L) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hW2 _ hwW, one_mul]
    have htW : ((g₀ ^ 3 : L) : L ⧸ Subgroup.center L) ∈ W := by
      rw [QuotientGroup.mk_pow, h3w]
      exact hwW
    have htne : g₀ ^ 3 ≠ 1 := by
      intro h
      apply hw1'
      have h' : ((g₀ ^ 3 : L) : L ⧸ Subgroup.center L) = 1 := by
        rw [h, QuotientGroup.mk_one]
      rw [QuotientGroup.mk_pow, h3w] at h'
      exact h'
    intro hbot
    have hmem : g₀ ^ 3 ∈ kdHatT hZ3 W hWc := ⟨ht2, htW⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact htne hmem
  refine ⟨x, orderOf_eq_prime hxpow hx1, hxZ, kdHatT hZ3 W hWc, hT, ?_, ?_⟩
  · exact kd_isPGroup_two _ (fun g hg => hg.1)
  · rw [Subgroup.mem_set_normalizer_iff]
    intro g
    simp only [SetLike.mem_coe]
    constructor
    · intro hg
      exact kd_conj_mem hZ3 W hWc hxc hcW hg
    · intro hg
      have hcW'' : ∀ w ∈ W, c⁻¹ * w * c⁻¹⁻¹ ∈ W := fun w hw => by rw [inv_inv]; exact hcW' w hw
      have h' := kd_conj_mem hZ3 W hWc (x := x⁻¹) (c := c⁻¹)
        (by rw [QuotientGroup.mk_inv, hxc]) hcW'' hg
      have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
      rwa [e] at h'

private theorem kd_perm_comm : ∀ σ τ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 →
    Equiv.Perm.sign τ = 1 → σ ^ 2 = 1 → τ ^ 2 = 1 → σ * τ = τ * σ := by
  decide

private theorem kd_A4_comm (σ τ : alternatingGroup (Fin 4)) (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) :
    σ * τ = τ * σ := by
  apply Subtype.ext
  have h := kd_perm_comm (σ : Equiv.Perm (Fin 4)) (τ : Equiv.Perm (Fin 4))
    (Equiv.Perm.mem_alternatingGroup.mp σ.2) (Equiv.Perm.mem_alternatingGroup.mp τ.2)
    (by simpa using congrArg Subtype.val hσ) (by simpa using congrArg Subtype.val hτ)
  simpa using h

private def kdV : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {σ | σ ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ
    have hσ' : σ ^ 2 = 1 := hσ
    have hτ' : τ ^ 2 = 1 := hτ
    have hc : Commute σ τ := kd_A4_comm σ τ hσ' hτ'
    show (σ * τ) ^ 2 = 1
    rw [hc.mul_pow, hσ', hτ', one_mul]
  inv_mem' := by
    intro σ hσ
    have hσ' : σ ^ 2 = 1 := hσ
    show σ⁻¹ ^ 2 = 1
    rw [inv_pow, hσ', inv_one]

private theorem kdV_conj (g : alternatingGroup (Fin 4)) {v : alternatingGroup (Fin 4)}
    (hv : v ∈ kdV) : g * v * g⁻¹ ∈ kdV := by
  have hv' : v ^ 2 = 1 := hv
  show (g * v * g⁻¹) ^ 2 = 1
  rw [show (g * v * g⁻¹) ^ 2 = g * v ^ 2 * g⁻¹ by rw [sq, sq]; group, hv', mul_one, mul_inv_cancel]

private def kdC : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private def kdA : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private theorem kdC_cube : kdC ^ 3 = 1 := Subtype.ext (by decide)

private theorem kdC_ne_one : kdC ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)

private theorem kdA_sq : kdA ^ 2 = 1 := Subtype.ext (by decide)

private theorem kdA_mem : kdA ∈ kdV := kdA_sq

private theorem kdA_ne_one : kdA ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)

theorem kd2028_hat (L : Type) [Group L] [Finite L] (hZ : Nat.card (Subgroup.center L) = 3)
    (φ : alternatingGroup (Fin 4) →* L ⧸ Subgroup.center L) (hφ : Function.Injective φ)
    (hexp : ∀ x : L, IsPGroup 3 (Subgroup.zpowers x) → x ^ 3 = 1) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      x ∈ Subgroup.normalizer (T : Set L) := by
  have hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1 := by
    intro z hz
    have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥(Subgroup.center L)) (x := ⟨z, hz⟩))
    rw [hZ] at h
    simpa using h
  have hWc : ∀ w ∈ kdV.map φ, ∀ w' ∈ kdV.map φ, w * w' = w' * w := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
    rw [← map_mul, ← map_mul, kd_A4_comm v v' hv hv']
  have hW2 : ∀ w ∈ kdV.map φ, w ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ^ 2 = 1 := hv
    rw [← map_pow, hv', map_one]
  have hWne : kdV.map φ ≠ ⊥ := by
    intro h
    have hmem : φ kdA ∈ kdV.map φ := Subgroup.mem_map_of_mem φ kdA_mem
    rw [h, Subgroup.mem_bot] at hmem
    apply kdA_ne_one
    apply hφ
    rw [hmem, map_one]
  have hc1 : φ kdC ≠ 1 := by
    intro h
    apply kdC_ne_one
    apply hφ
    rw [h, map_one]
  have hc3 : φ kdC ^ 3 = 1 := by rw [← map_pow, kdC_cube, map_one]
  have hcW : ∀ w ∈ kdV.map φ, φ kdC * w * (φ kdC)⁻¹ ∈ kdV.map φ := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem φ (kdV_conj kdC hv)
  have hcW' : ∀ w ∈ kdV.map φ, (φ kdC)⁻¹ * w * φ kdC ∈ kdV.map φ := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    have h' := kdV_conj kdC⁻¹ hv
    rw [inv_inv] at h'
    exact Subgroup.mem_map_of_mem φ h'
  exact kd_hat_core hZ3 hexp (kdV.map φ) hWc hW2 hWne (φ kdC) hc1 hc3 hcW hcW'

end CFSG.LocalAnalysis.GLTheoremA
