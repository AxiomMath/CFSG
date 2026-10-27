module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3U4T2b
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4Dat
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Cls
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4T2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4T2c

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks PSpL UnitaryOut
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

omit h in
theorem comm_of_mk_comm_trace (h4 : (4 : K) ≠ 0) {G u : unitarySU p f K 4}
    (htr : (((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).trace = 4)
    (hc : (QuotientGroup.mk G : StatedProj (StatedSU 4 (p ^ f) K)) * QuotientGroup.mk u =
      QuotientGroup.mk u * QuotientGroup.mk G) : G * u = u * G := by
  have e : (QuotientGroup.mk (G * u * G⁻¹) : StatedProj (StatedSU 4 (p ^ f) K)) =
      QuotientGroup.mk u := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc,
      mul_inv_cancel_right]
  rw [QuotientGroup.eq] at e
  obtain ⟨c, hc'⟩ := val_of_mem_scal e
  have hu : (((u : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (c : K) • (((G * u * G⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) := by
    have e1 : u = (G * u * G⁻¹) * ((G * u * G⁻¹)⁻¹ * u) := by group
    conv_lhs => rw [e1]
    rw [Subgroup.coe_mul, Units.val_mul, hc', Matrix.mul_smul, Matrix.mul_one]
  have htr' : (((G * u * G⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).trace = 4 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, htr]
  have hc1 : (c : K) = 1 := by
    have e2 := congrArg Matrix.trace hu
    rw [Matrix.trace_smul, htr', htr, smul_eq_mul] at e2
    have h0 : (4 : K) * ((c : K) - 1) = 0 := by linear_combination -e2
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 h4
    · linear_combination h0
  rw [hc1, one_smul] at hu
  have hGu : G * u * G⁻¹ = u := ext_val hu.symm
  calc G * u = G * u * G⁻¹ * G := by group
    _ = u * G := by rw [hGu]

variable {R : GL (Fin 4) K} {t : K}
  (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
  {X : unitarySU p f K 4}
  (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
    (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))

include hXR in
theorem eq_of_comm_range_U4 (hq3 : p ^ f = 3) (hp2 : p ≠ 2) (ht0 : t ≠ 0)
    (g : StatedProj (StatedSU 4 (p ^ f) K))
    (hg : ∀ x ∈ ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range, g * x = x * g) :
    g = 1 ∨ g = QuotientGroup.mk X := by
  obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective g
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2K h2K
  have hcomm : ∀ x ∈ (bdGens : Set (SL(2, h.fixedField) × SL(2, h.fixedField))),
      cP R G * bdK h x = bdK h x * cP R G := by
    intro x hx
    have hc : (QuotientGroup.mk G : StatedProj (StatedSU 4 (p ^ f) K)) *
        QuotientGroup.mk (bdHomU h hR x) = QuotientGroup.mk (bdHomU h hR x) *
          QuotientGroup.mk G := hg _ ⟨x, rfl⟩
    have e := congrArg (cP R) (comm_of_mk_comm_trace h4 (trace_bdHomU_gens h hR hx) hc)
    rwa [cP_mul, cP_mul, cP_bdHomU] at e
  obtain ⟨k1, k2, k3, k4⟩ := gens_mem (F := h.fixedField)
  obtain ⟨g1, g2, g3, g4⟩ := bdK_gens h
  have c1 := hcomm _ k1
  have c2 := hcomm _ k2
  have c3 := hcomm _ k3
  have c4 := hcomm _ k4
  rw [g1] at c1
  rw [g2] at c2
  rw [g3] at c3
  rw [g4] at c4
  have hGd := eq_of_comm_bd c1 c2 c3 c4
  set x := cP R G 0 0 with hx
  set y := cP R G 2 2 with hy
  have hun := unitary_cP_bJ h ht0 hR G
  rw [hGd] at hun
  have hxN : h.bar x * x = 1 := by
    have e := congrFun (congrFun hun 0) 1
    simp [uStar, bd, bJ, Matrix.mul_apply, Fin.sum_univ_four] at e
    linear_combination e
  have hdet : x ^ 2 * y ^ 2 = 1 := by
    have hd := det_cP h R G
    rw [hGd, det_bd, det_smul, det_smul, det_one, Fintype.card_fin, mul_one, mul_one] at hd
    exact hd
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hx4 : x ^ 4 = 1 := by
    rw [UnitaryFieldData.bar_apply, hq3] at hxN
    rw [show x ^ 4 = x ^ 3 * x by ring]
    exact hxN
  have hd0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hdN : h.bar x⁻¹ * x⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hxN, inv_one]
  have hd4 : x⁻¹ ^ 4 = 1 := by rw [inv_pow, hx4, inv_one]
  set Sc := Q5U4.scalU h hd0 hdN hd4 with hSc
  have hmk : (QuotientGroup.mk G : StatedProj (StatedSU 4 (p ^ f) K)) =
      QuotientGroup.mk (Sc * G) := by
    rw [QuotientGroup.mk_mul, hSc, Q5U4.mk_scalU, one_mul]
  have hw2 : (y * x⁻¹) ^ 2 = 1 := by
    have e : (y * x⁻¹) ^ 2 * x ^ 4 = x ^ 2 * y ^ 2 := by
      field_simp
    rw [hx4, mul_one, hdet] at e
    exact e
  have hcPS : cP R (Sc * G) = bd 1 ((y * x⁻¹) • 1) := by
    have hS : cP R Sc = x⁻¹ • 1 := by
      rw [cP, hSc, Q5U4.coe_scalU, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [cP_mul, hS, hGd, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bd, hx0, mul_comm]
  have hw' : (y * x⁻¹ - 1) * (y * x⁻¹ + 1) = 0 := by linear_combination hw2
  rcases mul_eq_zero.1 hw' with hw | hw
  · left
    have e : cP R (Sc * G) = cP R (1 : unitarySU p f K 4) := by
      rw [hcPS, sub_eq_zero.1 hw, one_smul, bd_one, cP_one]
    rw [hmk, eq_of_cP_eq R e, QuotientGroup.mk_one]
  · right
    have e : cP R (Sc * G) = cP R X := by
      rw [hcPS, eq_neg_of_add_eq_zero_left hw, cP_X hXR, X1_eq_bd, one_smul]
    rw [hmk, eq_of_cP_eq R e]

include hR hXR in
theorem false_t2_U43 (hq3 : p ^ f = 3) (hp2 : p ≠ 2) (ht0 : t ≠ 0)
    (hXX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1)
    {G : Type} [Group G] [Finite G] {R' : Subgroup G} {S : Sylow 2 R'} {t' : G}
    (hD : TightDatum R' S t') {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) (e : ↥N ≃* StatedProj (StatedSU 4 (p ^ f) K))
    (htN : t' ∈ N) (hu : e ⟨t', htN⟩ = QuotientGroup.mk X) : False := by
  have : Finite K := h.finite
  let := Fintype.ofFinite h.fixedField
  have hF3 : Fintype.card h.fixedField = 3 := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField, hq3]
  have hsi : (swU h hR)⁻¹ = swU h hR := inv_eq_of_mul_eq_one_right (swU_mul_swU h hR)
  have hwu : (QuotientGroup.mk (swU h hR) : StatedProj (StatedSU 4 (p ^ f) K)) *
      QuotientGroup.mk X = QuotientGroup.mk X * QuotientGroup.mk (swU h hR) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact (mk_eq_of_smul (val_swU_mul_X h hR hXR)).symm
  let β : SL(2, h.fixedField) × SL(2, h.fixedField) →* StatedProj (StatedSU 4 (p ^ f) K) :=
    (QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)
  refine Q3L4.false_of_block hD hC e htN hu hF3 β (fun a b => ker_bdHomU_iff h hR a b)
    (mk_bdHomU_neg_one h hR hXR) hwu (fun a b => ?_) (conj_mem_range_U4 h hR hXR hp2 ht0 hXX)
    (eq_of_comm_range_U4 h hR hXR hq3 hp2 ht0) (Q5U4.noOddNormal_range_bdHomU h hR hp2)
    (Q5U4.noQ8Fix_t2 h hp2 ht0 hR)
  simp only [β, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hsi, swU_conj]

end Q3U4

end CFSG.ClassicalInvolution.Q3.TA3
