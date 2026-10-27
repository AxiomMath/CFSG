module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2b
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4Dat
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4T2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4T2b

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3L4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL TBlocks HBlocks
open scoped MatrixGroups

variable {K : Type} [Field K] [Fintype K] (hK3 : Fintype.card K = 3) {P : GL (Fin 4) K}
  {X : SL(4, K)} (hXP : (X : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
    (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))

omit [Fintype K] in
theorem val_eq_smul_of_cP4 {G Y : SL(4, K)} {c : K} (h : cP4 P G = c • cP4 P Y) :
    (G : Matrix (Fin 4) (Fin 4) K) = c • (Y : Matrix (Fin 4) (Fin 4) K) := by
  rw [val_eq_cP4 P G, h, val_eq_cP4 P Y, Matrix.mul_smul, Matrix.smul_mul]

include hK3 hXP in
theorem eq_of_comm_range_L4 (g : projectiveSL 4 K)
    (hg : ∀ x ∈ ((proj 4 K).comp (bdHom P)).range, g * x = x * g) :
    g = 1 ∨ g = proj 4 K X := by
  obtain ⟨G, rfl⟩ := proj_surjective 4 K g
  have h2 := two_ne_zero' hK3
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hcomm : ∀ x ∈ (bdGens : Set (SL(2, K) × SL(2, K))),
      ((Matrix.SpecialLinearGroup.toGL G : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((bdHom P x : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      ((bdHom P x : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) *
        ((Matrix.SpecialLinearGroup.toGL G : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    intro x hx
    have hgx : proj 4 K G * proj 4 K (bdHom P x) = proj 4 K (bdHom P x) * proj 4 K G :=
      hg _ ⟨x, rfl⟩
    have hfix : conjAut 4 K (Matrix.SpecialLinearGroup.toGL G) (proj 4 K (bdHom P x)) =
        proj 4 K (bdHom P x) := by
      rw [conjAut_toGL, MulAut.conj_apply, hgx, mul_inv_cancel_right]
    exact Q5L4.comm_of_conjAut_fix' h4 _ (trace_bdGens P hx).1 hfix
  have g1 : ((slU (1 : K), (1 : SL(2, K))) : SL(2, K) × SL(2, K)) ∈ bdGens := Set.mem_insert _ _
  have g2 : ((slL (1 : K), (1 : SL(2, K))) : SL(2, K) × SL(2, K)) ∈ bdGens :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have g3 : (((1 : SL(2, K)), slU (1 : K)) : SL(2, K) × SL(2, K)) ∈ bdGens :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have g4 : (((1 : SL(2, K)), slL (1 : K)) : SL(2, K) × SL(2, K)) ∈ bdGens :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _)))
  have c1 : ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := Matrix.SpecialLinearGroup.coe_one
  obtain ⟨A', hA'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K, M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
      ((Matrix.SpecialLinearGroup.toGL G : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P :=
    ⟨_, rfl⟩
  have k1 := conj_comm_bd P (hcomm _ g1)
  have k2 := conj_comm_bd P (hcomm _ g2)
  have k3 := conj_comm_bd P (hcomm _ g3)
  have k4 := conj_comm_bd P (hcomm _ g4)
  rw [← hA'] at k1 k2 k3 k4
  simp only [c1] at k1 k2 k3 k4
  have hGd := eq_of_comm_bd k1 k2 k3 k4
  have hcP : cP4 P G = A' := by
    rw [hA', Matrix.SpecialLinearGroup.coe_GL_coe_matrix, cP4]
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : A' 0 0 ^ 2 * A' 2 2 ^ 2 = 1 := by
    have hd : (cP4 P G).det = 1 := by
      rw [cP4, det_mul, det_mul, mul_right_comm, ← det_mul, hPP, det_one, one_mul]
      exact Matrix.SpecialLinearGroup.det_coe G
    rw [hcP, hGd, det_bd, det_smul, det_smul, det_one, Fintype.card_fin, mul_one,
      mul_one] at hd
    exact hd
  have hX1 : cP4 P X = X1 1 := cP4_X hXP
  have hx0 : A' 0 0 ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  have hy0 : A' 2 2 ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  have hne : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rcases eq_zero_or_eq_one_or_eq_neg_one hK3 (A' 0 0) with hx | hx | hx
  · exact absurd hx hx0
  all_goals rcases eq_zero_or_eq_one_or_eq_neg_one hK3 (A' 2 2) with hy | hy | hy
  · exact absurd hy hy0
  · left
    have e : cP4 P G = cP4 P 1 := by
      rw [cP4_one, hcP, hGd, hx, hy, one_smul, bd_one]
    rw [eq_of_cP4_eq P e, map_one]
  · right
    have e : cP4 P G = cP4 P X := by
      rw [hX1, hcP, hGd, hx, hy, X1_eq_bd]
    rw [eq_of_cP4_eq P e]
  · exact absurd hy hy0
  · right
    have e : cP4 P G = (-1 : K) • cP4 P X := by
      rw [hX1, hcP, hGd, hx, hy, one_smul, X1_eq_bd]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [bd]
    exact (proj_eq_of_smul hne (val_eq_smul_of_cP4 e)).symm
  · left
    have e : cP4 P G = (-1 : K) • cP4 P 1 := by
      rw [cP4_one, hcP, hGd, hx, hy]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [bd]
    rw [← (proj_eq_of_smul hne (val_eq_smul_of_cP4 e)), map_one]

include hK3 hXP in
theorem false_t2_L43 {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
    (hD : TightDatum R S t) {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) (e : ↥N ≃* projectiveSL 4 K) (htN : t ∈ N)
    (hu : e ⟨t, htN⟩ = proj 4 K X) : False := by
  have hK : Nat.card K = 3 ^ 1 := by rw [Nat.card_eq_fintype_card, hK3, pow_one]
  have h2 := two_ne_zero' hK3
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hsi : (swP P)⁻¹ = swP P := inv_eq_of_mul_eq_one_right (swP_mul_swP P)
  refine false_of_block hD hC e htN hu hK3 ((proj 4 K).comp (bdHom P))
    (fun a b => ker_bdHom_iff hK3 P a b) (proj_bdHom_neg_one hXP) (proj_swP_comm hXP)
    (fun a b => ?_) (conj_mem_range_L4 hK3 hXP) (eq_of_comm_range_L4 hK3 hXP)
    (Q5L4.noOddNormal_range_bdHom ⟨3, 1, Nat.prime_three, ⟨1, rfl⟩, le_rfl, hK⟩ P)
    (Q5L4.noQ8Fix_t2 h4 Nat.prime_three hK odd_one P)
  simp only [MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, hsi, swP_conj]

end Q3L4

end CFSG.ClassicalInvolution.Q3.TA3
