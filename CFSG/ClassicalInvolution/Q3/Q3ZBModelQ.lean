module

public import CFSG.ClassicalInvolution.Q3.Q3ZBModelD
public import CFSG.ClassicalInvolution.Q3.Q3T6FaAut
public import CFSG.ClassicalInvolution.Q3.Q3T6FaField

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3ZA
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups
open Matrix

@[expose] noncomputable def qexpElt (a b c : F3) : StatedSp 2 F3 :=
  sb (usl a) * (weyl₁ * sb (usl b) * weyl₁⁻¹) * longBlock F3 2 0 (usl (c - a * b))

local macro "qe_simp" : tactic =>
  `(tactic| simp only [qexpElt, map_mul, ← Matrix.mulVec_mulVec, sb_usl_e0, sb_usl_e1, sb_usl_f0,
    sb_usl_f1, w1_e0, w1_e1, w1_f0, w1_f1, w1i_e0, w1i_e1, w1i_f0, w1i_f1, lb0u_e0, lb0u_e1,
    lb0u_f0, lb0u_f1, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul,
    Matrix.mulVec_sub, neg_neg])

theorem qexpElt_e0 (a b c : F3) : mat 2 F3 (qexpElt a b c) *ᵥ bE0 = bE0 := by
  qe_simp

theorem qexpElt_e1 (a b c : F3) : mat 2 F3 (qexpElt a b c) *ᵥ bE1 = bE1 + a • bE0 := by
  qe_simp

theorem qexpElt_f1 (a b c : F3) : mat 2 F3 (qexpElt a b c) *ᵥ bF1 = bF1 + b • bE0 := by
  qe_simp

theorem qexpElt_f0 (a b c : F3) :
    mat 2 F3 (qexpElt a b c) *ᵥ bF0 = bF0 + c • bE0 + b • bE1 - a • bF1 := by
  qe_simp
  module

theorem qexpElt_congr {a b c a' b' c' : F3} (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    qexpElt a b c = qexpElt a' b' c' := by
  subst h1 h2 h3
  rfl

local macro "qe_act" : tactic =>
  `(tactic| simp only [map_mul, ← Matrix.mulVec_mulVec, qexpElt_e0, qexpElt_e1, qexpElt_f0,
    qexpElt_f1, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, Matrix.mulVec_sub,
    map_one, Matrix.one_mulVec])

theorem qexpElt_mul (a b c a' b' c' : F3) :
    qexpElt a b c * qexpElt a' b' c' = qexpElt (a + a') (b + b') (c + c' + a * b' - a' * b) := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (qe_act; try module)

theorem qexpElt_mul_eq {a b c a' b' c' a'' b'' c'' : F3} (h1 : a + a' = a'')
    (h2 : b + b' = b'') (h3 : c + c' + a * b' - a' * b = c'') :
    qexpElt a b c * qexpElt a' b' c' = qexpElt a'' b'' c'' := by
  rw [qexpElt_mul]
  exact qexpElt_congr h1 h2 h3

theorem qexpElt_zero : qexpElt 0 0 0 = 1 := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (qe_act; try module)

theorem qexpElt_mul_neg (a b c : F3) : qexpElt a b c * qexpElt (-a) (-b) (-c) = 1 := by
  rw [qexpElt_mul, add_neg_cancel, add_neg_cancel, show c + -c + a * -b - -a * b = 0 by ring,
    qexpElt_zero]

theorem qexpElt_inv (a b c : F3) : (qexpElt a b c)⁻¹ = qexpElt (-a) (-b) (-c) :=
  inv_eq_of_mul_eq_one_right (qexpElt_mul_neg a b c)

theorem sbU_eq_qexpElt : sbU = qexpElt 1 0 0 := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;>
    (simp only [sbU_eq, sb_usl_e0, sb_usl_e1, sb_usl_f0, sb_usl_f1, qexpElt_e0, qexpElt_e1,
      qexpElt_f0, qexpElt_f1]; try module)

theorem qSp_eq_qexpElt : qSp = qexpElt 0 1 0 := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;>
    (simp only [qSp_e0, qSp_e1, qSp_f0, qSp_f1, qexpElt_e0, qexpElt_e1, qexpElt_f0, qexpElt_f1];
      try module)

theorem tHub_eq_qexpElt : tHub = qexpElt 0 0 1 := by
  unfold tHub
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;>
    (simp only [uSL_eq, lb0u_e0, lb0u_e1, lb0u_f0, lb0u_f1, qexpElt_e0, qexpElt_e1,
      qexpElt_f0, qexpElt_f1]; try module)

local macro "lb_act" : tactic =>
  `(tactic| simp only [map_mul, ← Matrix.mulVec_mulVec, qexpElt_e0, qexpElt_e1, qexpElt_f0,
    qexpElt_f1, uSL_eq, lSL_eq, lb1u_e0, lb1u_e1, lb1u_f0, lb1u_f1, lb1l_e0, lb1l_e1, lb1l_f0,
    lb1l_f1, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, Matrix.mulVec_sub])

theorem lb1U_mul_qexpElt (a b c : F3) :
    longBlock F3 2 1 uSL * qexpElt a b c = qexpElt a (b - a) c * longBlock F3 2 1 uSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (lb_act; try module)

theorem lb1L_mul_qexpElt (a b c : F3) :
    longBlock F3 2 1 lSL * qexpElt a b c = qexpElt (a - b) b c * longBlock F3 2 1 lSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (lb_act; try module)

theorem qexpElt_mem_DHub (a b c : F3) : qexpElt a b c ∈ DHub := by
  rw [mem_DHub, tHub_eq_qexpElt, qexpElt_mul, qexpElt_mul]
  exact qexpElt_congr (by ring) (by ring) (by ring)

theorem qexpElt_entry_e0 (a b c : F3) (r : Fin 2 ⊕ Fin 2) :
    mat 2 F3 (qexpElt a b c) r (Sum.inl 0) = (bE0 : V4) r := by
  have h := congrFun (qexpElt_e0 a b c) r
  rwa [mulVec_single_one_apply] at h

theorem qexpElt_entry_e1 (a b c : F3) (r : Fin 2 ⊕ Fin 2) :
    mat 2 F3 (qexpElt a b c) r (Sum.inl 1) = (bE1 + a • bE0 : V4) r := by
  have h := congrFun (qexpElt_e1 a b c) r
  rwa [mulVec_single_one_apply] at h

theorem qexpElt_entry_f1 (a b c : F3) (r : Fin 2 ⊕ Fin 2) :
    mat 2 F3 (qexpElt a b c) r (Sum.inr 1) = (bF1 + b • bE0 : V4) r := by
  have h := congrFun (qexpElt_f1 a b c) r
  rwa [mulVec_single_one_apply] at h

theorem qexpElt_mem_Qexp (a b c : F3) : qexpElt a b c ∈ Qexp := by
  refine mem_Qexp.2 ⟨qexpElt_mem_DHub a b c, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkSL_coe, blkMat, qexpElt_entry_e1, qexpElt_entry_f1]
  · simp [epsHom, qexpElt_entry_e0]

theorem exists_qexpElt_of_mem_Qexp {g : StatedSp 2 F3} (hg : g ∈ Qexp) :
    ∃ a b c : F3, g = qexpElt a b c := by
  obtain ⟨hD, hb, he⟩ := mem_Qexp.1 hg
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := entries_of_mem_DHub hD
  have he' : mat 2 F3 g (Sum.inl 0) (Sum.inl 0) = 1 := he
  have hb' := fun i j => congrArg (fun A : SL(2, F3) => (A : Matrix (Fin 2) (Fin 2) F3) i j) hb
  have b11 : mat 2 F3 g (Sum.inl 1) (Sum.inl 1) = 1 := by simpa [blkSL_coe, blkMat] using hb' 0 0
  have b12 : mat 2 F3 g (Sum.inl 1) (Sum.inr 1) = 0 := by simpa [blkSL_coe, blkMat] using hb' 0 1
  have b21 : mat 2 F3 g (Sum.inr 1) (Sum.inl 1) = 0 := by simpa [blkSL_coe, blkMat] using hb' 1 0
  have b22 : mat 2 F3 g (Sum.inr 1) (Sum.inr 1) = 1 := by simpa [blkSL_coe, blkMat] using hb' 1 1
  have s1 := form_mulVec g bE1 bF0
  have s2 := form_mulVec g bF1 bF0
  simp [form_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply, sgn, par] at s1 s2
  have hff : mat 2 F3 g (Sum.inr 0) (Sum.inr 0) = 1 := by rw [z6, he']
  have h10 : mat 2 F3 g (Sum.inr 1) (Sum.inr 0) = -mat 2 F3 g (Sum.inl 0) (Sum.inl 1) := by
    rw [hff, b11, b21, z4] at s1
    linear_combination s1
  have h01 : mat 2 F3 g (Sum.inl 1) (Sum.inr 0) = mat 2 F3 g (Sum.inl 0) (Sum.inr 1) := by
    rw [hff, b12, b22, z5] at s2
    linear_combination -s2
  refine ⟨mat 2 F3 g (Sum.inl 0) (Sum.inl 1), mat 2 F3 g (Sum.inl 0) (Sum.inr 1),
    mat 2 F3 g (Sum.inl 0) (Sum.inr 0), ?_⟩
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_
  · rw [qexpElt_e0]
    funext r
    rw [mulVec_single_one_apply]
    rcases r with r | r <;> fin_cases r <;> simp [he', z1, z2, z3]
  · rw [qexpElt_e1]
    funext r
    rw [mulVec_single_one_apply]
    rcases r with r | r <;> fin_cases r <;> simp [b11, b21, z4]
  · rw [qexpElt_f0]
    funext r
    rw [mulVec_single_one_apply]
    rcases r with r | r <;> fin_cases r <;> simp [hff, h10, h01]
  · rw [qexpElt_f1]
    funext r
    rw [mulVec_single_one_apply]
    rcases r with r | r <;> fin_cases r <;> simp [b12, b22, z5]

theorem tHub_mem_Qexp : tHub ∈ Qexp := by
  rw [tHub_eq_qexpElt]
  exact qexpElt_mem_Qexp 0 0 1

theorem sbU_mem_Qexp : sbU ∈ Qexp := by
  rw [sbU_eq_qexpElt]
  exact qexpElt_mem_Qexp 1 0 0

theorem qSp_mem_Qexp : qSp ∈ Qexp := by
  rw [qSp_eq_qexpElt]
  exact qexpElt_mem_Qexp 0 1 0

theorem Qexp_cube {g : StatedSp 2 F3} (hg : g ∈ Qexp) : g * g * g = 1 := by
  obtain ⟨a, b, c, rfl⟩ := exists_qexpElt_of_mem_Qexp hg
  have h3 := three_eq_zero_f3
  rw [qexpElt_mul, qexpElt_mul, qexpElt_congr (a' := 0) (b' := 0) (c' := 0)
    (by linear_combination a * h3) (by linear_combination b * h3) (by linear_combination c * h3),
    qexpElt_zero]

theorem qexpElt_mem_of_gens {N' : Subgroup (StatedSp 2 F3)} (hs : sbU ∈ N') (hq : qSp ∈ N')
    (ht : tHub ∈ N') (a b c : F3) : qexpElt a b c ∈ N' := by
  have hx : ∀ x : F3, qexpElt x 0 0 ∈ N' ∧ qexpElt 0 x 0 ∈ N' ∧ qexpElt 0 0 x ∈ N' := by
    intro x
    rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl
    · rw [qexpElt_zero]
      exact ⟨N'.one_mem, N'.one_mem, N'.one_mem⟩
    · rw [sbU_eq_qexpElt] at hs
      rw [qSp_eq_qexpElt] at hq
      rw [tHub_eq_qexpElt] at ht
      exact ⟨hs, hq, ht⟩
    · rw [sbU_eq_qexpElt] at hs
      rw [qSp_eq_qexpElt] at hq
      rw [tHub_eq_qexpElt] at ht
      have e1 : qexpElt (-1) 0 0 = (qexpElt 1 0 0)⁻¹ := by rw [qexpElt_inv, neg_zero]
      have e2 : qexpElt 0 (-1) 0 = (qexpElt 0 1 0)⁻¹ := by rw [qexpElt_inv, neg_zero]
      have e3 : qexpElt 0 0 (-1) = (qexpElt 0 0 1)⁻¹ := by rw [qexpElt_inv, neg_zero]
      rw [e1, e2, e3]
      exact ⟨N'.inv_mem hs, N'.inv_mem hq, N'.inv_mem ht⟩
  have e : qexpElt a b c = qexpElt a 0 0 * qexpElt 0 b 0 * qexpElt 0 0 (c - a * b) := by
    rw [qexpElt_mul_eq (a'' := a) (b'' := b) (c'' := a * b) (by ring) (by ring) (by ring),
      qexpElt_mul]
    exact qexpElt_congr (by ring) (by ring) (by ring)
  rw [e]
  exact N'.mul_mem (N'.mul_mem (hx a).1 (hx b).2.1) (hx _).2.2

theorem Qexp_le_of_gens {N' : Subgroup (StatedSp 2 F3)} (hs : sbU ∈ N') (hq : qSp ∈ N')
    (ht : tHub ∈ N') : Qexp ≤ N' := by
  intro g hg
  obtain ⟨a, b, c, rfl⟩ := exists_qexpElt_of_mem_Qexp hg
  exact qexpElt_mem_of_gens hs hq ht a b c

theorem Qexp_eq_closure : Qexp = Subgroup.closure {sbU, qSp, tHub} := by
  refine le_antisymm (Qexp_le_of_gens (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) ?_
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact sbU_mem_Qexp
  · exact qSp_mem_Qexp
  · exact tHub_mem_Qexp

theorem conj_lb1U (a b c : F3) :
    longBlock F3 2 1 uSL * qexpElt a b c * (longBlock F3 2 1 uSL)⁻¹ = qexpElt a (b - a) c := by
  rw [mul_inv_eq_iff_eq_mul]
  exact lb1U_mul_qexpElt a b c

theorem conj_lb1L (a b c : F3) :
    longBlock F3 2 1 lSL * qexpElt a b c * (longBlock F3 2 1 lSL)⁻¹ = qexpElt (a - b) b c := by
  rw [mul_inv_eq_iff_eq_mul]
  exact lb1L_mul_qexpElt a b c

theorem lb1U_sbU :
    longBlock F3 2 1 uSL * sbU * (longBlock F3 2 1 uSL)⁻¹ = sbU * qSp⁻¹ * tHub := by
  rw [sbU_eq_qexpElt, qSp_eq_qexpElt, tHub_eq_qexpElt, qexpElt_inv, conj_lb1U,
    qexpElt_mul_eq (a'' := 1) (b'' := -1) (c'' := -1) (by ring) (by ring) (by ring),
    qexpElt_mul]
  exact qexpElt_congr (by ring) (by ring) (by ring)

theorem lb1L_qSp :
    longBlock F3 2 1 lSL * qSp * (longBlock F3 2 1 lSL)⁻¹ = qSp * sbU⁻¹ * tHub⁻¹ := by
  rw [sbU_eq_qexpElt, qSp_eq_qexpElt, tHub_eq_qexpElt, qexpElt_inv, qexpElt_inv, conj_lb1L,
    qexpElt_mul_eq (a'' := -1) (b'' := 1) (c'' := 1) (by ring) (by ring) (by ring),
    qexpElt_mul]
  exact qexpElt_congr (by ring) (by ring) (by ring)

theorem Qexp_le_of_conj {N' : Subgroup (StatedSp 2 F3)}
    (h1 : ∀ y, longBlock F3 2 1 y ∈ N')
    (h2 : ∀ c ∈ DHub, ∀ y, c * longBlock F3 2 1 y * c⁻¹ ∈ N') : Qexp ≤ N' := by
  have hk' : (longBlock F3 2 1 uSL)⁻¹ ∈ N' := N'.inv_mem (h1 uSL)
  have hcomm : ∀ a : F3, a * a = 1 → qexpElt 0 a 1 ∈ N' := by
    intro a ha
    have hd := h2 _ (Qexp_le_DHub (qexpElt_mem_Qexp a 0 0)) uSL
    have e : qexpElt a 0 0 * longBlock F3 2 1 uSL * (qexpElt a 0 0)⁻¹ *
        (longBlock F3 2 1 uSL)⁻¹ = qexpElt 0 a 1 := by
      calc qexpElt a 0 0 * longBlock F3 2 1 uSL * (qexpElt a 0 0)⁻¹ * (longBlock F3 2 1 uSL)⁻¹
          = qexpElt a 0 0 * (longBlock F3 2 1 uSL * (qexpElt a 0 0)⁻¹ *
              (longBlock F3 2 1 uSL)⁻¹) := by group
        _ = qexpElt 0 a 1 := by
          rw [qexpElt_inv, conj_lb1U, qexpElt_mul]
          exact qexpElt_congr (by ring) (by ring) (by linear_combination ha)
    rw [← e]
    exact N'.mul_mem hd hk'
  have h11 := hcomm 1 (by ring)
  have h12 := hcomm (-1) (by ring)
  have ht2 : qexpElt 0 0 (1 + 1) ∈ N' := by
    have e : qexpElt 0 1 1 * qexpElt 0 (-1) 1 = qexpElt 0 0 (1 + 1) :=
      qexpElt_mul_eq (by ring) (by ring) (by ring)
    rw [← e]
    exact N'.mul_mem h11 h12
  have ht : tHub ∈ N' := by
    have e : qexpElt 0 0 (1 + 1) * qexpElt 0 0 (1 + 1) = tHub := by
      rw [tHub_eq_qexpElt]
      exact qexpElt_mul_eq (by ring) (by ring) (by linear_combination three_eq_zero_f3)
    rw [← e]
    exact N'.mul_mem ht2 ht2
  have hq : qSp ∈ N' := by
    have e : qexpElt 0 1 1 * tHub⁻¹ = qSp := by
      rw [qSp_eq_qexpElt, tHub_eq_qexpElt, qexpElt_inv, qexpElt_mul]
      exact qexpElt_congr (by ring) (by ring) (by ring)
    rw [← e]
    exact N'.mul_mem h11 (N'.inv_mem ht)
  have hs : sbU ∈ N' := by
    have e : sbU = (longBlock F3 2 1 wSL)⁻¹ * qSp * longBlock F3 2 1 wSL := by
      rw [qSp, weyl₁]
      group
    rw [e]
    exact N'.mul_mem (N'.mul_mem (N'.inv_mem (h1 wSL)) hq) (h1 wSL)
  exact Qexp_le_of_gens hs hq ht

theorem DHub_le_of_conj {N' : Subgroup (StatedSp 2 F3)}
    (h1 : ∀ y, longBlock F3 2 1 y ∈ N')
    (h2 : ∀ c ∈ DHub, ∀ y, c * longBlock F3 2 1 y * c⁻¹ ∈ N')
    (h3 : longInv F3 2 0 ∈ N') : DHub ≤ N' := by
  intro g hg
  obtain ⟨q, hq, y, hy | hy⟩ := DHub_decomp hg
  · rw [hy]
    exact N'.mul_mem (Qexp_le_of_conj h1 h2 hq) (h1 y)
  · rw [hy]
    exact N'.mul_mem (N'.mul_mem (Qexp_le_of_conj h1 h2 hq) (h1 y)) h3

theorem swap_sbU_conj : swapElt * sbU * swapElt⁻¹ = sbL := by
  rw [mul_inv_eq_iff_eq_mul, sbU_eq, sbL_eq]
  exact swap_mul_sbU 1

theorem swap_qSp_conj : swapElt * qSp * swapElt⁻¹ = qSp := by
  rw [mul_inv_eq_iff_eq_mul]
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;>
    (simp only [map_mul, ← Matrix.mulVec_mulVec, swap_e0, swap_e1, swap_f0, swap_f1, qSp_e0,
      qSp_e1, qSp_f0, qSp_f1, Matrix.mulVec_add]; try module)

theorem swap_tHub_conj : swapElt * tHub * swapElt⁻¹ = longBlock F3 2 1 uSL := by
  rw [mul_inv_eq_iff_eq_mul, tHub]
  exact swap_mul_lb uSL

end CFSG.ClassicalInvolution.Q3.Q3ZB
