module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_conj_of_type3_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) {F F' : Subgroup G}
    (hFV : F ≤ V) (hF4 : Nat.card F = 4) (hF'V : F' ≤ V) (hF'4 : Nat.card F' = 4)
    (hFc : ¬ IsCentralType L V F 1) (hFf : ¬ IsFieldType M L V F 1)
    (hF'c : ¬ IsCentralType L V F' 1) (hF'f : ¬ IsFieldType M L V F' 1) :
    ∃ m ∈ ch6MV M V, F' = conjSubgroup F m := by
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T_F4 h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  set tt : Subgroup.normalizer (V : Set G) := ⟨t₀, ht₀M.2⟩ with htt
  have hd0 : h.det625 tt ≠ 0 := h.det625_ne_zero _ (h.normal ht₀M.1)
  obtain ⟨x, y, hP⟩ := h.isPlane625_of_not_central hFV hF4 hFc
  obtain ⟨x', y', hP'⟩ := h.isPlane625_of_not_central hF'V hF'4 hF'c
  have hne : det2 x y ≠ (h.det625 tt)⁻¹ := fun he =>
    hFf (h.isFieldType_of_det hFV hF4 hP ht₀M ht₀ he)
  have hne' : det2 x' y' ≠ (h.det625 tt)⁻¹ := fun he =>
    hF'f (h.isFieldType_of_det hF'V hF'4 hP' ht₀M ht₀ he)
  by_cases heq : det2 x' y' = det2 x y
  · obtain ⟨l, hlL, hlx, hly⟩ := h.exists_L_basis_ch625 hP'.1 heq.symm
    exact ⟨l, h.L_le_MV_ch625 hlL, h.eq_conjSubgroup_of_isPlane625 hFV hF'V hP hP' l hlx hly⟩
  · have hδ' := h.eq_mul_sq_of_ne_ch625 hd0 hP.1 hP'.1 hne hne' heq
    have hfrob := (h.semilinear_cases_ch625 tt (h.normal ht₀M.1)).resolve_left ht₀
    have hdt : det2 (h.data.conj tt x) (h.data.conj tt y) = det2 x' y' := by
      rw [h.det2_conj_frob_ch625 hfrob, hδ']
      ring
    obtain ⟨l, hlL, hlx, hly⟩ := h.exists_L_basis_ch625 hP'.1 hdt
    refine ⟨((tt⁻¹ * l : Subgroup.normalizer (V : Set G)) : G),
      (ch6MV M V).mul_mem ((ch6MV M V).inv_mem ht₀M) (h.L_le_MV_ch625 hlL), ?_⟩
    exact h.eq_conjSubgroup_of_isPlane625 hFV hF'V hP hP' (tt⁻¹ * l)
      (by rw [h.data.conj_mul, hlx, h.conj_inv_conj_ch625])
      (by rw [h.data.conj_mul, hly, h.conj_inv_conj_ch625])

theorem exists_type3_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 2) :
    ∃ F : Subgroup G, F ≤ V ∧ Nat.card F = 4 ∧ ¬ IsCentralType L V F 1 ∧
      ¬ IsFieldType M L V F 1 := by
  have hK := h.card_K_ch625
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T_F4 h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  set d := h.det625 ⟨t₀, ht₀M.2⟩ with hd
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_ch625 hK
  obtain ⟨c, hc0, hcd⟩ : ∃ c : h.data.K, c ≠ 0 ∧ c ≠ d⁻¹ := by
    by_cases h1 : (1 : h.data.K) = d⁻¹
    · exact ⟨ω, hω0, fun h2 => hω1 (h2.trans h1.symm)⟩
    · exact ⟨1, one_ne_zero, h1⟩
  set x : Fin 2 → h.data.K := ![1, 0] with hx
  set y : Fin 2 → h.data.K := c • ![0, 1] with hy
  have hxy : det2 x y = c := by rw [hy, det2_smul_right_ch625, det2_e_ch625, mul_one]
  have hxy0 : det2 x y ≠ 0 := by rw [hxy]; exact hc0
  set F := h.data.subOf (planeAddSub hK x y) with hF
  have hFV : F ≤ V := h.data.subOf_le _
  have hP : h.IsPlane625 F x y := by
    refine ⟨hxy0, fun w => ?_⟩
    rw [← mem_planeAddSub hK, ← h.data.addSub_subOf (planeAddSub hK x y)]
    exact (h.data.mem_addSub).symm
  have hF4 : Nat.card F = 4 := by
    rw [← h.data.card_addSub hFV, h.data.addSub_subOf, card_planeAddSub hK hxy0]
  refine ⟨F, hFV, hF4, h.not_central_of_isPlane625 hFV hF4 hP, fun hf => ?_⟩
  obtain ⟨t, htM, htN, hlin, hdet⟩ := h.fieldType_det hFV hF4 hf hP
  have := h.det625_eq_of_not_lin hidx htM ht₀M hlin ht₀
  rw [hdet, hxy] at this
  exact hcd (by rw [hd, ← this, inv_inv])

end Hyp6Sec2

end CFSG.Quasithin.H13
