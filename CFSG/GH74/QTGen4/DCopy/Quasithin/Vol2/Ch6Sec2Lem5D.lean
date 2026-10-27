module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_not_lin_T_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) :
    ∃ t, ∃ ht : t ∈ T, ¬ h.IsLin625 ⟨t, h.toHyp611.T_le_normalizer ht⟩ := by
  obtain ⟨t, htT, htZ⟩ := h.exists_not_mem_centralizer_ZS_F4 h331 h615
  refine ⟨t, htT, fun hlin => htZ ?_⟩
  obtain ⟨v, hv, hle⟩ := h.toHyp611Nat.exists_line
  exact h.toHyp611Nat.mem_centralizer_ZS_of_linear hv hle htT hlin

theorem relIndex_le_two_of_det_eq_one_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4)
    (hall : ∀ m (hm : m ∈ ch6MV M V), h.IsLin625 ⟨m, hm.2⟩ → h.det625 ⟨m, hm.2⟩ = 1) :
    (autOn L V).relIndex (autOn (ch6MV M V) V) ≤ 2 := by
  have hK := h.card_K_ch625
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T_F4 h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  set K' := autOn (ch6MV M V) V with hK'
  set H' := (autOn L V).subgroupOf K' with hH'
  set τ : ↥K' := ⟨conjAct V ⟨t₀, ht₀M.2⟩, conjAct_mem_autOn_MV ht₀M⟩ with hτ

  have hcases : ∀ φ : ↥K', φ ∈ H' ∨ φ⁻¹ * τ ∈ H' := by
    rintro ⟨φ, hφ⟩
    obtain ⟨m, hmM, rfl⟩ := mem_autOn_iff.mp hφ
    have hmM' : (m : G) ∈ ch6MV M V := hmM
    by_cases hlin : h.IsLin625 m
    · left
      obtain ⟨y, hyL, hy⟩ := h.exists_L_of_det_one (h.normal hmM'.1) hlin (hall m hmM' hlin)
      rw [Subgroup.mem_subgroupOf]
      exact mem_autOn_iff.mpr ⟨y, hyL, (h.conjAct_eq_of_conj_eq hy).symm⟩
    · right
      have hfm := (h.semilinear_cases_ch625 m (h.normal hmM'.1)).resolve_left hlin
      have hft := (h.semilinear_cases_ch625 ⟨t₀, ht₀M.2⟩ (h.normal ht₀M.1)).resolve_left ht₀
      set n : Subgroup.normalizer (V : Set G) := m⁻¹ * ⟨t₀, ht₀M.2⟩ with hn
      have hnM : (n : G) ∈ ch6MV M V :=
        (ch6MV M V).mul_mem ((ch6MV M V).inv_mem hmM') ht₀M
      have hfminv : ∀ (c : h.data.K) w, h.data.conj m⁻¹ (c • w) = c ^ 2 • h.data.conj m⁻¹ w := by
        intro c w
        apply (h.data.conj m).injective
        rw [h.conj_conj_inv_ch625, hfm, h.conj_conj_inv_ch625, sq_sq_ch625 hK]
      have hnlin : h.IsLin625 n := by
        intro c w
        rw [hn, h.data.conj_mul, h.data.conj_mul, hft, hfminv, sq_sq_ch625 hK]
      obtain ⟨y, hyL, hy⟩ := h.exists_L_of_det_one (h.normal hnM.1) hnlin (hall n hnM hnlin)
      rw [Subgroup.mem_subgroupOf]
      have e : ((⟨conjAct V m, hφ⟩ : ↥K')⁻¹ * τ : ↥K').1 = conjAct V n := by
        simp [hτ, hn, map_mul, map_inv]
      rw [e]
      exact mem_autOn_iff.mpr ⟨y, hyL, (h.conjAct_eq_of_conj_eq hy).symm⟩

  have hsurj : Function.Surjective (fun b : Bool =>
      if b then (QuotientGroup.mk τ : ↥K' ⧸ H') else (QuotientGroup.mk 1 : ↥K' ⧸ H')) := by
    intro q
    obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective q
    rcases hcases φ with hφ | hφ
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [QuotientGroup.eq]
      simpa using hφ
    · refine ⟨true, ?_⟩
      simp only [↓reduceIte]
      rw [QuotientGroup.eq]
      simpa [mul_inv_rev] using H'.inv_mem hφ
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
  exact h2

theorem exists_scalar_of_six_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 6) :
    ∃ s ∈ ch6MV M V, ∃ μ : h.data.K, μ ≠ 0 ∧ μ ≠ 1 ∧
      ∀ hs : s ∈ Subgroup.normalizer (V : Set G), ∀ w, h.data.conj ⟨s, hs⟩ w = μ • w := by
  by_contra hcon
  have hall : ∀ m (hm : m ∈ ch6MV M V), h.IsLin625 ⟨m, hm.2⟩ → h.det625 ⟨m, hm.2⟩ = 1 := by
    intro m hm hlin
    by_contra hdet
    exact hcon (h.exists_scalar_of_det_ne_one hm hlin hdet)
  have := h.relIndex_le_two_of_det_eq_one_F4 h331 h615 hall
  omega

theorem exists_MV_basis_six_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 6) {x y x' y' : Fin 2 → h.data.K}
    (hxy : det2 x y ≠ 0) (hxy' : det2 x' y' ≠ 0) :
    ∃ m ∈ ch6MV M V, ∃ hm : m ∈ Subgroup.normalizer (V : Set G), h.IsLin625 ⟨m, hm⟩ ∧
      h.data.conj ⟨m, hm⟩ x = x' ∧ h.data.conj ⟨m, hm⟩ y = y' := by
  obtain ⟨s, hsM, μ, hμ0, hμ1, hs⟩ := h.exists_scalar_of_six_F4 h331 h615 hidx
  exact h.exists_MV_basis_of_scalar hsM hμ0 hμ1 hs hxy hxy'

end Hyp6Sec2

end CFSG.Quasithin.H13
