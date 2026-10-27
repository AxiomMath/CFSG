module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem isFieldType_of_isPlane625_six_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 6) {F : Subgroup G} (hFV : F ≤ V)
    (hF4 : Nat.card F = 4) {x y : Fin 2 → h.data.K} (hP : h.IsPlane625 F x y) :
    IsFieldType M L V F 1 := by
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T_F4 h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  have hfrob := (h.semilinear_cases_ch625 ⟨t₀, ht₀M.2⟩ (h.normal ht₀M.1)).resolve_left ht₀
  have hdet0 : det2 (h.data.conj ⟨t₀, ht₀M.2⟩ x) (h.data.conj ⟨t₀, ht₀M.2⟩ y) ≠ 0 := by
    rw [h.det2_conj_frob_ch625 hfrob]
    exact mul_ne_zero (pow_ne_zero 2 hP.1) (h.det625_ne_zero _ (h.normal ht₀M.1))
  obtain ⟨m, hmM, hmN, hmlin, hmx, hmy⟩ := h.exists_MV_basis_six_F4 h331 h615 hidx hdet0 hP.1
  exact h.isFieldType_of_isPlane625 hFV hF4 hP ht₀M ht₀ (l := ⟨m, hmN⟩) hmM hmlin hmx hmy

end Hyp6Sec2

end CFSG.Quasithin.H13
