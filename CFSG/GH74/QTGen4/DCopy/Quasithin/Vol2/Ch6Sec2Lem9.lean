module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

theorem stmt6_2_9_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4) (h614 : Stmt6_1_4_F4)
    (h615 : Stmt6_1_5_F4) : Stmt6_2_9_F4 := by
  intro G _ _ T M L V h H K
  set Z := quasithinOmegaOneCenter T with hZ
  have hZV : Z ≤ V := h.omega_le_V_F4 h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZ1 : Z ≠ ⊥ := by
    intro h0
    have : Nat.card Z = 1 := by rw [h0, Subgroup.card_bot]
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ1
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  have hzZS : (z : G) ∈ ch6ZS T L V := ⟨hZV z.2, Subgroup.centralizer_le inf_le_left (hZC z.2)⟩
  have hz1' : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hNV := h.normalizer_V_le_F4 h432
  have hHN : H ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  have hVH : V ≤ H := fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    B2F.isElemAbelian_comm h.toHyp611.isElemAbelian (hZV hw) hv
  have hKH : K ≤ H :=
    conjClosure_le fun a ha v hv => H.mul_mem (H.mul_mem ha (hVH hv)) (H.inv_mem ha)

  have key : ∀ x ∈ H, x ∈ Subgroup.normalizer (V : Set G) →
      x ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    intro x hxH hxV
    refine h.mem_normalizer_ZS_of_fix hxV (h.normal (hNV hxV)) hzZS hz1' ?_
    exact (Subgroup.mem_centralizer_iff.mp hxH z z.2).symm
  have hZSV := h.normalizer_ZS_le_F4 h432
  refine ⟨h.toHyp611Nat.inf_eq_inf_normalizer hNV hZ1 hZV hHN, ?_,
    h.toHyp611Nat.inf_eq_inf_normalizer hNV hZ1 hZV (hKH.trans hHN), ?_⟩
  · exact le_antisymm (le_inf inf_le_left fun x hx => key x hx.1 hx.2)
      (inf_le_inf_left _ hZSV)
  · exact le_antisymm (le_inf inf_le_left fun x hx => key x (hKH hx.1) hx.2)
      (inf_le_inf_left _ hZSV)

end CFSG.Quasithin.H13
