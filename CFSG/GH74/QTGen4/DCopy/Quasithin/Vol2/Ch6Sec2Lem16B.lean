module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem16B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem16A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_comm_eq_U_ch616_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) :
    ∀ x ∈ V ⊓ uCh611 T L V, ∃ a ∈ uCh611 T L V, ⁅v, a⁆⁻¹ * x ∈ zCh611 T := by
  classical
  set U := uCh611 T L V with hUdef
  set Z := zCh611 T with hZdef
  obtain ⟨g, hg, hgk⟩ := h.exists_not_two_ch615_F4 h6210 hv
    (h.not_mem_C_ch615_F4 h6210 h6211 h6212 hlt hv hvU)
  obtain ⟨-, -, -, hDU⟩ :=
    h.pair_data_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hg hgk
  have hAU : conjSubgroup (V ⊓ U) g ≤ U := le_sup_right.trans hDU
  have hZ2 : Nat.card Z = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hV := h.toHyp611.isElemAbelian
  have hVU8 : Nat.card ↥(V ⊓ U) = 8 := by
    have := (stmt6_2_14_of_F4 h6210 h6211 h6212 G T M L V h hlt).2
    rw [this]; norm_num
  have hZVU : Z ≤ V ⊓ U := fun z hz =>
    ⟨((h.omega_le_ZS_F4 h331 h432 h512 h614 h615).trans inf_le_left) hz,
      (le_conjClosure (ch6ZS T L V) (hCh611 T)) (h.omega_le_ZS_F4 h331 h432 h512 h614 h615 hz)⟩
  obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
  have hcommVU : ∀ x ∈ V, ∀ u ∈ U, ⁅x, u⁆ ∈ V ⊓ U := fun x hx u hu =>
    hVUc (Subgroup.commutator_mem_commutator hx hu)
  intro x hx
  obtain ⟨a, ha, haz⟩ := exists_comm_eq_ch616 (A := conjSubgroup (V ⊓ U) g) (v := v)
    hZVU hZ2 (by rw [card_conjSubgroup, hVU8]) hVU8
    (fun a ha b hb => B2F.isElemAbelian_comm hV ha.1 hb.1)
    (fun a ha => hcommVU v hv a (hAU ha))
    (fun a ha b hb => by
      have := h.comm_mem_ch615_F4 h331 h432 h512 h614 h615 (hAU ha) (hcommVU v hv b (hAU hb)).2
      rwa [← commutatorElement_def] at this)
    (fun a ha hva => by
      by_contra haZ
      rw [commutatorElement_def] at hva
      exact h.comm_not_mem_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hvU hg
        hgk ha haZ hva) x hx
  exact ⟨a, hAU ha, haz⟩

theorem le_commutator_sup_ch616_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    V ⊓ uCh611 T L V ≤ ⁅V, uCh611 T L V⁆ ⊔ zCh611 T := by
  obtain ⟨v, hv, hvU⟩ := h.exists_not_mem_U_ch615_F4 h6210 h6211 h6212 hlt
  intro x hx
  obtain ⟨a, ha, haz⟩ :=
    h.exists_comm_eq_U_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hvU x hx
  have e : x = ⁅v, a⁆ * (⁅v, a⁆⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv ha))
    (Subgroup.mem_sup_right haz)

theorem comm_conj_eq_one_ch616_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) {v : G} (hv : v ∈ V) {u : G}
    (hu : u ∈ uCh611 T L V) : u * (v * u * v⁻¹) * u⁻¹ * (v * u * v⁻¹)⁻¹ = 1 := by
  have hV := h.toHyp611.isElemAbelian
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    h.toHyp611.T_le_normalizer (h.uCh611_le_T_F4 h331 h432 h512 h614 h615 hu)
  have hconj : ∀ x ∈ V, u * x * u⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp huN x).mp hx
  have hu2 : u ^ 2 ∈ zCh611 T := h.sq_mem_ch615_F4 h331 h432 h512 h614 h615 hu
  have hZV : zCh611 T ≤ V := (h.omega_le_ZS_F4 h331 h432 h512 h614 h615).trans inf_le_left
  have hvi : v⁻¹ = v := inv_eq_self_ch626 hV hv
  set x := u * v * u⁻¹ with hx
  have hxV : x ∈ V := hconj v hv
  have hxi : x⁻¹ = x := inv_eq_self_ch626 hV hxV

  have hux : u * x * u⁻¹ = v := by
    have hc : u ^ 2 * v = v * u ^ 2 := B2F.isElemAbelian_comm hV (hZV hu2) hv
    rw [hx]
    calc u * (u * v * u⁻¹) * u⁻¹ = u ^ 2 * v * (u ^ 2)⁻¹ := by rw [pow_two]; group
      _ = v := by rw [hc, mul_inv_cancel_right]
  set w := v * u * v⁻¹ * u⁻¹ with hw
  have hw' : w = v * x := by
    rw [hw, hx]
    calc v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
      _ = v * (u * v * u⁻¹)⁻¹ := by group
      _ = v * (u * v * u⁻¹) := by rw [← hx, hxi]
  have huw : u * w * u⁻¹ = w := by
    rw [hw']
    calc u * (v * x) * u⁻¹ = (u * v * u⁻¹) * (u * x * u⁻¹) := by group
      _ = x * v := by rw [← hx, hux]
      _ = v * x := B2F.isElemAbelian_comm hV hxV hv
  have e : v * u * v⁻¹ = w * u := by rw [hw]; group
  rw [e]
  calc u * (w * u) * u⁻¹ * (w * u)⁻¹ = (u * w * u⁻¹) * w⁻¹ := by group
    _ = 1 := by rw [huw, mul_inv_cancel]

end Hyp6Sec2

end CFSG.Quasithin.H13
