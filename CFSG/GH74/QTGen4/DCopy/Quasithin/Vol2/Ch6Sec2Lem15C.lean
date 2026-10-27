module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem15C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem15B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem not_mem_C_ch615_F4 (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G} (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) :
    v ∉ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) := by
  intro hvC
  obtain ⟨-, -, hCQ⟩ := h6212 G T M L V h
  have hCQ' : centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) = pCoreOf 2 (hCh611 T) := hCQ
  have h14 : V ⊓ uCh611 T L V = V ⊓ pCoreOf 2 (hCh611 T) :=
    (stmt6_2_14_of_F4 h6210 h6211 h6212 G T M L V h hlt).1
  have : v ∈ V ⊓ pCoreOf 2 (hCh611 T) := ⟨hv, hCQ' ▸ hvC⟩
  rw [← h14] at this
  exact hvU this.2

theorem exists_not_mem_U_ch615_F4 (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) : ∃ v ∈ V, v ∉ uCh611 T L V := by
  by_contra hcon
  push Not at hcon
  have h8 : Nat.card ↥(V ⊓ uCh611 T L V) = 2 ^ 3 :=
    (stmt6_2_14_of_F4 h6210 h6211 h6212 G T M L V h hlt).2
  have : V ⊓ uCh611 T L V = V := inf_eq_left.mpr hcon
  rw [this, h.natural.card_eq] at h8
  norm_num at h8

theorem exists_extraspecial_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    ∃ U₀ : Subgroup G, U₀ ≤ uCh611 T L V ∧ uCh611 T L V = centerOf (uCh611 T L V) ⊔ U₀ ∧
      CFSG.IsExtraspecial 2 ↥U₀ ∧ 2 ^ 5 ≤ Nat.card U₀ ∧
      ∃ A : Subgroup G, A ≤ U₀ ∧ IsElemAbelian 2 A ∧ Nat.card A = 2 ^ 3 := by
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h_F4 h331 h432 h512 h614 h615
  have hZc : ∀ z ∈ zCh611 T, ∀ u ∈ uCh611 T L V, u * z = z * u := fun z hz u hu =>
    (Subgroup.mem_centralizer_iff.mp (hUH hu) z hz).symm
  have hsq : ∀ u ∈ uCh611 T L V, u ^ 2 ∈ zCh611 T := fun u hu =>
    h.sq_mem_ch615_F4 h331 h432 h512 h614 h615 hu
  have hcomm : ∀ a ∈ uCh611 T L V, ∀ b ∈ uCh611 T L V, a * b * a⁻¹ * b⁻¹ ∈ zCh611 T :=
    fun a ha b hb => h.comm_mem_ch615_F4 h331 h432 h512 h614 h615 ha hb

  obtain ⟨v, hv, hvU⟩ := h.exists_not_mem_U_ch615_F4 h6210 h6211 h6212 hlt
  obtain ⟨g, hg, hgk⟩ := h.exists_not_two_ch615_F4 h6210 hv
    (h.not_mem_C_ch615_F4 h6210 h6211 h6212 hlt hv hvU)
  obtain ⟨-, ⟨D, hDX, hXD, hDext, -⟩, -, hOU⟩ :=
    h.two_six_ch615_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hg hgk
  obtain ⟨hDes, hD32, E, hED, hEab, hE8⟩ := hDext
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 5) (by rw [hD32])
  have hDU : D ≤ uCh611 T L V := (le_pCoreOf_of_le_normalizer 2 hDX hXD hD2).trans hOU
  obtain ⟨hDna, hZD, hcenD⟩ := extraspecial_facts_ch615 hZ2 hDU hZc hcomm hDes
  obtain ⟨U₀, hDU₀, hU₀U, hsup, hcap⟩ :=
    exists_complement_ch615 hZc hsq hcomm hDU hZD hcenD
  have hna : ∃ a ∈ U₀, ∃ b ∈ U₀, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hDna
    exact ⟨a, hDU₀ ha, b, hDU₀ hb, hab⟩
  refine ⟨U₀, hU₀U, by rw [sup_comm, hsup],
    isExtraspecial_ch615 hZ2 (hZD.trans hDU₀) hU₀U hsup hcap hZc hsq hcomm hna, ?_,
    E, hED.trans hDU₀, hEab, hE8⟩
  exact (show 2 ^ 5 = Nat.card D by rw [hD32]).trans_le (Subgroup.card_le_of_le hDU₀)

end Hyp6Sec2

end CFSG.Quasithin.H13
