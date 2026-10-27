module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem17A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem10

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem centralizer_le_T_ch617_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) :
    (lsCh617 T L V ⊔ T) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ T := by
  rintro x ⟨hx, hxC⟩
  have hx' : x ∈ ((lsCh617 T L V ⊔ T : Subgroup G) : Set G) := hx
  rw [h.coe_sup_ch617] at hx'
  obtain ⟨t, ht, l, hl, htl⟩ := hx'
  replace htl : t * l = x := htl
  subst htl
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ zCh611 T, z ≠ 1 := by
    have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  have htz : t * z = z * t := by
    have hA := h.almostSpecialHyp_Gz_F4 h331 h432 h512 h614 h615
    exact (Subgroup.mem_centralizer_iff.mp (hA.sylow_H.1 ht) z hzZ).symm
  have hlz : l * z * l⁻¹ = z := by
    have h1 : (t * l) * z * (t * l)⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hxC z (hZZS hzZ), mul_inv_cancel_right]
    have e : l * z * l⁻¹ = t⁻¹ * ((t * l) * z * (t * l)⁻¹) * t := by group
    rw [e, h1, mul_assoc, ← htz, inv_mul_cancel_left]
  have hlL := (ls_le_ch617 hl).1
  have hlC := h.lin_fix_ch617 hlL (ls_le_ch617 hl).2 (hZZS hzZ) hz1 hlz
  exact T.mul_mem ht (h.mem_T_of_mem_L_ch611 hlL hlC)

theorem pCoreOf_le_centralizer_ch617_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) :
    pCoreOf 2 (lsCh617 T L V ⊔ T) ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  have hA := h.almostSpecialHyp_Gz_F4 h331 h432 h512 h614 h615
  have hTsyl : IsSylowTwoOf T (lsCh617 T L V ⊔ T) :=
    E6.isSylowIn_of_le (⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩)
      le_sup_right le_top
  have hOT : pCoreOf 2 (lsCh617 T L V ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  obtain ⟨d, hdLS, -, hdN, hfix⟩ := h.exists_diag_ch617
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ zCh611 T, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  set w := d⁻¹ * z * d with hw
  have hwZS : w ∈ ch6ZS T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) z).mp (hZZS hzZ)
    simpa [hw] using this
  have hwZ : w ∉ zCh611 T := by
    intro hwZ
    have hw1 : w ≠ 1 := fun h1 => hz1 (by
      have : z = d * w * d⁻¹ := by rw [hw]; group
      rw [this, h1]; group)
    have hwz : w = z := SteinbergBS.eq_of_card_le_two hZ2.le hwZ hzZ hw1 hz1
    have hdz : d * z * d⁻¹ = z := by
      have : z = d * w * d⁻¹ := by rw [hw]; group
      calc d * z * d⁻¹ = d * w * d⁻¹ := by rw [hwz]
        _ = z := this.symm
    exact hz1 (hfix z ((h.omega_le_ZS_F4 h331 h432 h512 h614 h615).trans inf_le_left hzZ) hdz)
  intro q hq
  have hqT := hOT hq
  have hdq : d * q * d⁻¹ ∈ pCoreOf 2 (lsCh617 T L V ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hdLS)) q).mp hq
  have hcz : ∀ y ∈ T, y * z = z * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hA.sylow_H.1 hy) z hzZ).symm
  have hqz := hcz q hqT
  have hqw : q * w = w * q := by
    have h1 := hcz _ (hOT hdq)
    rw [hw]
    calc q * (d⁻¹ * z * d) = d⁻¹ * ((d * q * d⁻¹) * z) * d := by group
      _ = d⁻¹ * (z * (d * q * d⁻¹)) * d := by rw [h1]
      _ = d⁻¹ * z * d * q := by group
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 hwZ hwZS hs with e | e | e | e
  · rw [e]; group
  · rw [e]; exact hqz.symm
  · rw [e]; exact hqw.symm
  · rw [e]
    calc z * w * q = z * (w * q) := by group
      _ = z * (q * w) := by rw [hqw]
      _ = (z * q) * w := by group
      _ = (q * z) * w := by rw [hqz]
      _ = q * (z * w) := by group

theorem centralizer_eq_ch617_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) :
    (lsCh617 T L V ⊔ T) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) =
      pCoreOf 2 (lsCh617 T L V ⊔ T) := by
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 _)
    (h.pCoreOf_le_centralizer_ch617_F4 h331 h432 h512 h614 h615))
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left
    ((le_inf Subgroup.le_normalizer (h.sup_le_normalizer_ZS_ch617.trans
      (normalizer_le_normalizer_centralizer'' (ch6ZS T L V)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf) ?_
  exact h.sylow.1.to_le (h.centralizer_le_T_ch617_F4 h331 h432 h512 h614 h615)

end Hyp6Sec2

end CFSG.Quasithin.H13
