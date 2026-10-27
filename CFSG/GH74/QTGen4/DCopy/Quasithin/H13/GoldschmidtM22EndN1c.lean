module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN1c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN1b

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

section Main

variable [Fact (IsElemAbelianMod (UU T L V) (quasithinOmegaOneCenter T))]
  (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
  (h6210 : Stmt6_2_10_F4) (hZS : ch6ZS T L V = V ⊓ UU T L V)
  (z₀ : G) (hz₀ : z₀ ∈ ch6ZS T L V) (hz₀Z : z₀ ∉ quasithinOmegaOneCenter T)
  (hw : ∀ (z : G) (hz : z ∈ ch6ZS T L V),
    zt T L V z hz = 1 ∨ zt T L V z hz = zt T L V z₀ hz₀)
  (a : ↥(HH T)) (haV : (a : G) ∈ V) (ha1 : rep T L V a ≠ 1)

include h hZS h6210 hw haV ha1 in

theorem commV_rep_eq_F4 : commV (Subgroup.zpowers (rep T L V a)) =
    Subgroup.zpowers (zt T L V z₀ hz₀) := by
  have hform := rep_form_F4 h h6210 hZS z₀ hz₀ hw a haV
  have ha2 : rep T L V a * rep T L V a = 1 := by
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      simpa [pow_two] using h.toHyp611.isElemAbelian.2 (a : G) haV)
    rw [this, map_one]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    rcases mem_zpowers_involution ha2 hx with rfl | rfl
    · simp
    · rcases hform v with h1 | h1
      · rw [h1, mul_inv_cancel]; exact Subgroup.one_mem _
      · rw [h1, mul_comm v, mul_inv_cancel_right]; exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    obtain ⟨v, hv⟩ : ∃ v, rep T L V a v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact ha1 (MulEquiv.ext hcon)
    have h1 : rep T L V a v = v * zt T L V z₀ hz₀ := (hform v).resolve_left hv
    exact Subgroup.subset_closure ⟨rep T L V a, Subgroup.mem_zpowers _, v, by
      rw [h1, mul_comm v, mul_inv_cancel_right]⟩

include h hZ hZS h6210 hz₀Z hw haV ha1 in

theorem normalizer_V_of_rep_comm_F4 (h629 : Stmt6_2_9_F4) (c : ↥(HH T))
    (hc : rep T L V c * rep T L V a = rep T L V a * rep T L V c) :
    (c : G) ∈ Subgroup.normalizer (V : Set G) := by
  have hform := rep_form_F4 h h6210 hZS z₀ hz₀ hw a haV
  have hw1 : zt T L V z₀ hz₀ ≠ 1 := fun h1 => hz₀Z ((tmk_eq_one_iff _).mp h1)
  obtain ⟨v, hv⟩ : ∃ v, rep T L V a v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact ha1 (MulEquiv.ext hcon)
  have h1 : rep T L V a v = v * zt T L V z₀ hz₀ := (hform v).resolve_left hv
  have hfix : rep T L V c (zt T L V z₀ hz₀) = zt T L V z₀ hz₀ := by
    have hzv : zt T L V z₀ hz₀ = rep T L V a v * v⁻¹ := by
      rw [h1, mul_comm v, mul_inv_cancel_right]
    have hc' : rep T L V c (rep T L V a v) = rep T L V a (rep T L V c v) := by
      have := congrArg (fun φ : MulAut (Ut T L V) => φ v) hc
      simpa using this
    have e1 : rep T L V c (zt T L V z₀ hz₀) =
        rep T L V a (rep T L V c v) * (rep T L V c v)⁻¹ := by
      conv_lhs => rw [hzv]
      rw [map_mul, map_inv, hc']
    rcases hform (rep T L V c v) with h2 | h2
    · exfalso
      rw [h2, mul_inv_cancel] at e1
      apply hw1
      have : rep T L V c (zt T L V z₀ hz₀) = rep T L V c 1 := by rw [e1, map_one]
      exact (rep T L V c).injective this
    · rw [e1, h2, mul_comm (rep T L V c v), mul_inv_cancel_right]
  have hN := mem_normalizer_ZS_of_fix h hZ z₀ hz₀ hw c hfix
  exact HH_inf_normalizer_ZS_le_F4 h h629 ⟨c.2, hN⟩

end Main

end CFSG.Quasithin.H13.GM22
