module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN1b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndCtx

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

section Rep

variable [Fact (IsElemAbelianMod (UU T L V) (quasithinOmegaOneCenter T))]

variable (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
  (h6210 : Stmt6_2_10_F4) (hZS : ch6ZS T L V = V ⊓ UU T L V)

variable (z₀ : G) (hz₀ : z₀ ∈ ch6ZS T L V)
  (hw : ∀ (z : G) (hz : z ∈ ch6ZS T L V), zt T L V z hz = 1 ∨ zt T L V z hz = zt T L V z₀ hz₀)

include h hZS h6210 hw in

theorem rep_form_F4 (a : ↥(HH T)) (haV : (a : G) ∈ V) (x : Ut T L V) :
    rep T L V a x = x ∨ rep T L V a x = x * zt T L V z₀ hz₀ := by
  induction x using QuotientGroup.induction_on with | H u => ?_
  have hc : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ ch6ZS T L V := by
    have h1 := commutator_V_UU_le_F4 h h6210 (Subgroup.commutator_mem_commutator haV u.2)
    rw [commutatorElement_def] at h1
    rwa [hZS]
  have hcU : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ UU T L V := le_conjClosure _ _ hc
  have e : conjU (UU T L V) a (HH_le_normalizer_UU T L V a.2) u =
      ⟨(a : G) * u * (a : G)⁻¹ * (u : G)⁻¹, hcU⟩ * u := by
    apply Subtype.ext
    rw [coe_conjU]
    simp
  change rep T L V a (tmk T L V u) = tmk T L V u ∨
    rep T L V a (tmk T L V u) = tmk T L V u * zt T L V z₀ hz₀
  rw [rep_mk, e, tmk_mul]
  rcases hw _ hc with h1 | h1
  · have h1' : tmk T L V ⟨_, hcU⟩ = 1 := h1
    left; rw [h1', one_mul]
  · have h1' : tmk T L V ⟨_, hcU⟩ = zt T L V z₀ hz₀ := h1
    right; rw [h1', mul_comm]

end Rep

end CFSG.Quasithin.H13.GM22
