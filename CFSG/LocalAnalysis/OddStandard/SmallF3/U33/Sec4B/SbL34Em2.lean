module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Em1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem card_CW_eq (ha : Ctx4A t L S x₁ x₂ lam rho tau) {W : Subgroup G} {v : G}
    (hv : Ctx4V t x₁ x₂ lam tau W v) :
    Nat.card ↥(centralizer ({t * lam} : Set G) ⊓ W) = 2 ^ 7 := by
  have hc : Ctx4L t L S x₁ x₂ lam rho tau := ha.toCtx4L
  have hD2 : IsPGroup 2 ↥(centralizer ({t * lam} : Set G) ⊓ W) :=
    hv.sylow.2.1.to_le inf_le_right
  obtain ⟨g₀, hg₀⟩ := hc.inv_tl 1 (Subgroup.one_mem _)
    (by simpa using q_mul_self hc.toCtx4Q)
  have hg₀' : g₀ * t * g₀⁻¹ = t * lam := by simpa using hg₀
  have hle : Nat.card ↥(centralizer ({t * lam} : Set G) ⊓ W) ≤ 2 ^ 7 :=
    card_pgroup_le_of_conj hg₀' S hc.le_invCent hc.relIndex_odd
      (Ctx4.card_S_seven hc.toCtx4) hD2 inf_le_left
  have hSp : ctxSp t tau x₁ x₂ lam v ≤ centralizer ({t * lam} : Set G) ⊓ W := by
    refine le_inf (Sp_le_cent hc hv) ?_
    unfold ctxSp
    exact sup_le (inf_le_left.trans hv.U_le) (zpowers_le.mpr hv.v_mem)
  have hge : 2 ^ 7 ≤ Nat.card ↥(centralizer ({t * lam} : Set G) ⊓ W) :=
    (le_card_Sp hc hv).trans (Subgroup.card_le_of_le hSp)
  exact le_antisymm hle hge

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
