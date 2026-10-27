module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem64
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Prop61

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem prop_6_1 (h14 : IVK_1_4a_quat) (h119 : IVK_1_19_lift) (htriv : IVK_triv_fAut)
    (hpow : IVK_f_pow) (hsqR : IVK_f_sq_R) (hII : II4_4_4_center)
    (h5r1 : Prop5_9_r1) (h10r1 : Lemma5_10_r1) (h5 : Prop5_9) (h10 : Lemma5_10)
    (h64 : Lemma6_4) (h65 : Lemma6_5) : Prop6_1 := by
  intro G _ _ z S h
  have he := h.elim61 h5r1 h10r1 h5 h10
  have hb := h.cond6b h14 h119 htriv hII he
  have ha := h.cond6a h14 h119 hpow hsqR he hb
  refine ⟨ha, hb, ?_, ?_⟩
  · intro K hK1
    have hK : IsRigidRankOneComp z K := by
      have : K ∈ {K' : Subgroup G | IsRigidRankOneComp z K'} := by rw [hK1]; exact Set.mem_singleton K
      exact this
    exact h64 G z S K ⟨h, hK1⟩ (ha K hK) (hb K hK)
  · intro K hK
    have hm : K ∈ {K' : Subgroup G | IsRigidRankOneComp z K'} := hK
    rcases h.cases with ⟨K₀, h1⟩ | ⟨K₁, K₂, h2⟩
    · rw [h1.comps] at hm
      have hK0 : K = K₀ := hm
      subst hK0
      exact not_2A7_of_G2Concl (h64 G z S K h1 (ha K hK) (hb K hK))
    · have hr1 : IsRigidRankOneComp z K₁ := h2.comp_rigid (Or.inl rfl)
      have hr2 : IsRigidRankOneComp z K₂ := h2.comp_rigid (Or.inr rfl)
      rw [h2.comps] at hm
      have h65' := h65 G z S K₁ K₂ h2 (ha K₁ hr1) (ha K₂ hr2)
      rcases (by simpa using hm : K = K₁ ∨ K = K₂) with rfl | rfl
      · exact h65'.1
      · exact h65'.2

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
