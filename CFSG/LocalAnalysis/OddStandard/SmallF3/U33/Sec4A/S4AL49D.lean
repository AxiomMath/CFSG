module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49G

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem ctxS1_le_ctxM_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (h2 : 2 ∣ S.index) (hG2 : 2 ^ 11 ∣ Nat.card G) (𝒮 : Sylow 2 G)
    (h𝒮 : S < (𝒮 : Subgroup G)) {E : Subgroup G} (hE𝒮 : E ≤ (𝒮 : Subgroup G))
    (hEn : (E.subgroupOf (𝒮 : Subgroup G)).Normal) (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEc : Nat.card E = 8) : ctxS1 S (𝒮 : Subgroup G) ≤ ctxM t tau x₁ x₂ := by
  intro α hα
  obtain ⟨hC, hidx, -⟩ := sylow_facts_of_l42 h h2 𝒮 h𝒮
  rcases conj_ctxX_cases h h43 h44 hα.1 with hnorm | hswap
  · exact (Subgroup.mem_set_normalizer_iff).2 (fun x => hnorm x)
  · exfalso
    have htS : t ∈ S := by
      have := h.center_ge (Subgroup.subset_closure (by simp) : t ∈ closure {t, (x₁ * x₂) ^ 2})
      exact this.1
    have hbound : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer ({t} : Set G) →
        Nat.card Q ≤ 2 ^ 7 := by
      intro Q hQ hQc
      have := card_le_of_isPGroup_le_centralizer_conj (S := S) (t := t) h.toCtx0.le_invCent
        h.toCtx0.isPGroup h.toCtx0.relIndex_odd (card_S_of h h43) 1 hQ (by simpa using hQc)
      exact this
    have htE : t ∉ E := fun ht =>
      false_of_mem_normal_E8 hE𝒮 hEn hEc hG2 ht hbound
    have hCE := four_le_card_inf_centralizer hE𝒮 hEn hEe hEc (h𝒮.le htS) (t_mul_self h.hyp)
    by_cases hES : E ≤ S
    · exact false_of_E_le_S h h43 h44 h𝒮.le hE𝒮 hEn hEe hEc htE hES hidx hα hswap
    · exact false_of_not_E_le_S h h43 h44 h𝒮.le hC hidx hE𝒮 hEn hEe hEc hCE hES hα hswap

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
