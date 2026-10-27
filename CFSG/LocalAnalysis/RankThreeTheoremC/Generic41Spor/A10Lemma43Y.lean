module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43YK
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43YPump
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43YFix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x t₁ t₂ : Y} {J₁ J₂ F : Subgroup Y}

theorem a10y_c_false (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hI : KFactI1434)
    (hU : KFactU44Data) {A₁ A₂ : Subgroup Y} (c : A10YCaseC Y P x t₁ t₂ J₁ J₂ F A₁ A₂) : False := by
  have hAeq : A₁ = A₂ := a10y_A_eq hInn c
  subst hAeq
  have h := c.data
  have hPA : P ≤ A₁ := a10y_P_le hInn c
  obtain ⟨-, hsimple, hnab, hcat⟩ := a10y_comp_simple h c.comp₁
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S, hS⟩ := h.sylow
  have hSA : (S : Subgroup Y) ≤ A₁ := hS ▸ hPA
  let Q : Sylow 5 ↥A₁ := S.subtype hSA
  have hQP : (Q : Subgroup ↥A₁).map A₁.subtype = P := by
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, hS]
    exact inf_eq_left.mpr hPA
  let x' : ↥A₁ := ⟨x, hPA h.x_mem⟩
  let t₁' : ↥A₁ := ⟨t₁, hPA h.t₁_mem.1⟩
  let t₂' : ↥A₁ := ⟨t₂, hPA h.t₂_mem.1⟩
  obtain ⟨hQr, hQc, hxQ, ht₁Q, ht₂Q, hx1, hx5, ht₁1, ht₂1, ht₁5, ht₂5⟩ :=
    a10y_sub_basic h Q hQP x' t₁' t₂' rfl rfl rfl
  obtain ⟨hc₁, hc₂, hne, hlay⟩ := a10y_comp_sub h c.comp₁ x' rfl c.le₁ c.le₂
  obtain ⟨hfus, hswap, hd₁, hd₂, hd₃⟩ :=
    a10y_fus_sub h (fun f hf => a10y_F_normalizes c hf) Q hQP x' t₁' t₂' rfl rfl rfl
  obtain ⟨hA₁, hA₂⟩ := a10y_A5_quot_sub h c.le₁ c.le₂
  exact a10_K_false hWC hI hU hsimple hnab hcat Q hQr hQc hxQ hx1 hx5 ht₁Q ht₂Q ht₁1 ht₂1
    ht₁5 ht₂5 hne hc₁ hc₂ hlay hA₁ hA₂ h.t₁_mem.2 h.t₂_mem.2 hd₁ hd₂ hd₃ hfus hswap

theorem a10y_components (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hI : KFactI1434) (hU : KFactU44Data)
    {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x t₁ t₂ : Y} {J₁ J₂ F : Subgroup Y}
    (h : A10YData Y P x t₁ t₂ J₁ J₂ F) : IsComponentOf J₁ ⊤ ∧ IsComponentOf J₂ ⊤ := by
  obtain ⟨f, -, hf12, -⟩ := h.F_swap
  have hswap : IsComponentOf J₁ ⊤ ↔ IsComponentOf J₂ ⊤ := by
    rw [← hf12]
    exact (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj f) J₁).symm
  obtain ⟨A₁, A₂, hA₁, hA₂, hJ₁, hJ₂⟩ := a10y_pumpup hSch h
  by_cases h₁ : IsComponentOf J₁ ⊤
  · exact ⟨h₁, hswap.mp h₁⟩
  · exact (a10y_c_false hInn hWC hI hU
      ⟨h, hA₁, hA₂, hJ₁, hJ₂, h₁, fun h₂ => h₁ (hswap.mpr h₂)⟩).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
