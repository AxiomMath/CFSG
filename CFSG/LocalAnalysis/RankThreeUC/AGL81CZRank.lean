module

public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

theorem inf_centralizer_inf_centralizer_ne_bot {K : Type*} [Group K] [Finite K] {d : ℕ}
    (hd : d.Prime) {W L₁ L₂ : Subgroup K} (h₁ : W ≤ normalizer (L₁ : Set K))
    (h₂ : W ≤ normalizer (L₂ : Set K)) (hr₁ : pRank d (⊤ : Subgroup (MulAut L₁)) ≤ 1)
    (hr₂ : pRank d (⊤ : Subgroup (MulAut L₂)) ≤ 1) (hW : 3 ≤ pRank d W) :
    W ⊓ centralizer (L₁ : Set K) ⊓ centralizer (L₂ : Set K) ≠ ⊥ := by
  let f₁ : ↥W →* MulAut ↥L₁ := (normalizerMonoidHom L₁).comp (Subgroup.inclusion h₁)
  let f₂ : ↥W →* MulAut ↥L₂ := (normalizerMonoidHom L₂).comp (Subgroup.inclusion h₂)
  have hW' : 3 ≤ pRank d (⊤ : Subgroup ↥W) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hW
  have e1 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hd f₁ ⊤
  have e2 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hd f₂ f₁.ker
  have m1 : pRank d ((⊤ : Subgroup ↥W).map f₁) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hd.one_lt le_top).trans hr₁
  have m2 : pRank d (f₁.ker.map f₂) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hd.one_lt le_top).trans hr₂
  rw [top_inf_eq] at e1
  have hpos : 1 ≤ pRank d (f₁.ker ⊓ f₂.ker) := by omega
  intro hbot
  have hker : f₁.ker ⊓ f₂.ker = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    have hmem : (w : K) ∈ W ⊓ centralizer (L₁ : Set K) ⊓ centralizer (L₂ : Set K) := by
      refine ⟨⟨w.2, ?_⟩, ?_⟩
      · have h1 : f₁ w = 1 := MonoidHom.mem_ker.mp hw.1
        have h' : (⟨(w : K), h₁ w.2⟩ : normalizer (L₁ : Set K)) ∈
            (normalizerMonoidHom L₁).ker := h1
        rw [normalizerMonoidHom_ker] at h'
        exact h'
      · have h2 : f₂ w = 1 := MonoidHom.mem_ker.mp hw.2
        have h' : (⟨(w : K), h₂ w.2⟩ : normalizer (L₂ : Set K)) ∈
            (normalizerMonoidHom L₂).ker := h2
        rw [normalizerMonoidHom_ker] at h'
        exact h'
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 (Subtype.ext hmem)
  rw [hker] at hpos
  have h0 : pRank d (⊥ : Subgroup ↥W) = 0 := by
    obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hd.one_lt (⊥ : Subgroup ↥W)
    rw [le_bot_iff] at hE
    rw [hE, Subgroup.card_bot] at hEcard
    exact (Nat.pow_eq_one.mp hEcard.symm).resolve_left hd.one_lt.ne'
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
