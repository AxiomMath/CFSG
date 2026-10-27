module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3



theorem lemma2_4_29_5 (h247 : Lemma2_4_27) (h246 : Lemma246Chi) : Lemma2_4_29_5 := by
  intro G _ _ T M H S L cfg hs3 hTC
  have cs := cfg.cs
  have hsingle : conjJoin S L = L := cfg.single
  have hQ : pCoreOf 2 H = blockU L := by
    obtain ⟨-, -, ⟨-, hQ, -, -⟩, -⟩ := h247 G T M H S L cs (Or.inl ⟨cfg.alt5, hsingle⟩)
    rw [hQ, hTC, bot_sup_eq, blockU0_eq_blockU hsingle]
  have hUQ : blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) :=
    cs.block.1.1.2.2.1.1
  have hUQ' : blockU L ≤ blockQ L := hUQ.trans inf_le_left
  have hQL : blockQ L ≤ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have hUL : blockU L ≤ L := hUQ'.trans hQL
  have hUabel : blockU L ≤ Subgroup.centralizer (blockU L : Set G) := fun x hx =>
    Subgroup.centralizer_le (s := (blockU L : Set G)) (t := (blockQ L : Set G)) hUQ' (hUQ hx).2
  obtain ⟨hcharN, hcoreN⟩ :=
    IsGamma0.charTwo_core_normalizer cs.setting cs.gamma0 cs.sylow_inf cs.charTwo
  rw [hQ] at hcharN hcoreN
  have hCU : Subgroup.centralizer (blockU L : Set G) = blockU L := by
    refine le_antisymm ?_ hUabel
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (blockU L : Set G) :=
      (Subgroup.centralizer_le_normalizer (blockU L : Set G)) hx
    have hmem : x ∈ Subgroup.normalizer (blockU L : Set G) ⊓
        Subgroup.centralizer
          (pCoreOf 2 (Subgroup.normalizer (blockU L : Set G)) : Set G) := by
      refine ⟨hxN, ?_⟩
      rw [hcoreN]
      exact hx
    have := hcharN hmem
    rwa [hcoreN] at this
  have hCL : Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxU : x ∈ blockU L := by
      rw [← hCU]
      exact Subgroup.centralizer_le (s := (blockU L : Set G)) (t := (L : Set G)) hUL hx
    have hxS : x ∈ S := by
      have : x ∈ pCoreOf 2 H := hQ ▸ hxU
      exact cs.sylow.pCoreOf_le this
    have hxT : x ∈ T ⊓ Subgroup.centralizer (conjJoin S L : Set G) := by
      rw [hsingle]
      exact ⟨cs.le_T hxS, hx⟩
    have : x ∈ blockTC T S L := hxT
    rwa [hTC] at this
  have hLn : Subgroup.normalizer (blockU L : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have := h246 G T M H S L cs hsingle (Or.inr cfg.alt5)
    rwa [hQ] at this
  exact { toA5Step3 := hs3, TC_one := hTC, Q_eq := hQ, CU_eq := hCU, CL_eq := hCL,
          L_normal := hLn }

end CFSG.QuasithinUnique.A5
