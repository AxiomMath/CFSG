module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dCoreSL
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dCoreTrans

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
open KFactsSmall

namespace K1525dCoreProof

theorem core_of_equiv {L : Type} [Group L] [Finite L] {m : ℕ} (hm : 3 ≤ m) (e₀ : L ≃* SLF2 m)
    (S₀ A₁ A₂ : Subgroup L) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S₀ ⊤)
    (hcov : ∀ P : Subgroup L, IsMinOverBorel ⊤ S₀ P →
      pElementSubgroup 2 P ≤ A₁ ∨ pElementSubgroup 2 P ≤ A₂)
    (h1 : CFSG.Open.pRank 3 A₁ ≤ 1) (h2 : CFSG.Open.pRank 3 A₂ ≤ 1) :
    IsL3TwoModO2 A₁ ∨ IsL3TwoModO2 A₂ := by
  obtain ⟨g, -, hg⟩ := (sylowTwo_map e₀ hS).exists_conj (isSylowTwoOf_bor m)
  let e : L ≃* SLF2 m := e₀.trans (MulAut.conj g)
  have hS0 : S₀.map e.toMonoidHom = bor m := by
    rw [hg, Subgroup.map_map]
    rfl
  have hcov' := cover_map e hcov
  rw [hS0] at hcov'
  have h1' : CFSG.Open.pRank 3 (A₁.map e.toMonoidHom) ≤ 1 := by
    rw [pRank_map_equiv]
    exact h1
  have h2' : CFSG.Open.pRank 3 (A₂.map e.toMonoidHom) ≤ 1 := by
    rw [pRank_map_equiv]
    exact h2
  rcases core_sl m hm (A₁.map e.toMonoidHom) (A₂.map e.toMonoidHom)
      (fun i => hcov' (minPar m i) (isMinOverBorel_minPar m i)) h1' h2' with h | h
  · exact Or.inl (isL3TwoModO2_of_map e h)
  · exact Or.inr (isL3TwoModO2_of_map e h)

theorem K1525dCore_holds : K1525dCore := by
  intro L _ _ hL S₀ A₁ A₂ hS hcov h1 h2
  rcases hL with ⟨⟨e⟩⟩ | h5
  · exact core_of_equiv (m := 3) (by norm_num)
      (e.trans (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
        (K421HoldsProof.slEquivGL2 4).symm)) S₀ A₁ A₂ hS hcov h1 h2
  · obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.McLaughlin.nonempty_equiv_G52_of_isL5Two h5
    exact core_of_equiv (m := 4) (by norm_num) (e.trans (K421HoldsProof.slEquivGL2 5).symm)
      S₀ A₁ A₂ hS hcov h1 h2

end K1525dCoreProof

end CFSG.LocalAnalysis.RankThreeUC.S15
