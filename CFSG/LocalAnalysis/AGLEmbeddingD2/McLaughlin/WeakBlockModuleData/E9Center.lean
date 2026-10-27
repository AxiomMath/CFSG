module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreNineLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.AlternatingNineFree
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.PerfectCover CFSG.Assembly.LowTwoRank

theorem not_nine_dvd_card_griess_of_census
    (hG : GriessAllModelsStatement) {X : Type} [Group X]
    (h : (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2IndexTwo d.1 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ¬ 9 ∣ Nat.card (griessHopfMultiplier X) := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact not_nine_dvd_multiplier_of_classicalIndexTwo hG d hd e
  · have h5 : 5 ≤ m := by rcases hm with rfl | rfl | rfl <;> norm_num
    exact AGLEmbeddingD2.McLaughlin.OrdinaryProofs.not_nine_dvd_card_griessHopfMultiplier_of_mulEquiv_alternating
      h5 e
  · rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
      have hc := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at hc
      rw [Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv,
        card_hopfMultiplier_of_statedClassicalModel hG hc]
      decide
    · obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
      have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at hc
      rw [Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv,
        card_hopfMultiplier_of_statedClassicalModel hG hc]
      decide

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
