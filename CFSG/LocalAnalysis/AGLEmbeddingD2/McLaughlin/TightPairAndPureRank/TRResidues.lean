module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.IrrQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem three_dvd_card_barM {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hL : IsWeakSBlock M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (h3 : BlockHasThree M S L) : 3 ∣ Nat.card (barM M L) := by
  obtain ⟨y, hyP, hy3, hyC⟩ := CFSG.AGLEmbeddingD2.exists_order_three_noncentral hL.le h3 hZ
  have hyL : y ∈ barM M L := barM_mono inf_le_right hyP
  have hy1 : y ≠ 1 := fun h => hyC (h ▸ Subgroup.one_mem _)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard (barM M L) hyL

end CFSG.AGLEmbeddingD2.McLaughlin
