module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

@[expose] def KFactM11ThreeIrr : Prop :=
  ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .M11).Group) →
      ∀ S : Sylow 3 L, ∀ Y : Subgroup L, Y ≤ S → Nat.card Y = 3 →
        ∃ t ∈ Subgroup.normalizer ((S : Subgroup L) : Set L),
          t ∉ Subgroup.normalizer (Y : Set L)

theorem automizerIrreducible_of_m11 (hKF : KFactM11Three) (hIrr : KFactM11ThreeIrr) {X : Type}
    [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group)) :
    AutomizerIrreducible 3 (R : Subgroup X) X₀ := by
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hX₀, -, -⟩ := h.eq_normalizer_of_card_outer_eq_one hKF e
  have hKtop := h.eq_top_of_card_outer_eq_one (hKF K ⟨e⟩).1
  have eX : X ≃* (TauCeti.CFSGIndex.sporadic .M11).Group :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hKtop.symm)).trans e
  intro Y hYR hY3
  obtain ⟨t, htN, htY⟩ := hIrr X ⟨eX⟩ R Y hYR hY3
  exact ⟨t, ⟨hX₀ ▸ htN, htN⟩, htY⟩

theorem d2AutomizerAt_m11 (hKF : KFactM11Three) (hIrr : KFactM11ThreeIrr) :
    D2AutomizerAt (.sporadic .M11) fun p => p = 3 := by
  intro X _ _ p hp3 R A X₀ K hK he
  subst hp3
  exact automizerIrreducible_of_m11 hKF hIrr hK he

theorem d2SylowNineAt_m11 (hKF : KFactM11Three) :
    D2SylowNineAt (.sporadic .M11) fun p => p = 3 := by
  intro X _ _ p hp3 R A X₀ K hK ⟨e⟩
  subst hp3
  exact (hK.eq_normalizer_of_card_outer_eq_one hKF e).2.2

end CFSG.LocalAnalysis.RankThreeTheoremC
