module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ParabolicBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem not_two_dvd_relIndex_inf_of_parabolic_of_sylow {B R L J N : Subgroup G}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo B R) (hJL : J ≤ L) (hNL : N ≤ L)
    (hN2 : IsPGroup 2 N) (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hJN : J ≤ Subgroup.normalizer (N : Set G))
    (hJ : ¬ 2 ∣ (J ⊓ R).relIndex J) (hodd : ¬ 2 ∣ (J ⊔ N).relIndex L) :
    ¬ 2 ∣ (L ⊓ R).relIndex L := by
  have hNR : N ≤ R := TwoRest3A6.le_of_isMaxInvariantTwo hR hN2 hRN hBN
  set J₁ := J ⊓ R
  have hJ₁J : J₁ ≤ J := inf_le_left
  have hU : N.relIndex (J ⊔ N) = N.relIndex J := relIndex_sup_of_le_normalizer hJN
  have hU₁ : N.relIndex (J₁ ⊔ N) = N.relIndex J₁ :=
    relIndex_sup_of_le_normalizer (hJ₁J.trans hJN)
  have hNJ : N ⊓ J₁ = N ⊓ J := by
    apply le_antisymm (inf_le_inf_left _ hJ₁J)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hNR))
  have hr : N.relIndex J₁ * J₁.relIndex J = N.relIndex J := by
    rw [← Subgroup.inf_relIndex_right N J₁, ← Subgroup.inf_relIndex_right N J, hNJ]
    exact Subgroup.relIndex_mul_relIndex _ _ _ (hNJ ▸ inf_le_right) hJ₁J
  have hm := Subgroup.relIndex_mul_relIndex N (J₁ ⊔ N) (J ⊔ N) le_sup_right
    (sup_le_sup_right hJ₁J N)
  rw [hU, hU₁, ← hr] at hm
  haveI : N.IsFiniteRelIndex J₁ := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hpos : 0 < N.relIndex J₁ := Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hx : (J₁ ⊔ N).relIndex (J ⊔ N) = J₁.relIndex J := Nat.eq_of_mul_eq_mul_left hpos hm
  have hUL : J ⊔ N ≤ L := sup_le hJL hNL
  have hle : J₁ ⊔ N ≤ L ⊓ R :=
    sup_le (le_inf (hJ₁J.trans hJL) inf_le_right) (le_inf hNL hNR)
  have hdvd := Subgroup.relIndex_dvd_of_le_left L hle
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_right hJ₁J N) hUL, hx] at hdvd
  intro h2
  rcases (Nat.prime_two.dvd_mul).mp (h2.trans hdvd) with h | h
  · exact hJ h
  · exact hodd h

theorem normalizer_le_of_cgs_le {R H : Subgroup G} (hCGS : CGS R ≤ H) :
    ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H := fun C hC hC1 hCc =>
  le_trans (by
    unfold CFSG.Quasithin.CGS
    exact le_iSup_of_le C <| le_iSup_of_le hC <| le_iSup_of_le hC1 <|
      le_iSup (fun _ : (C.subgroupOf R).Characteristic => Subgroup.normalizer (C : Set G)) hCc)
    hCGS

end CFSG.LocalAnalysis.RankThreeTheoremC
