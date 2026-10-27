module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeASix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem altSix_sFour_odd {A : Type} [Group A] [Finite A] {Y P : Subgroup A} (hPY : P ≤ Y)
    (eY : ↥Y ≃* alternatingGroup (Fin 6)) (eP : ↥P ≃* Equiv.Perm (Fin 4)) :
    ¬ 2 ∣ P.relIndex Y ∧ ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index := by
  refine ⟨?_, ?_⟩
  · have hA : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have hY : Nat.card Y = 360 := by rw [Nat.card_congr eY.toEquiv]; omega
    have hP : Nat.card P = 24 := by
      rw [Nat.card_congr eP.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have h := card_mul_index (P.subgroupOf Y)
    rw [Nat.card_congr (subgroupOfEquivOfLe hPY).toEquiv, hP, hY] at h
    have : (P.subgroupOf Y).index = 15 := by omega
    rw [relIndex, this]
    decide
  · obtain ⟨e⟩ := nonempty_quotient_pCore_mulEquiv eP
    have e3 := e.trans s4QuotientEquiv
    have htop : (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) ≤ wSup _ :=
      le_wSup_of_normal_symThree inferInstance (Subgroup.topEquiv.trans e3)
    rw [eq_top_iff.mpr htop, index_top]
    decide

variable (G : Type) [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
