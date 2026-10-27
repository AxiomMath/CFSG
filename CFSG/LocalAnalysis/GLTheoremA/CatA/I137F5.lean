module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1315
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2b
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem lieOrderFormula_le_of_k2Lie_five {d : LieTypeIndex} (h : k2Lie 5 d) :
    lieOrderFormula d ≤ CFSG.Open.ordTwistedF4 32 := by
  unfold k2Lie at h
  split at h
  all_goals first
    | exact h.elim
    | (exfalso; have h1 := h.1; omega)
    | (exfalso; rcases h with h | h <;> (have h1 := h.1; omega))
    | skip
  · norm_num [lieOrderFormula, CFSG.Open.orderTits, CFSG.Open.ordTwistedF4]
  · rename_i k
    obtain rfl : k = 2 := by
      rcases h with h | h
      · have h1 := h.1
        omega
      · exact h.2
    norm_num [lieOrderFormula, CFSG.Open.orderTwistedF4, CFSG.Open.ordTwistedF4]
  · rename_i k
    obtain rfl : k = 2 := h.2
    norm_num [lieOrderFormula, CFSG.Open.orderSuzuki, CFSG.Open.ordTwistedF4]

theorem i137Order5_holds :
    I137Order5 := by
  intro K _ _ hK hlev hch Q₀ _ hQ₀
  obtain ⟨j, hj, ⟨eQ⟩⟩ := hQ₀
  have hj' : S9.isReeF432 j := by
    rcases hj with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · norm_num at h
  have hQ : Nat.card Q₀ = CFSG.Open.ordTwistedF4 32 := by
    rcases j with _ | _ | ⟨d, hv⟩ | _
    · exact hj'.elim
    · exact hj'.elim
    · cases d with
      | reeF4 m =>
        obtain rfl : m = 2 := hj'
        rw [Nat.card_congr eQ.toEquiv,
          CFSG.AGLEmbedding.card_catGroup_reeF4 (d := ⟨.reeF4 2, hv⟩) (m := 2) rfl]
        norm_num
      | _ => exact hj'.elim
    · exact hj'.elim
  rw [hQ]
  have h12 : K1Cover 5 K ∨ K2Cover 5 K := by
    by_cases h1 : K1Cover 5 K
    · exact Or.inl h1
    · by_cases h2 : K2Cover 5 K
      · exact Or.inr h2
      · exfalso
        unfold fullCoverLevel at hlev
        rw [if_neg h1, if_neg h2] at hlev
        split_ifs at hlev <;> omega
  rcases h12 with ⟨-, h5⟩ | ⟨-, hc⟩
  ·
    rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1315.inputChevTwoOdd_holds
        (K ⧸ Subgroup.center K) 5 (by norm_num) (by norm_num) (by norm_num) h5 hch with
      ⟨⟨e⟩, -⟩ | ⟨-, h7⟩
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      norm_num [Nat.factorial, CFSG.Open.ordTwistedF4]
    · norm_num at h7
  ·
    rcases hc with ⟨hZ, i, hi, ⟨e⟩⟩ | ⟨-, i, hi, -⟩ | ⟨h3, -⟩ | ⟨i, hi, -⟩
    · have f : K ⧸ Subgroup.center K ≃* i.Group :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
      rcases i with _ | ⟨n, hn⟩ | d | s
      · exact hi.elim
      · exfalso
        rcases hi with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      · obtain ⟨d, hv⟩ := d
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ _ ⟨f⟩]
        exact lieOrderFormula_le_of_k2Lie_five hi
      · exact (CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds _ (.sporadic s)
          (Or.inl ⟨s, rfl, 5, hi⟩) ⟨f⟩ hch).elim
    · exfalso
      rcases i with _ | _ | ⟨d, hv⟩ | _
      · exact hi
      · exact hi
      · simp only [onLie] at hi
        split at hi <;> omega
      · exact hi
    · norm_num at h3
    · exfalso
      rcases i with _ | _ | _ | s
      · exact hi
      · exact hi
      · exact hi
      · exact absurd hi.1 (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
