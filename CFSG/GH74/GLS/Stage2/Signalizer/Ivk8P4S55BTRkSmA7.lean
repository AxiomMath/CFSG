module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkSmK
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace RkSm

theorem admRank3_of_order_four {k : Kind} {Y B : Type} [Group Y] [Finite Y] [Group B]
    (e : Y ≃* B) (hc : center Y = ⊥) (h32 : ¬ 32 ∣ Nat.card (MulAut Y)) (b : B)
    (hb4 : b ^ 4 = 1) (hb2 : b ^ 2 ≠ 1) : AdmRank3 k Y := by
  have := finite_mulAut (Y := Y)
  refine admRank3_of_sq fun E hE =>
    card_le_eight_of_order_four h32 (x := MulAut.conj (e.symm b)) ?_ ?_ E hE
  · rw [← map_pow, ← map_pow, hb4, map_one, map_one]
  · intro h
    refine hb2 (e.symm.injective (conj_injective hc ?_))
    rw [map_pow, map_pow, h, map_one, map_one]

end RkSm

theorem rankCellK_a7 :
    RankCellK Kind.psp4 (fun Y _ => Nonempty (Y ≃* alternatingGroup (Fin 7))) := by
  intro Y _ _ _ ⟨e⟩
  have hY : Nat.card Y = 2520 := by rw [Nat.card_congr e.toEquiv, RkSm.card_alt7]
  have hc : center Y = ⊥ := RkSm.center_eq_bot (by rw [hY]; norm_num)
  refine ⟨RkSm.not_isL2_of_card hY (a := 17) (by norm_num) (by norm_num), ?_⟩
  have hA : Nat.card (MulAut Y) = 5040 := by
    rw [RkSm.card_mulAut hc, hY, Nat.card_congr (equivalence e).toEquiv,
      ProperTwoGeneratedCore.BenderFacts.card_outer_alternatingGroup (by norm_num) (by norm_num)]
  let σ : alternatingGroup (Fin 7) := ⟨List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩
  exact RkSm.admRank3_of_order_four e hc (by rw [hA]; norm_num) σ (Subtype.ext (by decide))
    (fun h => absurd (congrArg Subtype.val h) (by decide))

theorem rankCell_m11j1 : RankCell (fun Y _ =>
    NativeSporadic.IsSporadic Y .M11 ∨ NativeSporadic.IsSporadic Y .J1) := by
  intro k hk Y _ _ _ hY
  rcases hY with h | h
  · have h' : Nonempty (Y ≃* NativeSporadic.M11) := h
    obtain ⟨e⟩ := h'
    have hY : Nat.card Y = 7920 := by rw [Nat.card_congr e.toEquiv, Sporadic.Schreier.m11_card]
    have hc : center Y = ⊥ := RkSm.center_eq_bot (by rw [hY]; norm_num)
    refine ⟨RkSm.not_kindFactorAll hk hY (a := 25) (by norm_num) (by norm_num)
      (RkSm.not_isSection_of_not_dvd hY (by norm_num)), ?_⟩
    have := RkSm.finite_mulAut (Y := Y)
    have hA : Nat.card (MulAut Y) = 7920 := by
      have h1 := RkSm.card_mulAut hc
      have h2 : Nat.card (MulAut Y) ≤ 7920 := by
        rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Sporadic.Schreier.m11_card]
        exact Sporadic.Schreier.m11_mulAut_card
      have h3 : 0 < Nat.card (Outer Y) := Nat.card_pos
      rw [hY] at h1
      omega
    let b : NativeSporadic.M11 := ⟨List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8],
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
    exact RkSm.admRank3_of_order_four e hc (by rw [hA]; norm_num) b (Subtype.ext (by decide))
      (fun h => absurd (congrArg Subtype.val h) (by decide))
  · have h' : Nonempty (Y ≃* NativeSporadic.J1) := h
    obtain ⟨e⟩ := h'
    have hY : Nat.card Y = 175560 := by rw [Nat.card_congr e.toEquiv, Sporadic.J1.card_J1]
    have hc : center Y = ⊥ := RkSm.center_eq_bot (by rw [hY]; norm_num)
    refine ⟨RkSm.not_kindFactorAll hk hY (a := 70) (by norm_num) (by norm_num)
      (RkSm.not_isSection_of_not_dvd hY (by norm_num)), ?_⟩
    have := RkSm.finite_mulAut (Y := Y)
    refine RkSm.admRank3_of_sq fun E hE => RkSm.card_le_eight_of_not_dvd ?_ E hE
    rw [RkSm.card_mulAut hc, hY, Nat.card_congr (equivalence e).toEquiv,
      Sporadic.Schreier.at_j1_schreier.1]
    norm_num

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
