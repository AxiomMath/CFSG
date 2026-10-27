module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeGen3
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43OutIndex

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Multipliers.U43
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem nonempty_equiv_X₀_of_isU4of_three {T : Type} [Group T] (h : catalogIs T (S8.isU4of 3)) :
    Nonempty (T ≃* X₀) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA n q =>
      by_cases hn : n = 3
      · subst hn
        have hq : q.card = 3 := hi
        obtain ⟨b⟩ := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.u43_group_equiv hv hq
        exact ⟨e.trans b⟩
      · exfalso
        revert hi
        rcases n with _ | _ | _ | _ | n <;> simp_all [S8.isU4of, onLie]
    | _ => exact False.elim hi

theorem card_eq_of_isU4of_three {T : Type} [Group T] (h : catalogIs T (S8.isU4of 3)) :
    Nat.card T = 3265920 := by
  obtain ⟨e⟩ := nonempty_equiv_X₀_of_isU4of_three h
  rw [Nat.card_congr e.toEquiv, card_X₀]

theorem typeHyp3_u43 : BMType.TypeHyp3 (S8.isU4of 3) 3265920 where
  card T _ _ h := card_eq_of_isU4of_three h
  aut T _ _ h := by
    obtain ⟨e⟩ := nonempty_equiv_X₀_of_isU4of_three h
    haveI : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
    haveI : Finite (MulAut T) :=
      Finite.of_injective (fun f : MulAut T => (f : T → T)) (fun f g h => DFunLike.coe_injective h)
    haveI : Finite (Outer T) := Finite.of_surjective _ QuotientGroup.mk_surjective
    have hle : Nat.card (Outer T) ≤ 8 := by
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.u43_inn_index_le
    have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
    generalize Nat.card (Outer T) = k at hle hpos
    interval_cases k <;> norm_num
  big := by norm_num
  nine := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
