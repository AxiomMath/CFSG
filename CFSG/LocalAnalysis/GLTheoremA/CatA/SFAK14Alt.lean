module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


private theorem sfaK14_card_u52 {S : Type} [Group S] [Finite S] (hcat : catalogIs S S9.isU5two) :
    Nat.card S = 13685760 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | twistedA n q =>
      rcases n with _ | _ | _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 2 := hi
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ S ⟨f⟩]
        show orderTwistedA 4 q.card = 13685760
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

private theorem sfaK14_card_sp6two {S : Type} [Group S] [Finite S] (hcat : catalogIs S S9.isSp6two) :
    Nat.card S = 1451520 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B n q =>
      rcases n with _ | _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 2 := hi
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ S ⟨f⟩]
        show orderBC 3 q.card = 1451520
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem K14NotAlt_holds : K14NotAlt := by
  intro S _ m hm hcat ⟨e⟩
  haveI : Finite S := Finite.of_equiv (alternatingGroup (Fin m)) e.toEquiv.symm
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card S = Nat.factorial m / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  have hS : Nat.card S = 13685760 ∨ Nat.card S = 1451520 := by
    rcases hcat with h | h
    · exact Or.inl (sfaK14_card_u52 h)
    · exact Or.inr (sfaK14_card_sp6two h)
  rcases Nat.lt_or_ge m 12 with h12 | h12
  · interval_cases m <;> norm_num [Nat.factorial] at hc <;> omega
  · have h12' : Nat.factorial 12 ≤ Nat.factorial m := Nat.factorial_le h12
    norm_num [Nat.factorial] at h12'
    omega

end CFSG.LocalAnalysis.GLTheoremA

end
