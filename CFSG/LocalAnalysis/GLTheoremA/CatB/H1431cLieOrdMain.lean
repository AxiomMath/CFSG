module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cAltCard
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOrdExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem lieSTypeChar_holds :
    LieSTypeChar := by
  intro X _ _ r hX hC
  obtain ⟨i, hi, ⟨φ⟩⟩ := hX
  have hN : Nat.card X ∈ lieSOrdN := lieSOrd_mem_of_eq (altS_card_of_isType1430 i φ hi)
  rcases hC with ⟨j, hj, ⟨ψ⟩⟩ | ⟨j, hj, ⟨ψ⟩⟩
  ·
    cases j with
    | lie j' =>
      obtain ⟨e, hv⟩ := j'
      have hcard : Nat.card X = lieOrderFormula e := lieOrderBridge_holds ⟨e, hv⟩ X ⟨ψ⟩
      have hchar : e.characteristic = r := hj
      rw [hcard] at hN
      rcases lieSOrd_cases hv hN with ⟨q, rfl, hq, -⟩ | ⟨q, rfl, hq, -⟩ | ⟨q, rfl, hq, -⟩
      · have hp : q.p = 2 := lieSOrd_p_eq Nat.prime_two (k := 1) (by rw [hq]; norm_num)
        exact Or.inl ⟨by simpa [hp] using hchar.symm, Or.inl ⟨.lie ⟨.B 3 q, hv⟩, hq, ⟨ψ⟩⟩⟩
      · have hp : q.p = 3 := lieSOrd_p_eq Nat.prime_three (k := 6) (by rw [hq]; norm_num)
        exact Or.inr ⟨by simpa [hp] using hchar.symm, ⟨.lie ⟨.A 1 q, hv⟩, hq, ⟨ψ⟩⟩⟩
      · have hp : q.p = 2 := lieSOrd_p_eq Nat.prime_two (k := 3) (by rw [hq]; norm_num)
        exact Or.inl ⟨by simpa [hp] using hchar.symm, Or.inr ⟨.lie ⟨.B 2 q, hv⟩, hq, ⟨ψ⟩⟩⟩
    | _ => exact hj.elim
  ·
    cases j with
    | alternating n hn =>
      exfalso
      rcases hj with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        exact lieSOrd_not_alt ψ.toEquiv hN (by omega)
    | lie j' =>
      exfalso
      obtain ⟨e, hv⟩ := j'
      have hcard : Nat.card X = lieOrderFormula e := lieOrderBridge_holds ⟨e, hv⟩ X ⟨ψ⟩
      rw [hcard] at hN
      rcases lieSOrd_cases hv hN with ⟨q, rfl, -, -⟩ | ⟨q, rfl, hq, -⟩ | ⟨q, rfl, -, -⟩
      · exact hj
      · rcases hj with ⟨h7, -⟩ | ⟨h8, -⟩ <;> omega
      · exact hj
    | _ => exact hj.elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
