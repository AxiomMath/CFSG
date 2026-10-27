module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.Blueprint.Chevalley
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwoExceptional
import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


theorem exists_adjointGroup_of_catalogIs_isF4two {S : Type} [Group S]
    (h : catalogIs S isF4two) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (S ≃* ↥(adjointGroup Tag.F4 K)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isF4two, onLie] at hi
  | alternating n hn => simp [isF4two, onLie] at hi
  | sporadic s => simp [isF4two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | F4 q =>
      simp [isF4two, onLie] at hi
      have hq : q.p = 2 := by
        exact ((Nat.Prime.pow_eq_iff (p := 2) (a := q.p) (k := q.exponent)
          Nat.prime_two).1 hi).1
      have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq e
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ :=
        CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmodel
      refine ⟨K, inferInstance, inferInstance, ?_, ⟨φ⟩⟩
      rw [hK]
      exact hi
    | _ => simp [isF4two, onLie] at hi

theorem exists_eq_conj_of_pow_three_F4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {α : MulAut ↥(adjointGroup Tag.F4 K)} (hα : α ^ 3 = 1) :
    ∃ x : ↥(adjointGroup Tag.F4 K), α = MulAut.conj x := by
  have hmem := CFSG.LocalAnalysis.GLTheoremA.CatB.forall_cube_inner_of_card_outer
    (by rw [CFSG.SeitzReduction.SeitzQ2.card_outer_adjointGroup_F4_two hK]; norm_num) α hα
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner] at hmem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hmem
  exact ⟨x, hx.symm⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
