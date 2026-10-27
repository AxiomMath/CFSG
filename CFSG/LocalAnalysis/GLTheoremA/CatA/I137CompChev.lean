module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompList
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.LocalAnalysis.GLTheoremA.S8.Prop81

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

private theorem eq_two_or_three_or_five_of_ambiguousChev {q : ℕ} {i : TauCeti.CFSGIndex}
    (h : ambiguousChev q i) : q = 2 ∨ q = 3 ∨ q = 5 := by
  rcases i with _ | _ | ⟨d, _⟩ | _
  · simp [ambiguousChev] at h
  · simp [ambiguousChev] at h
    omega
  · cases d with
    | A n qq =>
        cases n with
        | zero => simp [ambiguousChev] at h
        | succ n =>
            cases n with
            | zero =>
                simp only [ambiguousChev] at h
                omega
            | succ n => simp [ambiguousChev] at h
    | twistedA n qq =>
        cases n with
        | zero => simp [ambiguousChev] at h
        | succ n =>
            cases n with
            | zero => simp [ambiguousChev] at h
            | succ n =>
                cases n with
                | zero =>
                    simp only [ambiguousChev] at h
                    omega
                | succ n =>
                    cases n with
                    | zero =>
                        simp only [ambiguousChev] at h
                        omega
                    | succ n => simp [ambiguousChev] at h
    | _ => simp [ambiguousChev] at h
  · simp [ambiguousChev] at h

section Certificates


theorem isChevSimple_two_of_chev_comp (hb : LieOrderBridge) (hA : Chev2OddAmb) {p q : ℕ}
    (hD : KDChevDownQ p q) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hq : IsChevSimple q S) (α : MulAut S) (hα : α ^ p = 1)
    (I : Subgroup S)
    (hI : GLAPComponent p (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I)
    (hcat : catalogIs (PSimple p I) (S9.isList93 p)) : IsChevSimple 2 S := by
  by_cases hq2 : q = 2
  · simpa [hq2] using hq
  · have hqprime : q.Prime := by
      rcases hq with ⟨i, hi, _⟩ | ⟨i, hi, _⟩
      · rcases i with _ | _ | ⟨d, _⟩ | _
        · simp [onLie] at hi
        · simp [onLie] at hi
        · rw [← hi]
          exact S8.lie_characteristic_prime d
        · simp [onLie] at hi
      · rcases eq_two_or_three_or_five_of_ambiguousChev hi with rfl | rfl | rfl
        · exact absurd rfl hq2
        · exact Nat.prime_three
        · exact Nat.prime_five
    exact absurd (hD S hS hnab hq α hα I hI)
      (not_isChevSimple_of_isList93 hb hA hqprime hq2 hcat)


end Certificates

end CFSG.LocalAnalysis.GLTheoremA
