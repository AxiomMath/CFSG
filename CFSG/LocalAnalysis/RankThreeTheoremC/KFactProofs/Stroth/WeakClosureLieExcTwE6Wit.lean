module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwE6Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWitWords

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false


section Witness

variable {L : Type} [Field L] [IsAlgClosed L]

@[expose] def e6OneThreeA : List (Fin TwistTag.E6.tag.rank) := [1]
@[expose] def e6OneThreeB : List (Fin TwistTag.E6.tag.rank) := [3]
@[expose] def e6OneThreeS : List (Fin TwistTag.E6.tag.rank) := [1]
theorem e6OneThree_witness (D : LangDatum TwistTag.E6.tag L) [Finite D.model] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord)) {ζ : Lˣ} (hζp : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) (hqp : (3 : ℤ) ∣ (q : ℤ) - (1)) [Fact (Nat.Prime 3)] :
    ∃ (Q : Subgroup (ModGL TwistTag.E6.tag L)) (x y : ModGL TwistTag.E6.tag L), IsPGroup 3 Q ∧
      x ∈ Q ∧ y ∈ Q ∧ x ∈ D.Γ ∧ y ∈ D.Γ ∧ x * y ≠ y * x :=
  tw_witness_Γ_of_check D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6OneMat) (tw_E6_hv e6One_hv)
    (N := 2) (by norm_num) twE6One_pow (la := e6OneThreeA) (lb := e6OneThreeB)
    (ls := e6OneThreeS) twE6OneMat rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hζp hζo ![0, 1, 0, 0, 2, 2] (e' := 1) hqp
    (by decide +kernel) 2 (by decide +kernel)

@[expose] def e6TwoThreeA : List (Fin TwistTag.E6.tag.rank) := [0]
@[expose] def e6TwoThreeB : List (Fin TwistTag.E6.tag.rank) := [2]
@[expose] def e6TwoThreeS : List (Fin TwistTag.E6.tag.rank) := [0]
theorem e6TwoThree_witness (D : LangDatum TwistTag.E6.tag L) [Finite D.model] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord)) {ζ : Lˣ} (hζp : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) (hqp : (3 : ℤ) ∣ (q : ℤ) - (-1)) [Fact (Nat.Prime 3)] :
    ∃ (Q : Subgroup (ModGL TwistTag.E6.tag L)) (x y : ModGL TwistTag.E6.tag L), IsPGroup 3 Q ∧
      x ∈ Q ∧ y ∈ Q ∧ x ∈ D.Γ ∧ y ∈ D.Γ ∧ x * y ≠ y * x :=
  tw_witness_Γ_of_check D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6TwoMat) (tw_E6_hv e6Two_hv)
    (N := 2) (by norm_num) twE6Two_pow (la := e6TwoThreeA) (lb := e6TwoThreeB)
    (ls := e6TwoThreeS) twE6TwoMat rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hζp hζo ![1, 0, 0, 0, 0, 0] (e' := -1) hqp
    (by decide +kernel) 3 (by decide +kernel)

@[expose] def e6TwoFiveA : List (Fin TwistTag.E6.tag.rank) := [0, 3]
@[expose] def e6TwoFiveB : List (Fin TwistTag.E6.tag.rank) := [2, 4]
@[expose] def e6TwoFiveS : List (Fin TwistTag.E6.tag.rank) := [0]
theorem e6TwoFive_witness (D : LangDatum TwistTag.E6.tag L) [Finite D.model] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord)) {ζ : Lˣ} (hζp : ζ ^ 5 = 1)
    (hζo : orderOf ζ = 5) (hqp : (5 : ℤ) ∣ (q : ℤ) - (-1)) [Fact (Nat.Prime 5)] :
    ∃ (Q : Subgroup (ModGL TwistTag.E6.tag L)) (x y : ModGL TwistTag.E6.tag L), IsPGroup 5 Q ∧
      x ∈ Q ∧ y ∈ Q ∧ x ∈ D.Γ ∧ y ∈ D.Γ ∧ x * y ≠ y * x :=
  tw_witness_Γ_of_check D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6TwoMat) (tw_E6_hv e6Two_hv)
    (N := 2) (by norm_num) twE6Two_pow (la := e6TwoFiveA) (lb := e6TwoFiveB)
    (ls := e6TwoFiveS) twE6TwoMat rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hζp hζo ![1, 0, 0, 0, 0, 0] (e' := -1) hqp
    (by decide +kernel) 0 (by decide +kernel)

end Witness

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
