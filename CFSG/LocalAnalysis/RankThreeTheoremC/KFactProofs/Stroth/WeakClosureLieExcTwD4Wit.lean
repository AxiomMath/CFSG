module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwD4Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWitWords

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false


section Witness

variable {L : Type} [Field L] [IsAlgClosed L]

theorem d4One_witness (D : LangDatum TwistTag.D4.tag L) [Finite D.model] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd d4OneWord)) {ζ : Lˣ} (hζp : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) (hq3 : (3 : ℤ) ∣ (q : ℤ) - 1) :
    ∃ (Q : Subgroup (ModGL TwistTag.D4.tag L)) (x y : ModGL TwistTag.D4.tag L), IsPGroup 3 Q ∧
      x ∈ Q ∧ y ∈ Q ∧ x ∈ D.model ∧ y ∈ D.model ∧ x * y ≠ y * x :=
  tw_witness_of_sc_check D hq hFr hΦ hn (M := d4OneM) (tw_hv_of_hw d4One_hw) (N := 3)
    (by norm_num) d4One_pow (la := d4OneX) (lb := d4OneY) d4OneMl d4OneM_eq
    (by decide +kernel) (by decide +kernel) hζp hζo ![0, 0, 1, 0] hq3
    (by decide +kernel) 0 (by decide +kernel)

theorem d4Two_witness (D : LangDatum TwistTag.D4.tag L) [Finite D.model] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd d4TwoWord)) {ζ : Lˣ} (hζp : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) (hq3 : (3 : ℤ) ∣ (q : ℤ) - (-1)) :
    ∃ (Q : Subgroup (ModGL TwistTag.D4.tag L)) (x y : ModGL TwistTag.D4.tag L), IsPGroup 3 Q ∧
      x ∈ Q ∧ y ∈ Q ∧ x ∈ D.model ∧ y ∈ D.model ∧ x * y ≠ y * x :=
  tw_witness_of_sc_check D hq hFr hΦ hn (M := d4TwoM) (tw_hv_of_hw d4Two_hw) (N := 6)
    (by norm_num) d4Two_pow (la := d4TwoX) (lb := d4TwoY) d4TwoMl d4TwoM_eq
    (by decide +kernel) (by decide +kernel) hζp hζo ![1, 0, 1, 0] hq3
    (by decide +kernel) 1 (by decide +kernel)

end Witness

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
