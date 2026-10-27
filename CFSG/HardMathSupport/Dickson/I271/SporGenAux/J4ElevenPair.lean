module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.J4Eleven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.Solomon78 CFSG.RankThree.PartTwo.Sec4
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem j4_allInner
    (hOut : SporadicOuterLeTwo) (e : ↥J ≃* Spor .J4) :
    ∀ α : MulAut ↥J, ∃ g : ↥J, α = MulAut.conj g := by
  have hsimple : IsSimpleGroup ↥J := isSimpleGroup_J j4Facts
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [card_J_eq]; norm_num)
  have hnab : ∃ a b : ↥J, a * b ≠ b * a := by
    refine ⟨qx, qy, fun h => qz_ne_one ?_⟩
    rw [qz, commutatorElement_def, h]
    group
  have hle : Nat.card (Outer ↥J) ≤ 2 := hOut ↥J hsimple hnab .J4 ⟨e⟩
  have hodd := CTU_J4_outer_automorphism_group_odd_order
  have h1 : Nat.card (Outer ↥J) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have := Nat.card_pos (α := Outer ↥J)
    omega
  intro α
  haveI : Subsingleton (Outer ↥J) := (Nat.card_eq_one_iff_unique.1 h1).1
  have hα : (QuotientGroup.mk α : Outer ↥J) = 1 := Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).1 hα
  exact ⟨g, hg.symm⟩

theorem sporPlaneKill_J4_eleven
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .J4 11 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have bJ : ↥J ≃* Spor .J4 := (seedEquiv j4Facts.mat).symm.trans b₀
  have hAut := j4_allInner hOut bJ
  have bX : ↥J4T ≃* Spor .J4 := eJ4T.symm.trans bJ
  refine @sporPlaneKill_of_noSig_model hOut .J4 11 (by norm_num) (by norm_num) (by decide) ↥J4T
    (Subgroup.toGroup J4T) bX ?_ (NativeSporadic.Carrier .J4) _ b₀ offPair_J4
  intro R Y hR hR9 hY3 hRY
  exact j4Eleven_noSig hAut R hR hR9 Y ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY3) hRY

theorem sporPair_J4_eleven
    (hOut : SporadicOuterLeTwo) : SporPair .J4 11 :=
  sporPair_of_planeKill (sporPlaneKill_J4_eleven hOut)

end CFSG.HardMathSupport.Dickson.I271
