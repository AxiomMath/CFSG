module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def cover107 (lab : GLALabel) : Prop :=
  lab = ⟨.F4, 0, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩

@[expose] def I67Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (X L : Subgroup G) (lab : GLALabel), p.Prime → p ≠ 2 →
    CFSG.Open.IsKGroup ↥X → GLAPComponent p X L → Rk2IsLabel (PSimple p L) lab →
    GLAInLambda2 lab → 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) →
    Even (Nat.card ↥(Subgroup.center (LTilde p L))) → exempt107 lab ∨ cover107 lab

@[expose] def I1066CoverAt (lab : GLALabel) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    GLARawDatum lab (fun R _ _ _ => Nonempty (K ⧸ Subgroup.center K ≃* R)) →
    twoRankLow107 lab + CFSG.Open.pRank 2 (Subgroup.center K) ≤ CFSG.Open.pRank 2 (⊤ : Subgroup K)

@[expose] def I1066Cover : Prop :=
  I1066CoverAt ⟨.F4, 0, 1⟩ ∧ I1066CoverAt ⟨.twA, 5, 1⟩ ∧ I1066CoverAt ⟨.twE6, 0, 1⟩

theorem coverEvenAt_of_split (h67 : I67Cover) (h1066 : I1066Cover) : CoverEvenAt := by
  intro G _ _ p X L lab hp hp2 hX hL hrk hlab hex hm hEven
  rcases h67 G p X L lab hp hp2 hX hL hrk hlab hm hEven with h | h
  · exact absurd h hex
  have hperf := ltilde_perfect hL
  obtain ⟨e⟩ := ltilde_centre_equiv hL
  haveI hsimple : IsSimpleGroup (PSimple p L) := (isQuasisimple_pQuot_of_glaPComponent hp hL).2
  have hraw : GLARawDatum lab
      (fun R _ _ _ => Nonempty (LTilde p L ⧸ Subgroup.center (LTilde p L) ≃* R)) := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono (fun R _ I F hQ => ?_)
      (rk2IsLabel_rawDatum hrk)
    obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
    have hZ : Subgroup.center (PSimple p L) = ⊥ := center_eq_bot_of_quotient_nonab θ hna
    let e₀ : PSimple p L ⧸ Subgroup.center (PSimple p L) ≃* PSimple p L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact ⟨e.trans (e₀.symm.trans θ)⟩
  rcases h with rfl | rfl | rfl
  · exact h1066.1 _ hperf hraw
  · exact h1066.2.1 _ hperf hraw
  · exact h1066.2.2 _ hperf hraw

end CFSG.LocalAnalysis.GLTheoremA
