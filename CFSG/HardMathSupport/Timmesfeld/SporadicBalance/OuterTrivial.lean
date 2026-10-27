module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance

theorem noOuterFixesCentralizer_of_inner_eq_top {K : Type*} [Group K] (p : ℕ)
    (h : innerAut K = ⊤) : NoOuterFixesCentralizer p K :=
  fun σ _ hσ _ _ => absurd (h ▸ Subgroup.mem_top σ) hσ

theorem innerAut_eq_top_of_forall {K : Type*} [Group K]
    (h : ∀ α : MulAut K, ∃ g : K, α = MulAut.conj g) : innerAut K = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  obtain ⟨g, hg⟩ := h σ
  exact ⟨g, hg.symm⟩

theorem sporadicOuterHolds_of_inner (name : TauCeti.SporadicName) (p : ℕ)
    (h : innerAut (NativeSporadic.Carrier name) = ⊤) : SporadicOuterHolds name p :=
  fun _ _ _ _ ⟨e⟩ =>
    NoOuterFixesCentralizer.of_mulEquiv e (noOuterFixesCentralizer_of_inner_eq_top p h)

theorem sporadicOuterHolds_Fi23
    (p : ℕ) :
    SporadicOuterHolds .Fi23 p :=
  sporadicOuterHolds_of_inner .Fi23 p CFSG.Sporadic.FischerOddCore.inner_fi23_eq_top

theorem sporadicOuterHolds_Co3
    (p : ℕ) : SporadicOuterHolds .Co3 p :=
  sporadicOuterHolds_of_inner .Co3 p
    CFSG.Sporadic.SmallOddCore.ctuc_co3_all_automorphisms_inner.{0}.2.1.2

theorem sporadicOuterHolds_Co2
    (p : ℕ) : SporadicOuterHolds .Co2 p :=
  sporadicOuterHolds_of_inner .Co2 p (innerAut_eq_top_of_forall
    (CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model
      (NativeSporadic.Carrier .Co2) (MulEquiv.refl _)))

theorem sporadicOuterHolds_Co1
    (p : ℕ) : SporadicOuterHolds .Co1 p :=
  sporadicOuterHolds_of_inner .Co1 p (innerAut_eq_top_of_forall
    (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
        Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner))

theorem sporadicOuterHolds_Th
    (p : ℕ) : SporadicOuterHolds .Th p :=
  sporadicOuterHolds_of_inner .Th p CFSG.Sporadic.ThSchreier.inner_Th

theorem sporadicOuterHolds_Ly
    (p : ℕ) : SporadicOuterHolds .Ly p :=
  sporadicOuterHolds_of_inner .Ly p
    CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput

theorem sporadicOuterHolds_B
    (p : ℕ) : SporadicOuterHolds .B p :=
  sporadicOuterHolds_of_inner .B p
    (innerAut_eq_top_of_forall CFSG.RankThree.PartOne.SPOR.allInner_B)

theorem sporadicOuterHolds_M
    (p : ℕ) : SporadicOuterHolds .M p :=
  fun _ _ _ _ ⟨e⟩ => noOuterFixesCentralizer_of_inner_eq_top p
    (Subgroup.index_eq_one.mp (CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
