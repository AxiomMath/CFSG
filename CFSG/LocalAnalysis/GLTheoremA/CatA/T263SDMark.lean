module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] noncomputable def sdPSimpleEquiv {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) : ↥S ⧸ Subgroup.center ↥S ≃* PSimple p S :=
  let e1 : ↥S ≃* PQuot p S :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hSp.symm)
  QuotientGroup.congr (Subgroup.center ↥S) (Subgroup.center (PQuot p S)) e1
    (Subgroup.map_center_eq e1)

theorem sdPSimpleEquiv_mk {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (s : ↥S) :
    sdPSimpleEquiv hSp (QuotientGroup.mk s : ↥S ⧸ Subgroup.center ↥S) =
      (QuotientGroup.mk (QuotientGroup.mk s : PQuot p S) : PSimple p S) := rfl

theorem sd_marking_on_S {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B₀ : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hInn : InnDiagOn p B₀ S) :
    ∃ lab : GLALabel, LargeEvenInLambda2 lab ∧
      LargeEvenRawDatum lab fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥S ⧸ Subgroup.center ↥S ≃* R, ∀ b ∈ B₀, ∃ φ ∈ I,
          LargeEvenInduces θ (fun s s' : ↥S => (s' : Ω) = b * s * b⁻¹) φ := by
  obtain ⟨-, -, lab, hΛ, hraw⟩ := hInn
  refine ⟨lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R' _ I' F' ⟨hs, hna, θ, hind⟩
  refine ⟨hs, hna, (sdPSimpleEquiv hSp).trans θ, fun b hb => ?_⟩
  obtain ⟨φ, hφI, hφ⟩ := hind b⁻¹ (B₀.inv_mem hb)
  refine ⟨φ, hφI, fun s s' hss' => ?_⟩
  have h1 := hφ (QuotientGroup.mk s) (QuotientGroup.mk s') ⟨s, s', rfl, rfl, by rw [hss']; simp⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, sdPSimpleEquiv_mk, sdPSimpleEquiv_mk]
  exact h1

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
