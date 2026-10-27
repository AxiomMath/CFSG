module

public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional
public import CFSG.LieType.Multipliers.Sz8
public import CFSG.LieType.Steinberg.CentralExt.SuzukiMultiplier
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

variable {X : Type} [Group X]

theorem suzuki_eight_row
    {n : ℕ} (hmodel : CFSG.Models.LieModel X .twistedB2 n 2 3) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .twistedB2 n 2 3 × exceptional .twistedB2 n 2 3) := by
  have hn : n = 0 := by
    obtain ⟨-, hcl | ⟨hn, -⟩⟩ := hmodel
    · exact hcl.2.elim
    · exact hn
  subst hn
  obtain ⟨hX, ⟨e⟩⟩ := CFSG.LieType.Multipliers.Sz8.multiplier_Sz_eight_of_tauCeti X hmodel
  let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
  exact ⟨hX, ⟨e.trans (MulEquiv.uniqueProd.symm.trans
    (GriessClassical.toGenEx (t := .twistedB2) (n := 0) (p := 2) (f := 3) (a₁ := 1) (a₂ := 1)
      (b₁ := 2) (b₂ := 2) rfl (by decide)))⟩⟩

theorem twistedB2_row
    {n p f : ℕ} (hmodel : CFSG.Models.LieModel X .twistedB2 n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .twistedB2 n p f × exceptional .twistedB2 n p f) := by
  have hmodel' := hmodel
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | suzuki m =>
      obtain ⟨rfl, rfl⟩ := hd
      have hm1 : 1 ≤ m :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
      · exact suzuki_eight_row hmodel'
      · obtain ⟨h1, h2⟩ := SuzukiClosed.suzuki_hopfMultiplier hm2
        let eZ : CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m ⧸
            Subgroup.center (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ≃* X :=
          ((QuotientGroup.quotientMulEquivOfEq (SuzukiClosed.suzuki_center_eq_bot hm2)).trans
            QuotientGroup.quotientBot).trans
            (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).symm
        have : Group.IsPerfect (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m ⧸
            Subgroup.center (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := ⟨h1⟩
        have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := eZ.toMonoidHom) eZ.surjective
        refine row_of_subsingleton rfl ?_ ⟨Group.IsPerfect.commutator_eq_top,
          (griessHopfMultiplierCongr eZ.symm).toEquiv.subsingleton⟩
        unfold exceptionalOrders
        split <;> first | rfl | omega
    | _ => simp [CFSG.Models.NamesTag] at hd

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
