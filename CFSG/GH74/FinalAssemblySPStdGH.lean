module

public import CFSG.GH74.FinalAssemblyDeep6
public import CFSG.GH74.Generic.GKFFinal
public import CFSG.GH74.Generic.S45.PumpC2
public import CFSG.GH74.Generic.S45.KFactsProof
public import CFSG.GH74.M12.AscFinal
public import Mathlib
public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.GH74.GLS.Stage4.Q3n.Setting
public import CFSG.GH74.GLS.Stage4.Q3n.Leaves
public import CFSG.GH74.GLS.Stage4.Q3n.Derived
public import CFSG.GH74.GLS.Stage4.Q3n.Omega
public import CFSG.GH74.GLS.Stage4.Q3n.Glue
public import CFSG.GH74.GLS.Stage4.Q3n.Final
public import CFSG.GH74.GLS.Stage4.Q3n.LGBridge
public import CFSG.GH74.GLS.Stage4.HexCAssembly
public import CFSG.GH74.GLS.C3.Layer1.Back114Main
public import CFSG.GH74.GLS.C3.Layer1.Split
public import CFSG.GH74.GLS.C3.Layer1.Thm1Leaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1End
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GH74.GLS.C3.Layer1.Thm1Fine
public import CFSG.GH74.GLS.C3.Layer1.Thm1Fusion
public import CFSG.GH74.GLS.C3.Layer1.Thm1FmemberF
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.GH74.GLS.C3.Layer1.Thm1Normal
public import CFSG.GH74.GLS.C3.Layer1.P34RealTop
public import CFSG.GH74.GLS.C3.Layer1.P34RealL2D
public import CFSG.GH74.GLS.C3.Layer1.P34RealDone
public import CFSG.GH74.GLS.C3.Layer1.EvenMax
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
public import CFSG.GH74.GLS.Stage4.Q9.Final
public import CFSG.GH74.GLS.Stage4.Q3n.MainSplit
public import CFSG.GH74.GLS.Stage4.HexCAssembly2
public import CFSG.GH74.Generic.S1.RQ3Good
public import CFSG.GH74.GLS.C3.Layer1.BkGen4L34
public import CFSG.GH74.GLS.C3.Layer1.BkIv81
public import CFSG.GH74.Generic.S45.LJ2
public import CFSG.GH74.Generic.S45.LOut
public import CFSG.GH74.Generic.S45.LTransfer
public import CFSG.GH74.GLS.LU.Local.FiveBundles
public import CFSG.GH74.GLS.LU.Local.FiveSetup
public import CFSG.GH74.GLS.LU.Local.Torus8
public import CFSG.GH74.GLS.LU.Local.L3InvAll
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44a
public import CFSG.GH74.GLS.LU.Local.Assembly
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.SP.Local.SPLPumpXRed
public import CFSG.GH74.GLS.LU.Local.FiveAssemblyGH
public import CFSG.CharacterTheory.BrauerSplittingField
public import CFSG.CharacterTheory.BrauerThirdMainTheorem
public import CFSG.CharacterTheory.Wreathed.FullDefectCanonicalStructure

public section

namespace CFSG.GH74

open GLS Subgroup Blueprint Assembly.LowTwoRank

theorem GLS.LU.nonempty_mulEquiv_of_local'_gh (hT0 : LU.Local.LUSetupLeaf')
    (hT1 : LU.Local.LULocalLeaf'_gh) {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    (hKGH : KGH G)
    {Gs : Type} [Group Gs] (hcompat : LU.IsTwoCentralClassicalTypeCompat G Gs) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hmodel : (p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f))
    (h6A : Stage12.Max6A G p f) : Nonempty (G ≃* Gs) := by
  have hN := LU.Local.luNeighborhood_at'_gh hT0 hT1 hG hKGH hcompat hp hp2 hq fun _ z hz => h6A z hz
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hq
      omega
    · exact h0
  have : Fact p.Prime := ⟨hp⟩
  rcases hmodel with ⟨h8, hL⟩ | ⟨h8, hU⟩
  · obtain ⟨K, _, _, z, u, Y, hK, hz, hA, hCN⟩ := hN.1 ⟨h8, hL⟩
    have hG' := hA.lieModel hG.1 p f hp hp2 hK hq hCN (h6A z hz)
    exact LU.nonempty_mulEquiv_of_lieModel_psl hp hf hG' hL
  · obtain ⟨K, _, _, _, F, _, _, z, u, Y, hK, hF, hz, hA, hCN⟩ := hN.2 ⟨h8, hU⟩
    have hG' := hA.lieModel hG.1 hK hF hp2 hq hCN (h6A z hz)
    exact LU.nonempty_mulEquiv_of_lieModel_psu hG' hU

theorem GLS.Stage12.S_C2starFour_Std_of_stage5_localStdGH' (h2 : Stage12.S_stage2Four_Std)
    (hSP : SP.Local.S_stage5_SP_compat_Std) (hT0 : LU.Local.LUSetupLeaf')
    (hT1 : LU.Local.LULocalLeaf'_gh)
    (hMcL : Stage12.S_McL_leaf) (hLy : Stage12.S_Ly_leaf) : Stage12.S_C2starFour_Std := by
  intro G _ _ hStd h4 hT
  rcases h2 G hStd h4 hT with h | ⟨Gs, _, hcl, hc⟩
  · rcases h with h | h
    · exact GLS.C2StarList.of_McL (hMcL G hStd.kps.1 hStd.kps.2.1 h)
    · exact GLS.C2StarList.of_Ly (hLy G hStd.kps.1 hStd.kps.2.1 h)
  · rcases hcl with ⟨p, f, hp, hp2, h3, hL⟩ | ⟨p, f, hp, hp2, h5, hL, h6⟩
    · obtain ⟨e⟩ := hSP G hStd Gs ⟨p, f, hp, hp2, h3, hL⟩ hc
      exact GLS.C2StarList.of_psp4 hp hp2 h3 (lieModel_of_mulEquiv e.symm hL)
    · obtain ⟨e⟩ := GLS.LU.nonempty_mulEquiv_of_local'_gh hT0 hT1 hStd.kps hStd.kgh hc hp hp2 h5 hL h6
      rcases hL with ⟨h8, hL⟩ | ⟨h8, hL⟩
      · exact GLS.C2StarList.of_psl4 hp hp2 (by omega) h8 (lieModel_of_mulEquiv e.symm hL)
      · exact GLS.C2StarList.of_psu4 hp hp2 (by omega) h8 (lieModel_of_mulEquiv e.symm hL)

end CFSG.GH74
