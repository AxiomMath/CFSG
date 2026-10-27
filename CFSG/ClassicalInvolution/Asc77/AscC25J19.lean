module

public import CFSG.ClassicalInvolution.Asc77.AscC25X11
public import CFSG.ClassicalInvolution.Asc77.AscC25X8
public import CFSG.ClassicalInvolution.Asc77.AscR10E23
public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutOdd
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinus
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
open CFSG.ClassicalInvolution.Asc77.C25X
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three neZero_of_pow_eq_three)
open CFSG.ClassicalInvolution.ModelFacts (odd_natCard_galoisField_of_pow_eq_three)
open scoped MatrixGroups

local notation "FSC" => CFSG.ClassicalInvolution.ModelFacts.FundamentalSingleClass

section Rows

variable {p : ℕ} [Fact p.Prime]


theorem fundCorr_odd3 {f : ℕ} (h3 : p ^ f = 3) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) :
    (∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)),
        R.map (spinAction (quadOdd n (GaloisField p f))) ∈
          fundSet (quadOdd n (GaloisField p f))) ∧
      ∀ L ∈ fundSet (quadOdd n (GaloisField p f)),
        ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)),
          R.map (spinAction (quadOdd n (GaloisField p f))) = L := by
  have hm3 : 3 ≤ n := hadm.2.2.1
  have hsc : FSC .POmegaOdd (oddDatum n (GaloisField p f)) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd n p f Fact.out trivial
      hadm (by decide) (by decide)
  exact ⟨fun R hR => CFSG.ClassicalInvolution.RouteD.Gaps.map_mem_fundSet_odd hm3 hsc hR,
    fun L hL => CFSG.ClassicalInvolution.RouteD.Gaps.exists_map_eq_odd hm3
      (odd_natCard_galoisField_of_pow_eq_three h3) hL⟩

theorem fundCorr_plus3 {f : ℕ} (h3 : p ^ f = 3) {n : ℕ} (hn : 4 ≤ n) :
    (∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) (by omega)),
        R.map (spinAction (quadPlus n (GaloisField p f))) ∈
          fundSet (quadPlus n (GaloisField p f))) ∧
      ∀ L ∈ fundSet (quadPlus n (GaloisField p f)),
        ∃ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) (by omega)),
          R.map (spinAction (quadPlus n (GaloisField p f))) = L := by
  have hm3 : 3 ≤ n := by omega
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.2 (neZero_of_pow_eq_three h3).ne
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨Fact.out, hf1, hn⟩
  have eq' := CFSG.ClassicalInvolution.RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) hm3
  have hsc : FSC .POmegaPlus
      (Generic.modelUniv .POmegaPlus n p f Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus n p f Fact.out trivial
      hadm (by decide) (by decide)
  have hsc' : FSC .POmegaPlus (plusDatum n (GaloisField p f) hm3) := by
    revert hsc
    rw [eq']
    exact id
  exact ⟨fun R hR => CFSG.ClassicalInvolution.RouteD.Gaps.map_mem_fundSet hm3 hsc' hR,
    fun L hL => CFSG.ClassicalInvolution.RouteD.Gaps.exists_map_eq hm3
      (odd_natCard_galoisField_of_pow_eq_three h3) hL⟩

end Rows

end CFSG.ClassicalInvolution.Asc77.C25J
