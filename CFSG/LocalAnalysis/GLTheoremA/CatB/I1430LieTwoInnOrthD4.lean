module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutD4
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnOrth
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutA6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType lieSOutTypeW_a6 typeLayer_adjointD4_outerW
  typeLayer_congr)

section D4


private theorem not_compOfType_isA6_d4_outer {S : Type} [Group S] [Finite S] {f : ℕ}
    (hG : StatedClassicalModel S .POmegaPlus 4 2 f) {α : MulAut S} (hin : α ∉ inner S)
    (hα3 : α ^ 3 = 1) : ¬ CompOfType S α isA6 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e₀⟩⟩ := hG
  obtain ⟨e₁⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  let E : S ≃* adjointGroup Tag.D4 K := e₀.trans e₁
  haveI : Finite (adjointGroup Tag.D4 K) := Finite.of_equiv S E.toEquiv
  have hE3 : MulAut.congr E α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hEout : MulAut.congr E α ∉ inner (adjointGroup Tag.D4 K) := fun h =>
    hin ((CFSG.Sporadic.FischerOddCore.congr_mem_inner_iff E α).1 h)
  have hT := typeLayer_congr E
    (typeLayer_adjointD4_outerW lieSOutTypeW_a6 hadm.2.1 K hK _ hE3 hEout)
  rintro ⟨J, hJ, hJT⟩
  exact hT J hJ hJT

theorem i1430InnNoD_proved : I1430InnNoD := by
  rintro S _ _ hs hnab ⟨d, hv⟩ ⟨n, q, rfl⟩ hc - ⟨e⟩ α hα hα3 -
  have hq2 : q.p = 2 := by simpa using hc
  obtain ⟨hadm, hG | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D n q hv e
  · rw [hq2] at hG
    have h4 : 4 ≤ n := hadm.2.2
    by_cases hin : α ∈ inner S
    · exact not_compOfType_isA6_inner_omega_two (Or.inl rfl) hs hnab hG hin hα3
    · rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
      · exact not_compOfType_isA6_d4_outer hG hin hα3
      · exact absurd (mem_inner_of_mem_innAutDerived_omegaPlus hG h5 Nat.prime_three
          (by norm_num) hα hα3) hin
  · have h4 : 4 ≤ n := hadm.2.2
    omega

end D4

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
