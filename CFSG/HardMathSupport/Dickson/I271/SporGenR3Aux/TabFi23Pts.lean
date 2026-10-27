module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Lift
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.Quasithin.H13.J4Order
public import CFSG.RankThree.Native.Fi22FiveCheckInputs
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Walter.JRFacts
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Certificate13622Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Orbit

theorem fix_iff_comm (x : CFSG.Sporadic.Fi23.J) (r : Fin 31671) :
    x • r = r ↔ conjPt r.val * x = x * conjPt r.val := by
  rw [smul_eq_iff]
  constructor
  · intro h
    calc conjPt r.val * x = (x * conjPt r.val * x⁻¹) * x := by rw [h]
      _ = x * conjPt r.val := by group
  · intro h
    rw [← h]
    group

theorem exists_cent_smul_of_noncomm {x : CFSG.Sporadic.Fi23.J} {a b : Fin 31671} (ha : x • a = a) (hb : x • b = b)
    (hab : conjPt a.val * conjPt b.val ≠ conjPt b.val * conjPt a.val) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J), g • a = b := by
  have ha' := (fix_iff_comm x a).1 ha
  have hb' := (fix_iff_comm x b).1 hb
  have hDa : conjPt a.val ∈ D23 := conjPt_mem_D23 a.2
  have hDb : conjPt b.val ∈ D23 := conjPt_mem_D23 b.2
  have hcube := D23_cube hDa hDb hab
  have hA := D23_mul_self hDa
  have hB := D23_mul_self hDb
  have hA' : (conjPt a.val)⁻¹ = conjPt a.val := inv_eq_of_mul_eq_one_right hA
  have hB' : (conjPt b.val)⁻¹ = conjPt b.val := inv_eq_of_mul_eq_one_right hB
  refine ⟨conjPt a.val * conjPt b.val, cen_iff' ?_, (smul_eq_iff _ a b).2 ?_⟩
  · calc conjPt a.val * conjPt b.val * x = conjPt a.val * (conjPt b.val * x) := by rw [mul_assoc]
      _ = conjPt a.val * (x * conjPt b.val) := by rw [hb']
      _ = (conjPt a.val * x) * conjPt b.val := by rw [mul_assoc]
      _ = (x * conjPt a.val) * conjPt b.val := by rw [ha']
      _ = x * (conjPt a.val * conjPt b.val) := by rw [mul_assoc]
  · rw [mul_inv_rev, hA', hB']
    have key : conjPt a.val * conjPt b.val * conjPt a.val * conjPt b.val * conjPt a.val *
        conjPt b.val = 1 := by
      rw [← hcube]
      group
    calc conjPt a.val * conjPt b.val * conjPt a.val * (conjPt b.val * conjPt a.val)
        = (conjPt a.val * conjPt b.val * conjPt a.val * conjPt b.val * conjPt a.val *
            conjPt b.val) * (conjPt b.val)⁻¹ := by group
      _ = conjPt b.val := by rw [key, one_mul, hB']

theorem card_cent_eq_mul_stab {x : CFSG.Sporadic.Fi23.J} {p : Fin 31671} (hp : x • p = p)
    (htr : ∀ r : Fin 31671, x • r = r → ∃ g ∈ Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J), g • p = r) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J)) =
      Nat.card {r : Fin 31671 // x • r = r} *
        Nat.card ↥(Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J) ⊓
          Subgroup.centralizer ({conjPt p.val} : Set CFSG.Sporadic.Fi23.J)) := by
  set C : Subgroup CFSG.Sporadic.Fi23.J := Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J) with hC
  have horb : MulAction.orbit ↥C p = {r : Fin 31671 | x • r = r} := by
    ext r
    constructor
    · rintro ⟨g, rfl⟩
      show x • ((g : CFSG.Sporadic.Fi23.J) • p) = (g : CFSG.Sporadic.Fi23.J) • p
      have hg : (g : CFSG.Sporadic.Fi23.J) * x = x * (g : CFSG.Sporadic.Fi23.J) := by
        have h := cen_iff g.2
        exact h
      rw [← mul_smul, ← hg, mul_smul, hp]
    · intro hr
      obtain ⟨g, hg, hgp⟩ := htr r hr
      exact ⟨⟨g, hg⟩, hgp⟩
  have hstab : Nat.card ↥(MulAction.stabilizer ↥C p) =
      Nat.card ↥(C ⊓ Subgroup.centralizer ({conjPt p.val} : Set CFSG.Sporadic.Fi23.J)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨(g : ↥C).1, (g : ↥C).2, ?_⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · have hg : (g : ↥C) • p = p := g.2
      have h2 := (smul_eq_iff ((g : ↥C).1) p p).1 hg
      refine cen_iff' ?_
      calc ((g : ↥C).1) * conjPt p.val = (((g : ↥C).1) * conjPt p.val * ((g : ↥C).1)⁻¹) *
            ((g : ↥C).1) := by group
        _ = conjPt p.val * ((g : ↥C).1) := by rw [h2]
    · have h2 := cen_iff g.2.2
      show (g.1 : CFSG.Sporadic.Fi23.J) • p = p
      refine (smul_eq_iff g.1 p p).2 ?_
      rw [h2]
      group
  have h1 := (MulAction.stabilizer ↥C p).card_mul_index
  rw [MulAction.index_stabilizer, horb] at h1
  have h2 : Set.ncard {r : Fin 31671 | x • r = r} = Nat.card {r : Fin 31671 // x • r = r} :=
    (Nat.card_coe_set_eq _).symm
  rw [h2, hstab] at h1
  rw [← h1, mul_comm]

end Orbit

section Check

theorem card_fin_subtype_eq_countP' (N : ℕ) (q : ℕ → Bool) :
    Nat.card {x : Fin N // q x = true} = (List.range N).countP q := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if q i = true then 1 else 0) N]
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.countP_append]
    simp [List.countP_cons]

theorem ap_eq_smul {x : CFSG.Sporadic.Fi23.J} {T : Table} (hT : Rep 31671 T x) (r : Fin 31671) :
    ap T r.val = (x • r).val := by
  rw [hT r.val r.2, idx_of_lt x r.2]

end Check

end CFSG.HardMathSupport.Dickson.I271.TabFi23
