module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNRed

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10CNE

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

theorem cfTwoNilpSL2_conclusion_of_exc'
    (hGA : TBLit.GriessMultipliersAllModels) {M : Type} [Group M] [Finite M]
    (hq : IsQuasisimple M) (hO : pPrimeCore 2 M = ⊥) (hz : ∃ z ∈ center M, orderOf z = 2)
    (hexc : HarrisLit.L33.IsTwoNilpExc' (M ⧸ center M)) :
    (∃ (K' : Type) (_ : Field K') (_ : Finite K') (r m : ℕ), r.Prime ∧ r ≠ 2 ∧ 1 ≤ m ∧
        Nat.card K' = r ^ m ∧ 5 ≤ r ^ m ∧
        Nonempty (M ≃* Matrix.SpecialLinearGroup (Fin 2) K')) ∨
      GH74.GLS.IsDoubleCoverOfAlt M 7 ∨ LieModel (M ⧸ center M) .PSL 3 2 2 ∨
      ¬ 3 ∣ Nat.card M := by
  rcases hexc with h | ⟨f, hf, hm⟩
  · exact cfTwoNilpSL2_conclusion_of_exc hGA hq hO hz h
  · exfalso
    obtain ⟨z, hzZ, hz2⟩ := hz
    have hZ : IsPGroup 2 (center M) := TBLit.center_isPGroup_two_of_pPrimeCore_eq_bot hO
    obtain ⟨h1, h2, h3, h4⟩ := HarrisLit.L33.odd_orders_psp_two_two hf
    have hN := GH74.Generic.noTwoCover_of_griess hGA
      (GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm) h1 h2 h3 h4
    have hbot := hN M hq hZ ⟨MulEquiv.refl _⟩
    rw [hbot, mem_bot] at hzZ
    rw [hzZ, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)

end CFSG.ComponentClassification.CatLeafProof.X10CNE

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatLeafProof

theorem cfTwoNilpSL2_of_rows'
    (hGA : TBLit.GriessMultipliersAllModels)
    (hA : HarrisLit.L33.TwoNilpFor' fun Y _ =>
      ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))
    (hC : HarrisLit.L33.TwoNilpFor' fun Y _ => Milestones.ClassicalRep Y)
    (hE : HarrisLit.L33.TwoNilpFor' fun Y _ => Blueprint.ExceptionalRep Y)
    (hS : HarrisLit.L33.TwoNilpFor' fun Y _ => Blueprint.NativeSporadic.SporadicRep Y) :
    CFTwoNilpSL2 := by
  intro M _ _ hq hO hcat hz α hα hCα
  obtain ⟨z, hzZ, hz2⟩ := hz
  have : Group.IsPerfect M := hq.1
  have hZ := TBLit.center_isPGroup_two_of_pPrimeCore_eq_bot hO
  have hs : IsSimpleGroup (M ⧸ center M) := hq.2.1
  have hne := X10CN.barAut_ne_one hz2 hCα
  have hord : orderOf (X10CN.barAut α) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact X10CN.barAut_mul_self hα) hne
  have hP : IsPGroup 2 (↥(HarrisLit.fixedPoints (X10CN.barAut α)) ⧸
      pPrimeCore 2 ↥(HarrisLit.fixedPoints (X10CN.barAut α))) :=
    HarrisLit.L33.isPGroup_quotient_iff_hasNormalPComplement.mpr
      (X10CN.hasNormalPComplement_fixSub_barAut hZ hCα)
  exact X10CNE.cfTwoNilpSL2_conclusion_of_exc' hGA hq hO ⟨z, hzZ, hz2⟩
    (HarrisLit.L33.twoNilpExc'_of_rows hA hC hE hS (M ⧸ center M) hcat hs hq.2.2 _ hord hP)

end CFSG.ComponentClassification.GSThmB
