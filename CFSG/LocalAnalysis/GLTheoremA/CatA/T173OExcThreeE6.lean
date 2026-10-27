module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeCoprime
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE6Orbit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE6Cent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE6Layer
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6TwoPilot
open CFSG.StandardType.E6ThreeEnd CFSG.StandardType.SmallExc
open scoped MatrixGroups


section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem stdVanishes_torusE6Two_e0 (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    (hd : IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd e0E6))) :
    StdVanishes (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd e0E6)) :=
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  stdVanishes_of_hyperplanes Nat.prime_three (by norm_num) (isElemAbelian_range_torusE6Two h2) hd
    (centralizer_range_torusE6Two_le h2 hK) (range_torusE6Two_le_sup_stdLayer_e0 h2 hK)
    (fun _ hD => exists_conj_mem_hyperplane_torusE6Two h2 (by decide) reachB_one hD)

private theorem stdVanishes_torusE6Two_d2 (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    (hd : IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd d2E6))) :
    StdVanishes (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd d2E6)) :=
  haveI : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  stdVanishes_of_hyperplanes Nat.prime_three (by norm_num) (isElemAbelian_range_torusE6Two h2) hd
    (centralizer_range_torusE6Two_le h2 hK) (range_torusE6Two_le_sup_stdLayer_d2 h2 hK)
    (fun _ hD => exists_conj_mem_hyperplane_torusE6Two h2 (by decide) reachB_two hD)

theorem stdVanishes_torusE6Two (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    {d : adjointGroup .E6 K} (hd : IsStdElt 3 (torusE6Two (K := K) h2).range d) :
    StdVanishes (torusE6Two (K := K) h2).range d := by
  obtain ⟨w, rfl⟩ := hd.1
  have hv0 : Multiplicative.toAdd w ≠ 0 := by
    intro h0
    have hw : w = 1 := by
      have h := congrArg Multiplicative.ofAdd h0
      simpa using h
    exact hd.2.1 (by rw [hw, map_one])
  have key : ∀ z : ZMod 3, normE6 (Multiplicative.toAdd w) = z →
      StdVanishes (torusE6Two (K := K) h2).range
        (torusE6Two h2 (.ofAdd (Multiplicative.toAdd w))) := by
    intro z hz
    fin_cases z
    · exact absurd hd (not_isStdElt_of_inOrbit h2
        (inOrbit_of_reachB h2 _ 4 _ (reachB_zero _ hz hv0)) (not_isStdElt_torusE6Two_d0 h2 hK))
    · exact stdVanishes_torusE6Two_of_inOrbit h2 (inOrbit_of_reachB h2 _ 4 _ (reachB_one _ hz))
        (stdVanishes_torusE6Two_e0 h2 hK) hd
    · exact stdVanishes_torusE6Two_of_inOrbit h2 (inOrbit_of_reachB h2 _ 5 _ (reachB_two _ hz))
        (stdVanishes_torusE6Two_d2 h2 hK) hd
  exact key _ rfl

end Main

variable {F : Type} [Field F] [Finite F]

theorem modelFactV_three_E6_two [Finite ↥(adjointGroup .E6 F)] (hF : Nat.card F = 2) :
    ModelFactV 3 ↥(adjointGroup .E6 F) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine modelFactV_of_frame (torusE6Two (K := F) h2).range (fun A hA => ?_)
    (fun d hd => stdVanishes_torusE6Two h2 hF hd)
  obtain ⟨hAel, hcard, -⟩ := hA
  refine exists_conj_eq_range_torusE6Two h2 hF hAel ?_
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) (four_le_glaTwoLocalRank_three_E6 (K := F))

theorem modelFactExcThree_E6 : ModelFactExcThree .E6 :=
  fun _ _ _ _ hF => (modelFactV_three_E6_two hF).modelFactO

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
