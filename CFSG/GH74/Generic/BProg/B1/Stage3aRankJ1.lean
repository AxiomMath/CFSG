module

public import CFSG.GH74.Generic.BProg.B1.Stage3aRank
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankCerts
public import CFSG.Walter.J1Props.Facts

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Walter
  CFSG.Walter.J1Props Subgroup

theorem rankCertified_walterJ1_two : RankCertified walterJ1 2 := by
  obtain ⟨hxx, hx'x', -, hxx', -⟩ := rels_F
  obtain ⟨hx1, hx'1, hxx'ne, -, -, ht1⟩ := ne_one_F
  obtain ⟨hxt, hx't, -⟩ := commute_tJ
  obtain ⟨hxF, hx'F, -⟩ := mem_F
  refine rankCertified_two_of_three_involutions (a := tJ) (b := xJ) (c := x'J) tJ_mul_self hxx hx'x'
    hxt.symm hx't.symm hxx' ht1 hx1 hx'1 ?_ ?_ hxx'ne ?_
  · intro h
    exact tJ_not_mem_F (by rw [h]; exact hxF)
  · intro h
    exact tJ_not_mem_F (by rw [h]; exact hx'F)
  · intro h
    refine tJ_not_mem_F ?_
    have h1 : tJ = x'J * xJ⁻¹ := eq_mul_inv_of_mul_eq h
    rw [h1]
    exact FJ.mul_mem hx'F (FJ.inv_mem hxF)

theorem noJPrimeFor_shape5 : NoJPrimeFor QShape5 := by
  refine noJPrimeFor_of_bar (fun e h => ?_) ?_
  · obtain ⟨e'⟩ := h
    exact ⟨e.symm.trans e'⟩
  · intro G _ _ hgen x K hx hKpc hG2 hr h5
    obtain ⟨e0⟩ := h5
    let e : ↥(imgBar x K) ≃* walterJ1 := e0.trans walterJ1EquivNative.symm
    have hJ : IsSimpleGroup walterJ1 := J1_simple
    have hsimple : IsSimpleGroup ↥(imgBar x K) := e.isSimpleGroup
    have hbot : Subgroup.center ↥(imgBar x K) = ⊥ :=
      center_eq_bot_of_simple_of_quasisimple hsimple hG2.1.1
    exact false_of_J2_pair_rank_of_center_bot hgen hx hKpc hr hbot
      (rankCertified_walterJ1_two.of_mulEquiv e.symm)

end CFSG.GH74.Generic.BProg.B1
