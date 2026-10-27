module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Perf
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL3U3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Gen

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2 SmallL3Ne3 SmallU3Ne3)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem socF4L3_holds (r : ℕ) : SocF4L3 r := by
  intro hr A _ _ T _ hT hab hC hE R S z hd hc hnO hed hL3
  haveI := hT
  have hL3' := hL3
  obtain ⟨p, f, hp, hp2, hf, hq3, hm⟩ := hL3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
    (Or.inl ⟨by decide, hm⟩ : CFSG.Blueprint.LieModel ↥T .PSL 3 p f)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card K := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    rw [hK]
    omega
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd
  have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ :=
    CFSG.ClassicalInvolution.Q3.TL4.MF163.center_eq_bot_of_equiv hab e
  obtain ⟨hzT, hzS⟩ := z_mem_of_comm2 hr hC (socleOutAbelian_l3 hL3').comm2 hd hc
  obtain ⟨F⟩ := L3.exists_l3Frame T hodd e hzT hd.order
  exact socF4_clause_of_parts hzS F.J_le F.comm_le (F.J_perfect h4) (F.J_centralizes hd hodd h4)
    (L3.two_elts_mem_J F hC hd hodd h4 h2 hp hp2 hf hK hZ hr hc) hodd h4 F.Φ
    (F.Φ_injective hC) F.Φ_range

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
