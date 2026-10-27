module

public import CFSG.LocalAnalysis.OddStandard.ONanSylowFacts
public import Certificates.Data.ONanF2Quot

public section

namespace CFSG.OddStandard.ONanRec.Model

open Subgroup F2 F2.AlpE CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem f2Quot_parts (h : f2QuotCheck = true) : factP0 ∧ factT := by
  simp only [f2QuotCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem mem_subE_N_iff (h : f2QuotCheck = true) (a : AlpE) : a ∈ subE genNE ↔ a ∈ ballNE :=
  SubOK.mem_closure_iff (f2Quot_parts h).1.1 a

theorem mem_subE_P0_iff (h : f2QuotCheck = true) (a : AlpE) :
    a ∈ subE (genMaxE 1) ↔ a ∈ ballMaxL.getD 1 [] :=
  SubOK.mem_closure_iff (f2Quot_parts h).1.2.1 a

noncomputable def psi (h : f2QuotCheck = true) : ↥(subE (genMaxE 1)) →* TcM :=
  MonoidHom.mk' (fun a => fE a.1) (fun a b => by
    have hp := (f2Quot_parts h).1.2.2.2.1
    exact hp a.1 ((mem_subE_P0_iff h a.1).1 a.2) b.1 ((mem_subE_P0_iff h b.1).1 b.2))

theorem ker_psi (h : f2QuotCheck = true) :
    (psi h).ker = (subE genNE).subgroupOf (subE (genMaxE 1)) := by
  have hk := (f2Quot_parts h).1.2.2.2.2.1
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_subE_N_iff h]
  exact hk a.1 ((mem_subE_P0_iff h a.1).1 a.2)

theorem psi_surjective (h : f2QuotCheck = true) : Function.Surjective (psi h) := by
  intro y
  obtain ⟨a, ha, hy⟩ := (f2Quot_parts h).1.2.2.2.2.2.1 y
  exact ⟨⟨a, (mem_subE_P0_iff h a).2 ha⟩, hy⟩

end CFSG.OddStandard.ONanRec.Model
