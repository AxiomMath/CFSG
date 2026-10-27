module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.OrthChain

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

open Finset

theorem isQF_qm : IsQF qm := qm_add

theorem isQF_qp : IsQF qp := qp_add

set_option maxRecDepth 100000 in
theorem reach_qm : ∀ k : Fin 6, ∀ c ∈ Cset qm k, c ∈ reachSet qm k 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem reach_qp : ∀ k : Fin 6, ∀ c ∈ Cset qp k, c ∈ reachSet qp k 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem prod_Cset_qm : ∏ k : Fin 6, (Cset qm k).card = 51840 := by decide +kernel

set_option maxRecDepth 100000 in
theorem prod_Cset_qp : ∏ k : Fin 6, (Cset qp k).card = 40320 := by decide +kernel

theorem card_orthMinus : Nat.card OrthMinus = 51840 :=
  ((orthOf_chain isQF_qm reach_qm).1).trans prod_Cset_qm

theorem card_orthPlus : Nat.card OrthPlus = 40320 :=
  ((orthOf_chain isQF_qp reach_qp).1).trans prod_Cset_qp

theorem orthMinus_eq_TG : OrthMinus = TG qm := (orthOf_chain isQF_qm reach_qm).2

theorem orthPlus_eq_TG : OrthPlus = TG qp := (orthOf_chain isQF_qp reach_qp).2

private lemma exists_mem_orthOf_of_q_eq_one (q : V6 → ZMod 2) (hq : IsQF q)
    (hq0 : q (bs 0) = 1) (hreach : ∀ c ∈ Cset q 0, c ∈ reachSet q 0 2)
    (u v : V6) (hu : q u = 1) (hv : q v = 1) : ∃ g ∈ OrthOf q, g u = v := by
  have memCset : ∀ w : V6, q w = 1 → w ∈ Cset q 0 := by
    intro w hw
    rw [Cset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hw, hq0]
    · intro i hi
      exact absurd hi (by omega)
  obtain ⟨gu, hgu, hgu0⟩ :=
    exists_mem_stab_of_mem_reachSet hq 0 2 (hreach u (memCset u hu))
  obtain ⟨gv, hgv, hgv0⟩ :=
    exists_mem_stab_of_mem_reachSet hq 0 2 (hreach v (memCset v hv))
  have hguOrth : gu ∈ OrthOf q := (Subgroup.mem_inf.mp hgu).1.1
  have hgvOrth : gv ∈ OrthOf q := (Subgroup.mem_inf.mp hgv).1.1
  refine ⟨gv * gu⁻¹, mul_mem hgvOrth (inv_mem hguOrth), ?_⟩
  have hguinv : gu⁻¹ u = bs 0 := by
    rw [← hgu0]
    exact Equiv.symm_apply_apply gu (bs 0)
  rw [Equiv.Perm.mul_apply, hguinv, hgv0]

theorem orthMinus_transitive (u v : V6) (hu : qm u = 1) (hv : qm v = 1) :
    ∃ g ∈ OrthMinus, g u = v := by
  simpa only [OrthMinus] using
    exists_mem_orthOf_of_q_eq_one qm isQF_qm (by decide)
      (fun c hc => reach_qm 0 c hc) u v hu hv

theorem orthPlus_transitive (u v : V6) (hu : qp u = 1) (hv : qp v = 1) :
    ∃ g ∈ OrthPlus, g u = v := by
  simpa only [OrthPlus] using
    exists_mem_orthOf_of_q_eq_one qp isQF_qp (by decide)
      (fun c hc => reach_qp 0 c hc) u v hu hv

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
