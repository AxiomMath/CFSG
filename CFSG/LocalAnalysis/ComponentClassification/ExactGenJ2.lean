module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenLift
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenAut
public import Certificates.Certificate34001

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2
  CFSG.ComponentClassification.OuterAutomorphisms


theorem exactCore_J2 (S : Type) [Group S] [Finite S]
    (h : Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .J2)) : ExactCore S := by
  obtain ⟨e⟩ := h
  have hc : ExactFin.j2FCCheck () = true := Certificates.certificate34001
  simp only [ExactFin.j2FCCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hok, hk⟩, h0⟩, h1⟩, hordP⟩, hordN⟩ := hc
  have hsub : (ExactFin.j2FC ()).ctx.chP.sub 315 = j2P := by
    unfold ExactFin.ChainData.sub j2P
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hk] at hi
      interval_cases i
      · left
        simp [j2Gen, j2StrongPerm, h0]
      · right
        simp [j2Gen, j2StrongPerm, h1]
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, by simp [j2Gen, j2StrongPerm, h0]⟩
      · exact ⟨1, by omega, by simp [j2Gen, j2StrongPerm, h1]⟩
  have e' : S ≃* (ExactFin.j2FC ()).ctx.chP.sub 315 :=
    (e.trans j2PermEquiv).trans (MulEquiv.subgroupCongr hsub.symm)
  haveI hJ : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI : IsSimpleGroup S := e.isSimpleGroup
  have hcard : Nat.card S = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  have hnp : ¬ (Nat.card S).Prime := by
    rw [hcard]
    norm_num
  have hout : Nat.card (Outer S) ≤ 2 :=
    outer_card_le_of_equiv AT_J2_Schreier.1 e
  haveI : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => (f : S → S))
    (fun f g h => MulEquiv.ext (congrFun h))
  have hout2 : (Nat.card (Outer S)).factorization 2 ≤ 1 :=
    ExactFin.factorization_two_le_one Nat.card_pos hout
  have hk : 1 + ((ExactFin.j2FC ()).ctx.chP.order 315).factorization 2 ≤
      ((ExactFin.j2FC ()).ctx.chN.order 315).factorization 2 := by
    rw [hordP, hordN, Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  exact ExactFin.coreStmt_of_model 315 (ExactFin.j2FC ()) hok e'
    (ExactFin.commutator_eq_top_of_simple_card hnp) hout2 hk

end CFSG.ComponentClassification.SolMax.SwapP2
