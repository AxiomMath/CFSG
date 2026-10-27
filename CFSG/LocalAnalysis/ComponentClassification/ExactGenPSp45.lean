module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenLift
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenAut
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45Equiv
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45Out
public import Certificates.Certificate34003

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Monster.B.Co2


theorem exactCore_PSp45 (S : Type) [Group S] [Finite S] (h : Blueprint.LieModel S .PSp 2 5 1) :
    ExactCore S := by
  have hc : ExactFin.psp45FCCheck () = true := Certificates.certificate34003
  simp only [ExactFin.psp45FCCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hok, hk2⟩, h0⟩, h1⟩, hordP⟩, hordN⟩ := hc
  obtain ⟨hP, hN, -, -, -, hcP, -⟩ :=
    ExactFin.Ctx.sound 156 _ ((ExactFin.psp45FC ()).ctx_ok 156 hok)
  have hsub : (ExactFin.psp45FC ()).ctx.chP.sub 156 = ExactPSp45.pspP := by
    unfold ExactFin.ChainData.sub ExactPSp45.pspP
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hk2] at hi
      interval_cases i
      · left
        rw [h0]
      · right
        rw [h1]
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, by rw [h0]⟩
      · exact ⟨1, by omega, by rw [h1]⟩
  have hcardP : Nat.card ExactPSp45.pspP = 4680000 := by
    rw [← hsub, hcP, hordP]
  obtain ⟨e⟩ := ExactPSp45.psp45_equiv hcardP S h
  have e' : S ≃* (ExactFin.psp45FC ()).ctx.chP.sub 156 := e.trans (MulEquiv.subgroupCongr hsub.symm)
  have hB : StatedClassicalModel S .PSp 2 5 1 :=
    Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  haveI : IsSimpleGroup S :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp S 2 5 1 hB
  have hcard : Nat.card S = 4680000 := by
    rw [Nat.card_congr e'.toEquiv, hcP, hordP]
  have hnp : ¬ (Nat.card S).Prime := by
    rw [hcard]
    norm_num
  haveI : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => (f : S → S))
    (fun f g h => MulEquiv.ext (congrFun h))
  have hout : (Nat.card (Outer S)).factorization 2 ≤ 1 :=
    ExactFin.factorization_two_le_one Nat.card_pos (ExactPSp45.outer_psp45_le_two S h)
  have hk : 1 + ((ExactFin.psp45FC ()).ctx.chP.order 156).factorization 2 ≤
      ((ExactFin.psp45FC ()).ctx.chN.order 156).factorization 2 := by
    rw [hordP, hordN, Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  exact ExactFin.coreStmt_of_model 156 (ExactFin.psp45FC ()) hok e'
    (ExactFin.commutator_eq_top_of_simple_card hnp) hout hk

end CFSG.ComponentClassification.SolMax.SwapP2
