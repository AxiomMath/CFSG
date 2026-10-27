module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWCls
public import Certificates.Certificate27821

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

section Reps


theorem repCheck_all {j : ℕ} (hj : j < 9) :
    isInvA 128 repArrs[j]! (invCand 128 repArrs[j]!) = true ∧
      eqA 128 (compA 128 repArrs[j]! repArrs[j]!) (idA 128) = true ∧
      inPg repArrs[j]! = true ∧ neOneW [repArrs[j]!] = true ∧
      (fixCntW [repArrs[j]!] == (fpTab[j]!).1) = true ∧
      (fixSqW [repArrs[j]!] == (fpTab[j]!).2) = true := by
  have h := Certificates.certificate27821.1
  unfold repCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have h' := h.2 j hj
  exact ⟨h'.1.1.1.1.1, h'.1.1.1.1.2, h'.1.1.1.2, h'.1.1.2, h'.1.2, h'.2⟩

theorem repPerm_rep {j : ℕ} (hj : j < 9) : Rep 128 repArrs[j]! (repPerm j) :=
  (rep_permOfArr (repCheck_all hj).1).1

theorem repPerm_mem {j : ℕ} (hj : j < 9) : repPerm j ∈ Pg :=
  (inPg_iff (repPerm_rep hj)).1 (repCheck_all hj).2.2.1

theorem repPerm_sq {j : ℕ} (hj : j < 9) : repPerm j * repPerm j = 1 :=
  (eqA_iff (rep_compA (repPerm_rep hj) (repPerm_rep hj)) rep_idA).1 (repCheck_all hj).2.1

theorem repPerm_ne_one {j : ℕ} (hj : j < 9) : repPerm j ≠ 1 := by
  intro h
  obtain ⟨x, -, hne⟩ := (neOneW_iff (RepW.single (repPerm_rep hj))).1 (repCheck_all hj).2.2.2.1
  exact hne (by rw [h, Equiv.Perm.one_apply])

theorem fp_repPerm {j : ℕ} (hj : j < 9) : fp (repPerm j) = fpTab[j]! := by
  have h1 : fixCnt (repPerm j) = (fpTab[j]!).1 := by
    rw [← fixCntW_eq (RepW.single (repPerm_rep hj))]
    exact beq_iff_eq.1 (repCheck_all hj).2.2.2.2.1
  have h2 : fixSq (repPerm j) = (fpTab[j]!).2 := by
    rw [← fixSqW_eq (RepW.single (repPerm_rep hj))]
    exact beq_iff_eq.1 (repCheck_all hj).2.2.2.2.2
  exact Prod.ext h1 h2

@[expose] noncomputable def repPg (j : Fin 9) : Pg := ⟨repPerm j, repPerm_mem j.2⟩

theorem fpTab_ne {j j' : ℕ} (hj : j < 9) (hj' : j' < 9) (hne : j ≠ j') :
    fpTab[j]! ≠ fpTab[j']! := by
  have h := Certificates.certificate27821.2.1
  unfold fpDistinct at h
  have h2 := (List.all_eq_true.1 h) j (List.mem_range.2 hj)
  have h3 := (List.all_eq_true.1 h2) j' (List.mem_range.2 hj')
  simpa [hne] using h3

end Reps

section Counts


theorem card_invol : Nat.card {g : Pg // g * g = 1 ∧ g ≠ 1} = 10575 := by
  have h1 : Nat.card {g : Pg // (g : Equiv.Perm (Fin 128)) * g = 1 ∧
      (g : Equiv.Perm (Fin 128)) ≠ 1} = countW involW blocksPg [] :=
    card_eq_countW_Pg (f := involW) (Pr := fun π => π * π = 1 ∧ π ≠ 1)
      fun w g hw hg => involW_iff hw hg
  have h2 : countW involW blocksPg [] = 10575 := by
    have h := Certificates.certificate27821.2.2.2.2
    unfold involCheck at h
    exact eqNatB_iff.1 h
  have h3 : Nat.card {g : Pg // g * g = 1 ∧ g ≠ 1} = Nat.card {g : Pg //
      (g : Equiv.Perm (Fin 128)) * g = 1 ∧ (g : Equiv.Perm (Fin 128)) ≠ 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => by
      simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one, ne_eq])
  rw [h3, h1, h2]

theorem card_cent (j : Fin 9) :
    Nat.card (Subgroup.centralizer ({repPg j} : Set Pg)) = centTab[(j : ℕ)]! := by
  have h := Certificates.certificate27821.2.2.2.1
  unfold centCheck at h
  have h2 : countW (commW repArrs[(j : ℕ)]!) blocksPg [] = centTab[(j : ℕ)]! :=
    beq_iff_eq.1 ((List.all_eq_true.1 h) (j : ℕ) (List.mem_range.2 j.2))
  have h1 : Nat.card {x : Pg // (x : Equiv.Perm (Fin 128)) * repPerm j =
      repPerm j * (x : Equiv.Perm (Fin 128))} = countW (commW repArrs[(j : ℕ)]!) blocksPg [] :=
    card_eq_countW_Pg (f := commW repArrs[(j : ℕ)]!) (Pr := fun π => π * repPerm j = repPerm j * π)
      fun w g hw hg => commW_iff (repPerm_rep j.2) (repPerm_mem j.2) hw hg
  rw [← h2, ← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

end Counts

end CFSG.EvenSporadicStandard.Fin76b.W16
