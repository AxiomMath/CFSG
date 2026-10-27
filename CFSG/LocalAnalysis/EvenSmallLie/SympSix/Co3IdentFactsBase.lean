
module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModel
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModel
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFactsInputs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDataInputs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
public import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import CFSG.Sporadic.Schreier.Co3Arrays
public import CFSG.Sporadic.Schreier.Co3FirstCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Schreier.Co3Sp6Check
public import CFSG.Sporadic.Schreier.Co3OrbitZCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.Co3Sp6CheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import Mathlib.Data.Matrix.Block
public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck

@[expose] public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

theorem rep_g1 :
    Rep 276 (genArr 1) (gp 1) := rep_gp (i := 1) (by norm_num)
theorem rep_g5 :
    Rep 276 (genArr 5) (gp 5) := rep_gp (i := 5) (by norm_num)

theorem coe_mc :
    ((mc : co3M) : Equiv.Perm (Fin 276)) = gp 2 := coe_mGen (by decide)

theorem perm_aH :
    perm aH = gp 0 := coe_ma
theorem perm_eH :
    perm eH = co3Z := coe_me
theorem perm_cH :
    perm cH = gp 2 := coe_mc
theorem perm_yH :
    perm yH = gp 0 * gp 2 * co3Z := by
  simp only [perm, yH, coe_mul, aH, eH, cH, coe_ma, coe_mc, coe_me]

theorem rep_yH :
    Rep 276 yArr (perm yH) := by
  rw [perm_yH, ← gp_four]
  exact rep_compA (rep_compA rep_g0 rep_g2) rep_g4

theorem rep_eaH :
    Rep 276 eaArr (perm (eH * aH)) := by
  rw [show perm (eH * aH) = co3Z * gp 0 by simp only [perm, coe_mul, eH, aH, coe_me, coe_ma],
    ← gp_four]
  exact rep_compA rep_g4 rep_g0

theorem perm_gH
    (i : ℕ) : perm (gH i)
    = ((mWord (gLetters i) : co3M) : _) := rfl

theorem commutesA_iff
    {x w : edgeGroup} {t u : Array ℕ}
    (ht : Rep 276 t (perm x))
    (hu : Rep 276 u (perm w)) : commutesA 276 t u = true ↔ x * w = w * x := by
  rw [commutesA, eqA_iff (rep_compA ht hu) (rep_compA hu ht)]
  exact ⟨fun h => perm_injective h, fun h => congrArg perm h⟩

theorem bcbM_eq :
    bcbM = mWord [1, 2, 1] := by
  simp [bcbM, mWord, wordOf, mul_assoc]

theorem rep_bcb :
    Rep 276 bcbArr
    ((bcbM : co3M) : Equiv.Perm (Fin 276)) := by
  rw [bcbM_eq]
  exact rep_mWord (by decide)

theorem rep_kp :
    Rep 276 kpArr
    ((kpM : co3M) : Equiv.Perm (Fin 276))
    :=
  rep_mWord kpWord_letters

theorem card_edgeGroup :
    Nat.card
    edgeGroup = 4608 := card_edgeGroup_classA.1

theorem edgeGroup_eq_closure :
    edgeGroup = closure edgeSet := by
  refine le_antisymm (fun x hx => ?_) closure_edgeSet_le
  obtain ⟨j, -, hj⟩ := exists_eltH ⟨x, hx⟩
  have h : ((eltH j : edgeGroup) : co3M) = x := by rw [hj]
  rw [← h, eltH, ← coe_subtype, map_treeEval]
  exact treeEval_mem _ (fun i => mWord_gLetters_mem_closure i) _ _ _

theorem eH_mem_center :
    eH ∈ center edgeGroup := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  exact (me_comm (g : co3M))

theorem aH_mem_center :
    aH ∈ center edgeGroup := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  rw [coe_mul, coe_mul]
  exact mem_centralizer_singleton_iff.1 g.2

theorem comm_y_iff
    (x : edgeGroup) : x * yH = yH * x ↔ x * cH = cH * x := by
  have ha : ∀ g : edgeGroup, g * aH = aH * g := fun g => mem_center_iff.1 aH_mem_center g
  have he : ∀ g : edgeGroup, g * eH = eH * g := fun g => mem_center_iff.1 eH_mem_center g
  have e1 : x * yH = aH * (x * cH) * eH := by
    rw [yH, ← mul_assoc, ← mul_assoc, ha x, mul_assoc aH x cH]
  have e2 : yH * x = aH * (cH * x) * eH := by
    rw [yH, mul_assoc, ← he x, ← mul_assoc, mul_assoc aH]
  rw [e1, e2]
  constructor
  · intro h
    exact mul_left_cancel (mul_right_cancel h)
  · intro h
    rw [h]

theorem card_filter_range (n : ℕ) (P : ℕ → Bool) :
    ((Finset.range n).filter fun j => P j = true).card = ((List.range n).filter P).length := by
  rw [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  simp

theorem perm_psi
    (x : edgeGroup) : perm (psi x) =
    sP * perm x * sP⁻¹ := coe_psi x

theorem psi_eH :
    psi eH = aH :=
  perm_injective (by rw [perm_psi, perm_eH, perm_aH, sP_conj_z'])

theorem psi_aH :
    psi aH = eH :=
  perm_injective (by rw [perm_psi, perm_aH, perm_eH, sP_conj_a'])

theorem rep_yM :
    Rep 276 yArr ((yM : co3M) : Equiv.Perm (Fin 276)) := rep_yH

theorem rep_eaM :
    Rep 276 eaArr ((me * ma : co3M) : Equiv.Perm (Fin 276)) := rep_eaH

end CFSG.EvenSmallLie.SympSix.Co3Ident
