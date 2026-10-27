module

public import Certificates.Data.Kernel.L5.Sh2E16
public import CFSG.Certificates.Kernel.L5.Sh0GamSound
public import CFSG.GH74.GLS.C3.Layer2.L5C5eInputs
import all CFSG.GH74.GLS.C3.Layer2.L5C5d

public section

namespace CFSG.KD.L5.E16

open CFSG.Certificates.Kernel.L5S CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

theorem R1Idx_eq : R1Idx = R1IdxC := by
  unfold R1Idx R1IdxC
  congr 1
  funext i
  have e : R1L = (R1L.map cOf).map ev := by
    simp only [List.map_map, Function.comp_def, ev_cOf, List.map_id']
  conv_lhs => rw [e]
  rw [sh0L_getD, decide_mem_map_ev]

theorem all2_eq : all2 = eltsT := rfl

theorem e1_eq (mul : Nat × Bool → Nat × Bool → Nat × Bool) :
    (all2.all fun p => !(p.2 && decide (mul p p = (0, false))) ||
      decide ((all2.filter fun q => decide (mul q q = (0, false)) &&
        decide (mul p q = mul q p)).length < 16)) = e1T mul := by
  unfold e1T invsT centT
  rw [List.all_filter, all2_eq]
  refine List.all_congr rfl fun p => ?_
  rw [List.filter_filter, List.filter_congr fun q _ => Bool.and_comm (decide (mul p q = mul q p)) _]
  cases p.2 <;> cases decide (mul p p = (0, false)) <;> rfl

theorem e2_eq (mul : Nat × Bool → Nat × Bool → Nat × Bool) (A B : List Nat) :
    (all2.all fun p => !(!p.2 && decide (mul p p = (0, false)) && !decide (p.1 ∈ A) &&
        !decide (p.1 ∈ B)) ||
      decide ((all2.filter fun q => !q.2 && decide (mul q q = (0, false)) &&
        decide (mul p q = mul q p)).length < 16)) = e2T mul (A ++ B) := by
  unfold e2T invs0T invsT centT
  rw [List.filter_filter, List.all_filter, all2_eq]
  refine List.all_congr rfl fun p => ?_
  have hf : (eltsT.filter fun q => !q.2 && decide (mul q q = (0, false)) &&
      decide (mul p q = mul q p)) = eltsT.filter fun q =>
        decide (mul p q = mul q p) && (!q.2 && decide (mul q q = (0, false))) :=
    List.filter_congr fun q _ => Bool.and_comm _ _
  have hm : decide (p.1 ∈ A ++ B) = (decide (p.1 ∈ A) || decide (p.1 ∈ B)) := by
    simp only [List.mem_append, Bool.decide_or]
  rw [List.filter_filter, hf, hm]
  generalize decide ((eltsT.filter fun q => decide (mul p q = mul q p) &&
    (!q.2 && decide (mul q q = (0, false)))).length < 16) = X
  cases p.2 <;> cases decide (mul p p = (0, false)) <;> cases decide (p.1 ∈ A) <;>
    cases decide (p.1 ∈ B) <;> cases X <;> rfl

theorem mv_eq (mul : Nat × Bool → Nat × Bool → Nat × Bool) (inv : Nat × Bool → Nat × Bool)
    (R R₁ : List Nat) :
    ((List.range 128).all fun i => R₁.all fun j => R.any fun r =>
      decide (mul (mul (i, true) (r, false)) (inv (i, true)) = (j, false))) = mvT mul inv R R₁ := by
  unfold mvT conjsT
  simp only [List.any_map, Function.comp_def]

section

variable (hc : sh0Chk = true) (hn : ((sh0C.map ev).map pcode).Nodup) (ht : tabsE16 = true)
include hc hn ht

theorem gam_fun {m : Nat} (hm : m < 4) : (fun j => (gamTabs.getD m #[]).getD j 0) = gT m := by
  have hg : gamL m = (List.range 128).map (gamN m) := by
    simp only [tabsE16, List.all_eq_true, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at ht
    exact ht.2 m hm
  funext j
  rw [gamTabs_getD_eq hc hn hm, KT.getD_toArray, hg, gT]
  split_ifs with hj
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem mul2_eq {m : Nat} (hm : m < 4) : mul2 m = mulK m := by
  have e : mul2 m = mulT (fun n => mt0.getD n 0) (fun j => (gamTabs.getD m #[]).getD j 0)
      (ssData.getD m 0) := by
    funext p q
    rfl
  rw [e, mt0_fun hc hn, gam_fun hc hn ht hm]
  rfl

theorem inv2_eq {m : Nat} (hm : m < 4) : inv2 m = invK m := by
  have e : inv2 m = invT (fun n => mt0.getD n 0) (fun n => inv0.getD n 0)
      (fun j => (gamTabs.getD m #[]).getD j 0) (ssData.getD m 0) := by
    funext p
    rfl
  rw [e, mt0_fun hc hn, inv0_fun hc hn, gam_fun hc hn ht hm]
  rfl

omit hc hn in
theorem RIdx_rK : RIdx = rK := by
  simp only [tabsE16, Bool.and_eq_true, decide_eq_true_eq] at ht
  rw [RIdx_eq, ht.1.1]

omit hc hn in
theorem R1Idx_r1K : R1Idx = r1K := by
  simp only [tabsE16, Bool.and_eq_true, decide_eq_true_eq] at ht
  rw [R1Idx_eq, ht.1.2]

theorem sh2Chks_of (hk : ∀ m < 4, ch5068 m = true) :
    (List.range 4).all (fun m => sh2E16Chk1 m && sh2E16Chk2 m && sh2MoveChk m) = true := by
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hm
  have h := hk m hm
  unfold ch5068 at h
  unfold sh2E16Chk1 sh2E16Chk2 sh2MoveChk isInv2 cent2
  rw [mul2_eq hc hn ht hm, inv2_eq hc hn ht hm, RIdx_rK ht, R1Idx_r1K ht, e1_eq, e2_eq, mv_eq]
  exact h

end

end CFSG.KD.L5.E16

end
