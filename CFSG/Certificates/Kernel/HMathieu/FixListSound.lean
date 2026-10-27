module

public import Certificates.Data.Kernel.HMathieu.FixList
public import CFSG.Certificates.Kernel.HMathieu.OddSound

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu

theorem ascFrom_pairwise {a : Nat} {l : List Nat} (h : ascFrom a l = true) :
    (a :: l).Pairwise (· < ·) := by
  induction l generalizing a with
  | nil => exact List.pairwise_singleton _ _
  | cons b l ih =>
    simp only [ascFrom, Bool.and_eq_true, Nat.blt_eq] at h
    have hb := ih h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, hb⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.1 hb).1 x hx)

theorem ascB_pairwise : ∀ {l : List Nat}, ascB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | _ :: _, h => ascFrom_pairwise h

theorem fixList_eq {n : Nat} {M J R : List Nat} (h : fixListOK n M J R = true) :
    (List.range (2 ^ n)).filter (fun m => actM M m == m) = R := by
  simp only [fixListOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hJ, hok⟩, hR⟩, hasc⟩, hlen⟩ := h
  have hFle : ((List.range (2 ^ n)).filter (fun m => actM M m == m)).length ≤ R.length := by
    rw [length_filter_eq_card]
    exact (fix_le_of_imgOK hJ hok).trans hlen
  have hRp := ascB_pairwise hasc
  have hFp : ((List.range (2 ^ n)).filter (fun m => actM M m == m)).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hsub : R ⊆ (List.range (2 ^ n)).filter (fun m => actM M m == m) := fun v hv =>
    List.mem_filter.2 ⟨List.mem_range.2 (hR v hv).1, by simpa using (hR v hv).2⟩
  have hnd : R.Nodup := hRp.imp ne_of_lt
  have hperm := (hnd.subperm hsub).perm_of_length_le hFle
  exact (List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => absurd h1 (Nat.lt_asymm h2)) hRp hFp
    hperm).symm

theorem fixAll_sound {ok : List Nat → Bool} {cc lift : List Nat} {n : Nat} {E : List Nat} :
    ∀ {Js Rs : List (List Nat)}, fixAllK ok cc lift n E Js Rs = true →
      ∀ e ∈ E, ok ((List.range (2 ^ n)).filter fun m => actM (matP cc lift n e) m == m) = true := by
  induction E with
  | nil => intro _ _ _ e he; exact absurd he List.not_mem_nil
  | cons e E ih =>
    intro Js Rs h e' he'
    simp only [fixAllK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · rw [fixList_eq h.1.1]
      exact h.1.2
    · exact ih h.2 e' he'

theorem fixAll_of {T : PT 24} [Fact (T.check = true)] {cc' lift' : List Nat} {n' r fuel : Nat}
    {gens E : List Nat} {Js' : List (List Nat)} (hT : T = PT.ofGens 24 (gens.map unpk) fuel)
    (h : oddOK cc' lift' n' r fuel gens E Js' = true) {ok : List Nat → Bool} {cc lift : List Nat}
    {n : Nat} {Js Rs : List (List Nat)} (hk : fixAllK ok cc lift n (E.drop 1) Js Rs = true)
    {mats : Array (List Nat)}
    (hm : mats = T.elems.map fun a => matOf n fun m => actM cc (permM a (actM lift m))) :
    ∀ p : T.Elem, p ≠ 1 → ok (fixMasks n (fun q m => actM (mats[q.idx]!) m) [p]) = true := by
  intro p hp
  have H := packed_of_oddOK hT h
  have hidx : p.idx ≠ 0 := fun e => hp (PT.Elem.ext' (by rw [e, PT.idx_one, H.one]))
  have hM : mats[p.idx]! = matP cc lift n (pk E p) := by
    rw [hm, map_elems_get H]
    unfold matP matOf
    simp only [actM_unpk]
  have hlt := idx_lt H p
  have hmem : pk E p ∈ E.drop 1 := by
    rw [pk_eq H]
    have e : E[p.idx] = (E.drop 1)[p.idx - 1]'(by simp; omega) := by
      rw [List.getElem_drop]
      congr 1
      omega
    rw [e]
    exact List.getElem_mem _
  simp only [fixMasks, List.all_cons, List.all_nil, Bool.and_true, hM]
  exact fixAll_sound hk _ hmem

end CFSG.KC.HMathieu

end
