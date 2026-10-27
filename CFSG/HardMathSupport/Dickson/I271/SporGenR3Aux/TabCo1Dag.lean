module

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Data.TabCo1Kit

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Co1Schreier Matrix

theorem foldl_step_flag' (derivs : List (List ℤ))
    (st : List Native.Rows × List Native.Rows × Bool) :
    (derivs.foldl Native.step st).2.2 = true → st.2.2 = true := by
  induction derivs generalizing st with
  | nil => exact id
  | cons w ws ih =>
    intro h
    have := ih _ h
    simp only [Native.step, Bool.and_eq_true] at this
    exact this.1

theorem foldl_step_rep' (derivs : List (List ℤ))
    (st : List Native.Rows × List Native.Rows × Bool) (gs : List GL24)
    (hst : ListRep st.1 st.2.1 gs) (hflag : (derivs.foldl Native.step st).2.2 = true) :
    ListRep (derivs.foldl Native.step st).1 (derivs.foldl Native.step st).2.1
      (derivs.foldl (fun acc w => acc ++ [wordG acc w]) gs) := by
  induction derivs generalizing st gs with
  | nil => exact hst
  | cons w ws ih =>
    refine ih (Native.step st w) (gs ++ [wordG gs w]) ?_ hflag
    have hc := foldl_step_flag' ws _ hflag
    simp only [Native.step, Bool.and_eq_true, beq_iff_eq] at hc
    have hm := MRep.word hst w
    refine ⟨List.rel_append hst.1 (List.Forall₂.cons hm List.Forall₂.nil), ?_⟩
    exact List.rel_append hst.2 (List.Forall₂.cons (hm.inv hc.2) List.Forall₂.nil)

theorem dag_listRep {base : List Native.Rows} {baseG : List GL24}
    (hb : List.Forall₂ MRep base baseG) (derivs : List (List ℤ))
    (hflag : (Native.dag base derivs).2.2 = true) :
    ListRep (Native.dag base derivs).1 (Native.dag base derivs).2.1 (dagG baseG derivs) := by
  have h0 := foldl_step_flag' derivs _ hflag
  simp only [List.all_eq_true, beq_iff_eq] at h0
  have hinv : List.Forall₂ (fun I g => MRep I g⁻¹) (base.map Native.inv) baseG := by
    clear hflag
    induction hb with
    | nil => exact List.Forall₂.nil
    | @cons a b l₁ l₂ hab _ ih =>
      refine List.Forall₂.cons (hab.inv (h0 a (by simp))) (ih fun x hx => h0 x (by simp [hx]))
  exact foldl_step_rep' derivs _ baseG ⟨hb, hinv⟩ hflag

@[expose] noncomputable def kGs (ext : List (List Int)) : List GL24 :=
  dagG [A₁, A₂] (chainDerivs () ++ ext)

@[expose] noncomputable def kG (ext : List (List Int)) (i : ℕ) : GL24 := (kGs ext).getD (i - 1) 1

theorem kGs_mem (ext : List (List Int)) : ∀ g ∈ kGs ext, g ∈ GA := by
  refine dagG_mem (fun g hg => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h
  · rw [h]
    exact A₁_mem
  · rw [h]
    exact A₂_mem

theorem kG_mem (ext : List (List Int)) (i : ℕ) : kG ext i ∈ GA :=
  getD_mem_of_forall (kGs_mem ext) _

section Rep

variable {ext : List (List Int)}

theorem kDag_listRep (h : (kDag ext).2.2 = true) :
    ListRep (kDag ext).1 (kDag ext).2.1 (kGs ext) :=
  dag_listRep (List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil)) _ h

theorem rep_nd (h : (kDag ext).2.2 = true) (i : ℕ) : MRep (nd (kDag ext) i) (kG ext i) :=
  getD_rep (kDag_listRep h).1 MRep.one (i - 1)

theorem rep_ndI (h : (kDag ext).2.2 = true) (i : ℕ) : MRep (ndI (kDag ext) i) (kG ext i)⁻¹ :=
  getD_rep (P := fun I g => MRep I g⁻¹) (kDag_listRep h).2 (by simpa using MRep.one) (i - 1)

theorem listRep_idx (h : (kDag ext).2.2 = true) (idx : List ℕ) :
    ListRep (idx.map (nd (kDag ext))) (idx.map (ndI (kDag ext))) (idx.map (kG ext)) := by
  induction idx with
  | nil => exact ⟨List.Forall₂.nil, List.Forall₂.nil⟩
  | cons i idx ih =>
    exact ⟨List.Forall₂.cons (rep_nd h i) ih.1, List.Forall₂.cons (rep_ndI h i) ih.2⟩

theorem rep_evalW (h : (kDag ext).2.2 = true) (idx : List ℕ) (w : List ℤ) :
    MRep (evalW (kDag ext) idx w) (wordG (idx.map (kG ext)) w) :=
  MRep.word (listRep_idx h idx) w

end Rep

end CFSG.HardMathSupport.Dickson.I271.TabCo1
