module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.Sporadic.ONOddCore.SeedOrders
public import Certificates.Certificate27142

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore CFSG.EvenSporadicStandard.Solomon78


noncomputable def onCodePerm (c : Nat) : Equiv.Perm (Fin N) :=
  if c = 0 then a0 else if c = 1 then a0⁻¹ else if c = 2 then a1 else a1⁻¹

theorem exists_orderOf_eight_of_check {a b : Array Nat} (ha : PRep N a a0) (hb : PRep N b a1)
    (h : onOrderEightOK a b = true) : ∃ g : ↥Pv, orderOf g = 8 := by
  simp only [onOrderEightOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hia, hib⟩, h8⟩, h4⟩ := h
  have hai := prep_inv_of_pisInv ha hia
  have hbi := prep_inv_of_pisInv hb hib
  have hcode : ∀ c, PRep N (onCodeTab a (pinvCand nPts a) b (pinvCand nPts b) c)
      (onCodePerm c) := by
    intro c
    unfold onCodeTab onCodePerm
    split_ifs <;> assumption
  have hword : ∀ w : List Nat, PRep N (onWordTab a (pinvCand nPts a) b (pinvCand nPts b) w)
      (w.map onCodePerm).prod := by
    intro w
    induction w with
    | nil =>
      have e0 : onWordTab a (pinvCand nPts a) b (pinvCand nPts b) [] = pid nPts := by
        unfold onWordTab
        exact List.foldr_nil
      rw [e0, List.map_nil, List.prod_nil]
      exact prep_pid
    | cons c w ih =>
      have e1 : onWordTab a (pinvCand nPts a) b (pinvCand nPts b) (c :: w) =
          pcomp nPts (onCodeTab a (pinvCand nPts a) b (pinvCand nPts b) c)
            (onWordTab a (pinvCand nPts a) b (pinvCand nPts b) w) := by
        unfold onWordTab
        exact List.foldr_cons
      rw [e1, List.map_cons, List.prod_cons]
      exact prep_pcomp (hcode c) ih
  have hx := hword onWordO8
  have e8 := eq_of_peq (prep_ppow hx 8) prep_pid h8
  have e4 := ne_of_peq_false (prep_ppow hx 4) prep_pid h4
  set x := (onWordO8.map onCodePerm).prod with hxdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 8 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using e4) (by simpa using e8)
    simpa using this
  have hmem : x ∈ Pv := by
    refine Pv.list_prod_mem fun y hy => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
    unfold onCodePerm
    have h0 : a0 ∈ Pv := Subgroup.subset_closure (Set.mem_insert _ _)
    have h1 : a1 ∈ Pv := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    split_ifs
    · exact h0
    · exact Pv.inv_mem h0
    · exact h1
    · exact Pv.inv_mem h1
  refine ⟨⟨x, hmem⟩, ?_⟩
  rw [Subgroup.orderOf_mk]
  exact hord


theorem on_sporadicOrderEight : SporadicOrderEight .ONan := by
  obtain ⟨ha, hb⟩ := seed_facts
  obtain ⟨g, hg⟩ := exists_orderOf_eight_of_check ha hb Certificates.certificate27142
  obtain ⟨e⟩ := on_equiv_Pv (Y := Carrier .ONan) ⟨MulEquiv.refl _⟩
  exact ⟨e.symm g, by rw [MulEquiv.orderOf_eq]; exact hg⟩

end CFSG.EvenSporadicStandard.Induction
