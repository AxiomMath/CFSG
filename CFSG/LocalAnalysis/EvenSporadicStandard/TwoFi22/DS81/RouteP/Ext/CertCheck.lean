module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.CertMaskA
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.CertMaskB

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu Certificates.RouteP.M24Defect

theorem checkAll_spec (h : checkAll () = true) :
    relsOK = true ∧ treeOK (treeTab ()) = true ∧ treeLetters (treeTab ()) = true ∧
      (comboData ()).length = 67 ∧
      (∀ ents ∈ comboData (), entriesOK ents = true ∧
        bucketsZero (comboContribs (treeTab ()) ents) = true) ∧
      bezoutOK ((comboData ()).map (comboFs (treeTab ()))) (sData ()) (tData ()) = true := by
  simp only [checkAll, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hr⟩, hC⟩, hL⟩, hlen⟩, hall⟩, hbez⟩ := h
  exact ⟨hr, hC, hL, hlen, hall, hbez⟩

theorem exists_lam_of_combos (tab : Array (List (ℕ × Bool))) (cs : List (List (ℕ × ℕ × ℕ)))
    (S : List (ℕ × ℕ)) (T : List (List ℕ)) (hlen : cs.length = 67)
    (hcombos : ∀ ents ∈ cs, entriesOK ents = true ∧
      bucketsZero (comboContribs tab ents) = true)
    (hbez : bezoutOK (cs.map (comboFs tab)) S T = true) (d ψ : ℕ → ℕ)
    (hsys : ∀ p i m : ℕ, p / 24 < 24 → p % 24 < 24 → p / 24 ≠ p % 24 → i < 7 → m < 2048 →
      bp (fpart tab p m) (d i) = ((contribs tab p i m).map fun c => bp c.2 (ψ c.1)).sum) :
    ∃ z : ℕ × ℕ, ∀ i < 7, bvec 11 (d i) = bvec 11 (lamApply z i) := by
  refine exists_lam_of_bezout _ _ _ hbez d fun r hr => ?_
  have hr' : r < cs.length := by omega
  obtain ⟨hent, hb⟩ := hcombos _ (List.getElem_mem hr')
  have h0 := combo_sum_eq_zero tab (cs[r]) hent hb d ψ hsys
  have hmap : ((List.range 7).map fun i => bp ((((cs.map (comboFs tab))[r]!))[i]!) (d i)) =
      (List.range 7).map fun i => bp (comboF tab (cs[r]) i) (d i) := by
    refine List.map_congr_left fun i hi => ?_
    have hi7 : i < 7 := List.mem_range.1 hi
    simp [comboFs, hr', hi7]
  rw [hmap]
  exact h0

theorem exists_lam_of_checkAll (hcheck : checkAll () = true) (d ψ : ℕ → ℕ)
    (hsys : ∀ p i m : ℕ, p / 24 < 24 → p % 24 < 24 → p / 24 ≠ p % 24 → i < 7 → m < 2048 →
      bp (fpart (treeTab ()) p m) (d i) =
        ((contribs (treeTab ()) p i m).map fun c => bp c.2 (ψ c.1)).sum) :
    ∃ z : ℕ × ℕ, ∀ i < 7, bvec 11 (d i) = bvec 11 (lamApply z i) := by
  obtain ⟨-, -, -, hlen, hcombos, hbez⟩ := checkAll_spec hcheck
  exact exists_lam_of_combos _ _ _ _ hlen hcombos hbez d ψ hsys

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
