module

public import Certificates.Data.ChengHeldExcl1Facts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Model

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model

theorem chExcl1_parts (h : chExcl1OK = true) : ∀ α, α ≤ 1 → exclXiM (mkReg α) = true := by
  intro α hα
  simp only [chExcl1OK, List.all_eq_true, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at h
  interval_cases α
  exacts [h.1, h.2]

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.sq_mem_zpowers_of_comm_xi (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hE : chExcl1OK = true) {w : G} (hw : w ∈ c.W)
    (hcomm : w * c.xi = c.xi * w) : w * w ∈ zpowers c.t := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hk := chExcl1_parts hE α hα
  have eW := c.set_secW R hR
  have eZ := c.set_secZ R hR
  have nW := Rep.cent_size (M := mkReg α) (secV (mkReg α))
  rw [← SFacts4Aux.map_sW c] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  have hpt : R.pt w' ∈ RegModel.elems ((mkReg α).cent (secV (mkReg α))) :=
    (R.mem_elems_iff_exists_pt nW).2 ⟨w', rfl, by rw [eW]; exact hw'⟩
  simp only [exclXiM, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hk
  rcases hk _ hpt with hne | hZ
  · exfalso
    apply hne
    have h6 : (mkReg α).g 6 = R.pt (c.fam 6) := (hR 6).symm
    rw [h6, ← R.pt_mul, ← R.pt_mul]
    congr 1
    apply Subtype.ext
    have hx6 : ((c.fam 6 : ↥d.S) : G) = c.xi := rfl
    simp only [Subgroup.coe_mul, hx6]
    simpa using hcomm
  · have h1 : w' * w' ∈ R.set (secZ (mkReg α)) := by
      rw [Rep.mem_set, R.pt_mul]
      exact hZ
    rw [eZ] at h1
    have h2 := mem_zpowers_sub_iff.1 h1
    have ht0 : ((c.fam 0 : ↥d.S) : G) = c.t := rfl
    rw [ht0] at h2
    simpa using h2

end CFSG.OddStandard.ChengHeld
