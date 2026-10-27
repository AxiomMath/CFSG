module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HNorm
public import Certificates.Certificate26882

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std.HS08Check

theorem normProp : NormProp :=
  of_decide_eq_true Certificates.certificate26882

end CFSG.EvenSporadicStandard.M22Std.HS08Check

namespace CFSG.EvenSporadicStandard.M22Std.HS08H

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check CFSG.EvenSporadicStandard.M22Std.HS08Check
  CFSG.Blueprint.NativeSporadic

theorem trans_of_conj_base {G : Type*} [Group G] (N : Subgroup G) (R : Set G) (x0 : G)
    (h : ∀ z ∈ R, ∃ d ∈ N, d * x0 * d⁻¹ = z) :
    ∀ x ∈ R, ∀ y ∈ R, ∃ d ∈ N, d * x * d⁻¹ = y := by
  intro x hx y hy
  obtain ⟨dx, hdx, hdxx⟩ := h x hx
  obtain ⟨dy, hdy, hdyy⟩ := h y hy
  refine ⟨dy * dx⁻¹, N.mul_mem hdy (N.inv_mem hdx), ?_⟩
  rw [← hdxx, ← hdyy]
  group


theorem exists_mem_normalizer_of_mem_dTabs {d : Tab} (hd : d ∈ dTabs) :
    ∃ δ ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), autTab δ = d := by
  obtain ⟨δ, hδ, hδd⟩ := isTabsOf_dSub.exists_mem d hd
  exact ⟨δ, normalizer_jSub_eq ▸ hδ, hδd⟩

theorem card_jSub_inner :
    Nat.card ↥(jSub ⊓ innerImage (Carrier .M22) ⊤) = 16 := by
  have hset : ((jSub ⊓ innerImage (Carrier .M22) ⊤ : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22))) = {a | autTab a ∈ jInn} := by
    ext a
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_ofPred_eq, autTab_mem_jInn_iff]
  have h1 := ncard_preimage_mem_tabs autTab autTab_injective jInn (jTabs_nodup.filter _)
    fun l hl => by
      obtain ⟨x, -, hx⟩ := exists_mem_jSub (List.mem_filter.1 hl).1
      exact ⟨x, hx⟩
  rw [← normProp.1, ← h1, ← hset]
  exact Nat.card_coe_set_eq _

theorem centralizer_jSub_le (α : MulAut (Carrier .M22)) (h : ∀ x ∈ jSub, α * x = x * α) :
    α ∈ jSub := by
  have hN : α ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))) := by
    refine mem_normalizer_of_conj_mem jSub α fun x hx => ?_
    rw [h x hx, mul_inv_cancel_right]
    exact hx
  have hα : autTab α ∈ dTabs := (mem_normalizer_jSub_iff α).1 hN
  refine mem_jSub.2 (normProp.2.2.1 _ hα fun j hj => ?_)
  obtain ⟨x, hx, rfl⟩ := exists_mem_jSub hj
  rw [← autTab_mul, ← autTab_mul, h x hx]

theorem trans_inner_jSub :
    ∀ x ∈ jSub ⊓ innerImage (Carrier .M22) ⊤, x ≠ 1 → ∀ y ∈ jSub ⊓ innerImage (Carrier .M22) ⊤,
      y ≠ 1 → ∃ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), d * x * d⁻¹ = y := by
  have hP := normProp
  obtain ⟨x4, -, hx4⟩ := exists_mem_jSub hP.2.2.2.2.1
  have key : ∀ y ∈ jSub ⊓ innerImage (Carrier .M22) ⊤, y ≠ 1 →
      ∃ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), d * x4 * d⁻¹ = y := by
    intro y hy hy1
    have hyt : autTab y ∈ jInn.filter fun l => decide (l ≠ idTab) := by
      rw [List.mem_filter]
      refine ⟨(autTab_mem_jInn_iff y).2 hy, ?_⟩
      simp only [decide_eq_true_eq]
      intro h
      exact hy1 (autTab_injective (h.trans autTab_one.symm))
    obtain ⟨d, hd, hdy⟩ := hP.2.2.2.1 _ hyt
    obtain ⟨δ, hδ, rfl⟩ := exists_mem_normalizer_of_mem_dTabs hd
    exact ⟨δ, hδ, conj_eq_of_tmul (by rw [hx4]; exact hdy)⟩
  intro x hx hx1 y hy hy1
  exact trans_of_conj_base _ {z | z ∈ jSub ⊓ innerImage (Carrier .M22) ⊤ ∧ z ≠ 1} x4
    (fun z hz => key z hz.1 hz.2) x ⟨hx, hx1⟩ y ⟨hy, hy1⟩

theorem orbit_props {x0 : Tab} (hx0 : x0 ∈ jTabs)
    (hcl : ∀ d ∈ dTabs, ∀ x ∈ jOrb x0, ∃ y ∈ jOrb x0, tmul d x = tmul y d) :
    {x : MulAut (Carrier .M22) | autTab x ∈ jOrb x0}.ncard = (jOrb x0).length ∧
    (∀ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))),
      ∀ x ∈ {x : MulAut (Carrier .M22) | autTab x ∈ jOrb x0}, d * x * d⁻¹ ∈
        {x : MulAut (Carrier .M22) | autTab x ∈ jOrb x0}) ∧
    (∀ x ∈ {x : MulAut (Carrier .M22) | autTab x ∈ jOrb x0},
      ∀ y ∈ {x : MulAut (Carrier .M22) | autTab x ∈ jOrb x0},
        ∃ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), d * x * d⁻¹ = y) := by
  have hatt : ∀ l ∈ jOrb x0, ∃ a : MulAut (Carrier .M22), autTab a = l := fun l hl => by
    obtain ⟨x, -, hx⟩ := exists_mem_jSub (List.mem_filter.1 (List.mem_filter.1 hl).1).1
    exact ⟨x, hx⟩
  refine ⟨ncard_preimage_mem_tabs autTab autTab_injective (jOrb x0)
    ((jTabs_nodup.filter _).filter _) hatt, ?_, ?_⟩
  · intro d hd x hx
    obtain ⟨y, hy, hdxy⟩ := hcl _ ((mem_normalizer_jSub_iff d).1 hd) _ hx
    obtain ⟨y', rfl⟩ := hatt y hy
    have h := conj_eq_of_tmul (α := d) (β := x) (γ := y') hdxy
    show autTab (d * x * d⁻¹) ∈ jOrb x0
    rw [h]
    exact hy
  · obtain ⟨x0', -, hx0'⟩ := exists_mem_jSub hx0
    refine trans_of_conj_base _ _ x0' fun z hz => ?_
    have hz' : autTab z ∈ jOrb x0 := hz
    have h2 := (List.mem_filter.1 hz').2
    simp only [List.any_eq_true, decide_eq_true_eq] at h2
    obtain ⟨d, hd, hdx⟩ := h2
    obtain ⟨δ, hδ, rfl⟩ := exists_mem_normalizer_of_mem_dTabs hd
    exact ⟨δ, hδ, conj_eq_of_tmul (by rw [hx0']; exact hdx)⟩

theorem outer_orbits_jSub : ∃ R6 R10 : Set (MulAut (Carrier .M22)),
    R6 ∪ R10 = {x | x ∈ jSub ∧ x ∉ innerImage (Carrier .M22) ⊤} ∧ Disjoint R6 R10 ∧
      R6.ncard = 6 ∧ R10.ncard = 10 ∧
      (∀ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), ∀ x ∈ R6,
        d * x * d⁻¹ ∈ R6) ∧
      (∀ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), ∀ x ∈ R10,
        d * x * d⁻¹ ∈ R10) ∧
      (∀ x ∈ R6, ∀ y ∈ R6,
        ∃ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), d * x * d⁻¹ = y) ∧
      (∀ x ∈ R10, ∀ y ∈ R10,
        ∃ d ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))), d * x * d⁻¹ = y) := by
  obtain ⟨-, -, -, -, -, hx6, hx10, hl6, hl10, hcov, hdisj, hcl6, hcl10⟩ := normProp
  obtain ⟨n6, c6, t6⟩ := orbit_props hx6 hcl6
  obtain ⟨n10, c10, t10⟩ := orbit_props hx10 hcl10
  refine ⟨{x | autTab x ∈ jOrb x6Tab}, {x | autTab x ∈ jOrb x10Tab}, ?_, ?_, ?_, ?_, c6, c10, t6,
    t10⟩
  · ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h)
      · exact (autTab_mem_jOut_iff x).1 (List.mem_filter.1 h).1
      · exact (autTab_mem_jOut_iff x).1 (List.mem_filter.1 h).1
    · intro h
      exact hcov _ ((autTab_mem_jOut_iff x).2 h)
  · exact Set.disjoint_left.2 fun x h6 h10 => hdisj _ h6 h10
  · rw [n6, hl6]
  · rw [n10, hl10]

end CFSG.EvenSporadicStandard.M22Std.HS08H
