module

public import CFSG.ClassicalInvolution.Generic.StepLayer

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ComponentClassification

theorem native_isQuasisimple {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    CFSG.IsQuasisimple G :=
  ⟨⟨h.1⟩, h.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian G h⟩

theorem eq_or_le_center_of_isSubnormal {X : Type*} [Group X] {A B : Subgroup X}
    (h : IsSubnormal A B) (hB : CFSG.IsQuasisimple B) :
    A = B ∨ A ≤ (Subgroup.center B).map B.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hB with hMB | hM
    · subst hMB
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hB hn with h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · refine Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h ?_, rfl⟩
        exact hx
    · exact Or.inr (hAM.trans hM)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem eq_of_le_sup_of_isClassicalMember (hq4 : 4 ≤ p ^ f) {L A B : Subgroup G} {z : G}
    (h : IsClassicalMember p f L z) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hLAB : L ≤ A ⊔ B) (hzB : z ∉ B)
    (hAC : A ≤ Subgroup.centralizer ({z} : Set G)) (hAq : CFSG.Open.IsQuasisimple ↥A)
    (hBq : B = ⊥ ∨ CFSG.Open.IsQuasisimple ↥B) : L = A := by
  have hLA : L ≤ A := by
    rcases hBq with hB | hBq
    · rw [hB, sup_bot_eq] at hLAB
      exact hLAB
    · set Y : Subgroup G := A ⊔ B with hYdef
      have hAY : A ≤ Y := le_sup_left
      have hBY : B ≤ Y := le_sup_right
      have hzY : z ∈ Y := hLAB h.mem
      have hLmem := h.subgroupOf p f hLAB
      have hYA : Y ≤ Subgroup.normalizer (A : Set G) := by
        refine sup_le Subgroup.le_normalizer (Subgroup.le_normalizer_iff.mpr fun y hy x hx => ?_)
        have hxy := hcomm x hx y hy
        have : y * x * y⁻¹ = x := by rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
        rw [this]
        exact hx
      have hYB : Y ≤ Subgroup.normalizer (B : Set G) := by
        refine sup_le (Subgroup.le_normalizer_iff.mpr fun x hx y hy => ?_) Subgroup.le_normalizer
        have hxy := hcomm x hx y hy
        have : x * y * x⁻¹ = y := by rw [hxy, mul_assoc, mul_inv_cancel, mul_one]
        rw [this]
        exact hy
      have hcomp : ∀ {C : Subgroup G} (hCY : C ≤ Y) (hN : Y ≤ Subgroup.normalizer (C : Set G)),
          CFSG.Open.IsQuasisimple ↥C → IsComponentOf (C.subgroupOf Y) ⊤ := by
        intro C hCY hN hCq
        refine ⟨le_top, ?_, ?_⟩
        · refine isSubnormal_of_normal_subgroupOf le_top ?_
          rw [Subgroup.normal_subgroupOf_iff le_top]
          intro x k hx _
          have hx' : (x : G) ∈ C := hx
          exact (Subgroup.mem_normalizer_iff.mp (hN k.2) x).mp hx'
        · exact Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hCY) hCq
      have hTA := hcomp hAY hYA hAq
      have hTB := hcomp hBY hYB hBq
      have hsup : A.subgroupOf Y ⊔ B.subgroupOf Y = ⊤ := by
        have h1 : (A ⊔ B).subgroupOf Y = A.subgroupOf Y ⊔ B.subgroupOf Y :=
          (Subgroup.comap_sup_eq_of_le_range Y.subtype
            (by rw [Subgroup.range_subtype]; exact hAY)
            (by rw [Subgroup.range_subtype]; exact hBY)).symm
        rw [← h1]
        exact Subgroup.subgroupOf_self Y
      have hlayer : Layer.subgroup ↥Y = ⊤ := by
        rw [eq_top_iff, ← hsup]
        exact sup_le (Layer.component_le hTA) (Layer.component_le hTB)
      rcases IsClassicalMember.le_or_le_centralizer_of_component hq4 hlayer hTA hLmem with
        hc1 | hc1
      · intro x hx
        exact hc1 (show (⟨x, hLAB hx⟩ : ↥Y) ∈ L.subgroupOf Y from hx)
      · exfalso
        rcases IsClassicalMember.le_or_le_centralizer_of_component hq4 hlayer hTB hLmem with
          hc2 | hc2
        · exact hzB (hc2 (show (⟨z, hzY⟩ : ↥Y) ∈ L.subgroupOf Y from h.mem))
        · apply hLmem.not_le_center
          intro x hx
          rw [Subgroup.mem_center_iff]
          intro g
          have hx1 : A.subgroupOf Y ≤ Subgroup.centralizer ({x} : Set ↥Y) := fun t ht =>
            Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_iff.mp (hc1 hx) t ht)
          have hx2 : B.subgroupOf Y ≤ Subgroup.centralizer ({x} : Set ↥Y) := fun t ht =>
            Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_iff.mp (hc2 hx) t ht)
          have hg : g ∈ Subgroup.centralizer ({x} : Set ↥Y) := by
            have : (⊤ : Subgroup ↥Y) ≤ Subgroup.centralizer ({x} : Set ↥Y) := by
              rw [← hsup]
              exact sup_le hx1 hx2
            exact this (Subgroup.mem_top g)
          exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hsubA : IsSubnormal L A := by
    have h1 := isSubnormal_inf h.subnormal A
    rwa [inf_eq_left.mpr hLA, inf_eq_right.mpr hAC] at h1
  rcases eq_or_le_center_of_isSubnormal hsubA (native_isQuasisimple hAq) with h1 | h1
  · exact h1
  · exfalso
    have hcomm' : ∀ x y : L, x * y = y * x := fun x y => by
      obtain ⟨c, hc, hcx⟩ := h1 x.2
      apply Subtype.ext
      have := Subgroup.mem_center_iff.mp hc ⟨y, hLA y.2⟩
      have h3 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at h3 hcx
      show (x : G) * y = y * x
      rw [← hcx]
      exact h3.symm
    have hperf : Group.IsPerfect ↥L := h.perfect
    have hzmem : (⟨z, h.mem⟩ : ↥L) ∈ commutator ↥L := by
      rw [hperf.commutator_eq_top]
      exact Subgroup.mem_top _
    have hbot : commutator ↥L ≤ ⊥ := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm' x y
    exact h.ne_one (congrArg Subtype.val (Subgroup.mem_bot.mp (hbot hzmem)))

end CFSG.ClassicalInvolution.ModelFacts
