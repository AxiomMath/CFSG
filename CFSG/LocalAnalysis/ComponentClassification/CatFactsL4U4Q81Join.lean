module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Cent

public section

namespace CFSG.ComponentClassification.HarrisLit.Q81

open CFSG Subgroup

variable {G : Type} [Group G]

abbrev centerIn (C : Subgroup G) : Subgroup G := (center ↥C).map C.subtype

theorem mem_centerIn {C : Subgroup G} {x : G} :
    x ∈ centerIn C ↔ x ∈ C ∧ ∀ y ∈ C, x * y = y * x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, fun y hy => congrArg Subtype.val (mem_center_iff.mp hc ⟨y, hy⟩).symm⟩
  · rintro ⟨hx, hxc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun y => Subtype.ext (hxc y y.2).symm, rfl⟩

theorem mem_iSup_center_of_central {ι : Type*} (f : ι → Subgroup G) (s : Finset ι)
    (hc : ∀ i ∈ s, ∀ j ∈ s, f i ≠ f j → f i ≤ centralizer (f j : Set G)) {x : G}
    (hx : x ∈ ⨆ i ∈ s, f i) (hxc : ∀ y ∈ ⨆ i ∈ s, f i, x * y = y * x) :
    x ∈ ⨆ i ∈ s, centerIn (f i) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    have hx' : x = 1 := by simpa using hx
    rw [hx']
    exact one_mem _
  | insert i s hi ih =>
    have hc' : ∀ k ∈ s, ∀ l ∈ s, f k ≠ f l → f k ≤ centralizer (f l : Set G) := fun k hk l hl =>
      hc k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl)
    rw [Finset.iSup_insert] at hx hxc ⊢
    by_cases hdup : ∃ j ∈ s, f j = f i
    ·
      obtain ⟨j, hj, hji⟩ := hdup
      have hle : f i ≤ ⨆ k ∈ s, f k := hji ▸ le_biSup f hj
      rw [sup_eq_right.mpr hle] at hx hxc
      exact mem_sup_right (ih hc' hx hxc)
    · push Not at hdup
      have hcomm : f i ≤ centralizer ((⨆ k ∈ s, f k : Subgroup G) : Set G) := by
        rw [le_centralizer_iff]
        refine iSup₂_le fun k hk => ?_
        exact hc k (Finset.mem_insert_of_mem hk) i (Finset.mem_insert_self i s) (hdup k hk)
      obtain ⟨c, hcf, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
      have hcb : ∀ y ∈ ⨆ k ∈ s, f k, c * y = y * c := fun y hy =>
        (mem_centralizer_iff.mp (hcomm hcf) y hy).symm
      have hbf : ∀ y ∈ f i, b * y = y * b := fun y hy =>
        (mem_centralizer_iff.mp (hcomm hy) b hb)
      have hcZ : c ∈ centerIn (f i) := by
        refine mem_centerIn.mpr ⟨hcf, fun y hy => ?_⟩
        have h1 := hxc y (mem_sup_left hy)
        have h2 : c * y * b = y * c * b := by
          calc c * y * b = c * (b * y) := by rw [mul_assoc, ← hbf y hy]
            _ = c * b * y := by rw [mul_assoc]
            _ = y * (c * b) := h1
            _ = y * c * b := by rw [mul_assoc]
        exact mul_right_cancel h2
      have hbc : ∀ y ∈ ⨆ k ∈ s, f k, b * y = y * b := by
        intro y hy
        have h1 := hxc y (mem_sup_right hy)
        have h2 : c * (b * y) = c * (y * b) := by
          calc c * (b * y) = c * b * y := by rw [mul_assoc]
            _ = y * (c * b) := h1
            _ = y * c * b := by rw [mul_assoc]
            _ = c * y * b := by rw [hcb y hy]
            _ = c * (y * b) := by rw [mul_assoc]
        exact mul_left_cancel h2
      exact mul_mem (mem_sup_left hcZ) (mem_sup_right (ih hc' hb hbc))

theorem isElemTwo_iSup {ι : Type*} (f : ι → Subgroup G) (s : Finset ι)
    (hE : ∀ i ∈ s, GrSLit.IsElemTwo (f i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, f i ≤ centralizer (f j : Set G)) :
    GrSLit.IsElemTwo (⨆ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · have ha' : a = 1 := by simpa using ha
      have hb' : b = 1 := by simpa using hb
      rw [ha', hb']
    · have ha' : a = 1 := by simpa using ha
      rw [ha', one_mul]
  | insert i s hi ih =>
    have hE' : ∀ k ∈ s, GrSLit.IsElemTwo (f k) := fun k hk => hE k (Finset.mem_insert_of_mem hk)
    have hc' : ∀ k ∈ s, ∀ l ∈ s, f k ≤ centralizer (f l : Set G) := fun k hk l hl =>
      hc k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl)
    have h1 := ih hE' hc'
    have hi' := hE i (Finset.mem_insert_self i s)
    rw [Finset.iSup_insert]
    have hcomm : f i ≤ centralizer ((⨆ k ∈ s, f k : Subgroup G) : Set G) := by
      rw [le_centralizer_iff]
      exact iSup₂_le fun k hk => hc k (Finset.mem_insert_of_mem hk) i (Finset.mem_insert_self i s)
    have hcb : ∀ a ∈ f i, ∀ b ∈ ⨆ k ∈ s, f k, a * b = b * a := fun a ha b hb =>
      (mem_centralizer_iff.mp (hcomm ha) b hb).symm
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
      obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup hcomm hy
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [← hcb a' ha' b hb]
        _ = (a * a') * (b * b') := by group
        _ = (a' * a) * (b' * b) := by rw [hi'.1 a ha a' ha', h1.1 b hb b' hb']
        _ = a' * (a * b') * b := by group
        _ = a' * (b' * a) * b := by rw [hcb a ha b' hb']
        _ = a' * b' * (a * b) := by group
    · obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hcb a ha b hb]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [hi'.2 a ha, h1.2 b hb, one_mul]

end CFSG.ComponentClassification.HarrisLit.Q81
