module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsS0

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic

theorem ncard_preimage_mem_tabs {α : Type*} (e : α → Tab) (he : Function.Injective e)
    (L : List Tab) (hL : L.Nodup) (hex : ∀ l ∈ L, ∃ a, e a = l) :
    {a | e a ∈ L}.ncard = L.length := by
  classical
  have h : e '' {a | e a ∈ L} = ↑L.toFinset := by
    ext l
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact List.mem_toFinset.2 ha
    · intro hl
      obtain ⟨a, ha⟩ := hex l (List.mem_toFinset.1 hl)
      exact ⟨a, by rw [Set.mem_ofPred_eq, ha]; exact List.mem_toFinset.1 hl, ha⟩
  rw [← Set.ncard_image_of_injective _ he, h, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

theorem mem_iff_of_maps {Y : Type*} [Group Y] [Finite Y] (F : Subgroup Y) (α : MulAut Y)
    (h : ∀ x ∈ F, α x ∈ F) : ∀ x, x ∈ F ↔ α x ∈ F := by
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : F → F := fun y => ⟨α y, h y y.2⟩
  have hinj : Function.Injective f := fun y y' hyy =>
    Subtype.ext (α.injective (congrArg Subtype.val hyy))
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj ⟨α x, hx⟩
  have : α (y : Y) = α x := congrArg Subtype.val hy
  have hyx : (y : Y) = x := α.injective this
  rw [← hyx]
  exact y.2

@[expose] def autStab {Y : Type*} [Group Y] (F : Subgroup Y) : Subgroup (MulAut Y) where
  carrier := {α | ∀ x, x ∈ F ↔ α x ∈ F}
  mul_mem' := fun {a b} ha hb x => (hb x).trans (ha (b x))
  one_mem' := fun x => Iff.rfl
  inv_mem' := fun {a} ha x => by
    have := ha (a⁻¹ x)
    rw [MulAut.apply_inv_self] at this
    exact this.symm


section

variable {F : Subgroup (Carrier .M22)} (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
include hF

theorem betaAut_maps_F {x : Carrier .M22} (hx : x ∈ F) : betaAut x ∈ F := by
  rcases (hF x).1 hx with rfl | hx
  · rw [map_one]
    exact F.one_mem
  · have h1 : tab x ∈ elemTabs 1 := by
      rw [← tab_invs16]
      exact List.mem_map_of_mem hx
    have h2 := (s0Check_spec).2.2.2.1 betaTab (List.mem_cons_self ..)
    unfold normOK at h2
    simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
    obtain ⟨y', hy', hxy⟩ := h2 _ h1
    rw [← tab_invs16] at hy'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hy'
    have := (autTab_conj_iff betaAut x y).1 (by rw [autTab_betaAut]; exact hxy)
    rw [this, hF]
    exact Or.inr hy

theorem s0_normal : ∀ α ∈ s0, ∀ x, x ∈ F ↔ α x ∈ F := by
  have hle : s0 ≤ autStab F := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rcases List.mem_cons.1 hg with rfl | hg
    · exact mem_iff_of_maps F _ fun x hx => betaAut_maps_F hF hx
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      intro x
      have hnorm : normOK (elemTabs 1) (tab g') = true := by
        refine (s0Check_spec).2.2.2.1 _ ?_
        have : tab g' ∈ gensTab := by
          rw [← tab_sylowGens]
          exact List.mem_map_of_mem hg'
        exact List.mem_cons_of_mem _ this
      have := normalizes_of_normOK hF hnorm x
      rw [this]
      simp [MulAut.conj_apply]
  exact fun α hα => hle hα

end

@[expose] def x8Elt : Carrier .M22 := (invs16 1).getD 0 1

theorem x8Elt_mem : x8Elt ∈ invs16 1 := by
  have h : 0 < (invs16 1).length := by rw [(invs16_spec 1).1]; norm_num
  rw [x8Elt, List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem tab_x8Elt : tab x8Elt = x8Tab := by
  rw [x8Elt, tab_getD, tab_invs16, x8Tab]

theorem nodup_f1Tabs : f1Tabs.Nodup := by
  obtain ⟨-, hnd, hall⟩ := of_decide_eq_true (invsOK_elemTabs 1)
  exact List.nodup_cons.2 ⟨fun h => (hall _ h).1 rfl, hnd⟩

section

variable {F : Subgroup (Carrier .M22)} (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
include hF

theorem s0_orbit8 : ∃ x ∈ F, x ≠ 1 ∧ (autOrbit s0 x).ncard = 8 := by
  have hx8F : x8Elt ∈ F := (hF _).2 (Or.inr x8Elt_mem)
  refine ⟨x8Elt, hx8F, ((invs16_spec 1).2.2 _ x8Elt_mem).1, ?_⟩
  have hset : autOrbit s0 x8Elt = {y | tab y ∈ orbitTabs s0Tabs f1Tabs x8Tab} := by
    ext y
    simp only [Set.mem_ofPred_eq, orbitTabs, List.mem_filter, List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨?_, autTab α, (mem_s0_iff α).1 hα, ?_⟩
      · have hy : α x8Elt ∈ F := (s0_normal hF α hα x8Elt).1 hx8F
        rcases (hF _).1 hy with h | h
        · rw [h, tab_one]
          exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ ?_
          rw [← tab_invs16]
          exact List.mem_map_of_mem h
      · rw [← tab_x8Elt]
        exact (autTab_conj_iff α x8Elt (α x8Elt)).2 rfl
    · rintro ⟨-, a, ha, h⟩
      obtain ⟨α, hα, rfl⟩ := isTabsOf_s0.exists_mem a ha
      rw [← tab_x8Elt] at h
      exact ⟨α, hα, ((autTab_conj_iff α x8Elt y).1 h).symm⟩
  rw [hset, ncard_preimage_mem_tabs tab tab_injective (orbitTabs s0Tabs f1Tabs x8Tab)
    (by unfold orbitTabs; exact nodup_f1Tabs.filter _) ?_]
  · exact (s0Check_spec).2.2.2.2.1
  · intro l hl
    unfold orbitTabs at hl
    rcases List.mem_cons.1 (List.mem_filter.1 hl).1 with rfl | h
    · exact ⟨1, tab_one⟩
    · rw [← tab_invs16] at h
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
      exact ⟨y, rfl⟩

end

end CFSG.EvenSporadicStandard.M22Std
