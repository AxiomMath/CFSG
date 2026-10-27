module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std.TabMap

open CFSG.EvenSporadicStandard.M22Std.TabCheck

variable {G : Type*} [Group G] (τ : TabMap G)

theorem isTabsOf_closure_of_mem [Finite G] (gs : List G) (L : List Tab) (hid : idTab ∈ L)
    (hcl : ∀ l ∈ L, ∀ g ∈ gs, tmul l (τ.tb g) ∈ L)
    (hgen : ∀ l ∈ L, ∃ x ∈ Subgroup.closure {g | g ∈ gs}, τ.tb x = l) :
    τ.IsTabsOf (Subgroup.closure {g | g ∈ gs}) L := by
  refine ⟨fun x hx => ?_, hgen⟩
  have hx' : x ∈ Submonoid.closure {g | g ∈ gs} := by
    rw [← Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x _ => isOfFinOrder_of_finite x)]
    exact hx
  have key : ∀ y ∈ Submonoid.closure {g | g ∈ gs}, ∀ l : G, τ.tb l ∈ L → τ.tb (l * y) ∈ L := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      intro l hl
      rw [τ.mul]
      exact hcl _ hl _ hy
    | one => intro l hl; rwa [mul_one]
    | mul y z _ _ hy hz => intro l hl; rw [← mul_assoc]; exact hz _ (hy l hl)
  have h1 : τ.tb (1 * x) ∈ L := key x hx' 1 (by rw [τ.one]; exact hid)
  rwa [one_mul] at h1

end CFSG.EvenSporadicStandard.M22Std.TabMap

namespace CFSG.EvenSporadicStandard.M22Std.HS08H

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check CFSG.EvenSporadicStandard.M22Std.HS08Check
  CFSG.Blueprint.NativeSporadic

theorem wordElt_mem_of_forall {G : Type*} [Group G] (H : Subgroup G) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ H) (w : List Nat) : wordElt gs w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih =>
    refine H.mul_mem ?_ ih
    rcases lt_or_ge i gs.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hgs _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      exact H.one_mem

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] (J : Subgroup G) [Finite J] (g : G)
    (h : ∀ x ∈ J, g * x * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  let f : J → J := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hinj : Function.Injective f := fun y y' hyy => by
    have := congrArg Subtype.val hyy
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj ⟨g * n * g⁻¹, hn⟩
  have h1 : g * (y : G) * g⁻¹ = g * n * g⁻¹ := congrArg Subtype.val hy
  simp only [mul_left_inj, mul_right_inj] at h1
  rw [← h1]
  exact y.2

theorem mulAut_mul_conj_mul_inv {Y : Type*} [Group Y] (α : MulAut Y) (z : Y) :
    α * MulAut.conj z * α⁻¹ = MulAut.conj (α z) := by
  ext y
  simp [MulAut.conj_apply]

theorem mem_innerImage_top_iff {Y : Type*} [Group Y] (α : MulAut Y) :
    α ∈ innerImage Y ⊤ ↔ ∃ z : Y, MulAut.conj z = α := by
  simp only [innerImage, Subgroup.mem_map, Subgroup.mem_top, true_and]

theorem conj_mem_innerImage_iff {Y : Type*} [Group Y] (g α : MulAut Y) :
    g * α * g⁻¹ ∈ innerImage Y ⊤ ↔ α ∈ innerImage Y ⊤ := by
  have key : ∀ (g α : MulAut Y), α ∈ innerImage Y ⊤ → g * α * g⁻¹ ∈ innerImage Y ⊤ := by
    intro g α hα
    obtain ⟨z, rfl⟩ := (mem_innerImage_top_iff α).1 hα
    rw [mulAut_mul_conj_mul_inv]
    exact (mem_innerImage_top_iff _).2 ⟨_, rfl⟩
  refine ⟨fun h => ?_, key g α⟩
  have := key g⁻¹ _ h
  simpa [mul_assoc] using this

section


@[expose] noncomputable def autLetters : List (MulAut (Carrier .M22)) :=
  [MulAut.conj genA, MulAut.conj genB, MulAut.conj genBi, betaAut]

theorem map_autTab_autLetters : autLetters.map autTab = letterTabs4 := by
  simp only [autLetters, List.map_cons, List.map_nil, autTab_conj, tab_genA, tab_genB, tab_genBi,
    autTab_betaAut, letterTabs4]

theorem autTab_wordElt (ls : List (MulAut (Carrier .M22))) (w : List Nat) :
    autTab (wordElt ls w) = wordTab (ls.map autTab) w := by
  induction w with
  | nil => simp only [wordElt, wordTab, autTab_one]
  | cons i w ih =>
    have h : (ls.map autTab).getD i idTab = autTab (ls.getD i 1) := by
      rw [← autTab_one, List.getD_map]
    simp only [wordElt, wordTab, autTab_mul, ih, h]

theorem autTab_wordElt_letters (w : List Nat) :
    autTab (wordElt autLetters w) = wordTab letterTabs4 w := by
  rw [autTab_wordElt, map_autTab_autLetters]

theorem conj_eq_of_tmul {α β γ : MulAut (Carrier .M22)}
    (h : tmul (autTab α) (autTab β) = tmul (autTab γ) (autTab α)) : α * β * α⁻¹ = γ := by
  rw [mul_inv_eq_iff_eq_mul]
  exact autTab_injective (by rw [autTab_mul, autTab_mul]; exact h)

theorem exists_mem_jSub {l : Tab} (hl : l ∈ jTabs) : ∃ x ∈ jSub, autTab x = l := by
  obtain ⟨x, -, hx⟩ := isTabsOf_s0.exists_mem l (jTabs_prop l hl).1
  have hx' : autTab x = l := hx
  exact ⟨x, mem_jSub.2 (hx' ▸ hl), hx'⟩

theorem exists_tab_of_mem_s0Inner {l : Tab} (hl : l ∈ s0Inner) : ∃ z : Carrier .M22, tab z = l := by
  rw [s0Inner, ← tab_sylowGens, ← tab_spanE] at hl
  obtain ⟨z, -, hz⟩ := List.mem_map.1 hl
  exact ⟨z, hz⟩

theorem inner_iff_of_mem_s0 {α : MulAut (Carrier .M22)} (hα : α ∈ s0) :
    α ∈ innerImage (Carrier .M22) ⊤ ↔ autTab α ∈ s0Inner := by
  constructor
  · intro hin
    have hs : autTab α ∈ s0Inner ++ s0Outer := by
      rw [← s0Tabs_eq]
      exact (mem_s0_iff α).1 hα
    rcases List.mem_append.1 hs with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, hls⟩ := List.mem_map.1 h
      obtain ⟨z, hz⟩ := exists_tab_of_mem_s0Inner hl
      have hs : α = betaAut * MulAut.conj z :=
        autTab_injective (by rw [autTab_mul, autTab_betaAut, autTab_conj, hz, ← hls])
      apply betaAut_not_inner
      have : betaAut = α * (MulAut.conj z)⁻¹ := by rw [hs]; group
      rw [this]
      exact Subgroup.mul_mem _ hin (Subgroup.inv_mem _ ⟨z, Subgroup.mem_top _, rfl⟩)
  · intro h
    obtain ⟨z, hz⟩ := exists_tab_of_mem_s0Inner h
    have : α = MulAut.conj z := autTab_injective (by rw [autTab_conj, hz])
    rw [this]
    exact ⟨z, Subgroup.mem_top _, rfl⟩

theorem outer_iff_of_mem_s0 {α : MulAut (Carrier .M22)} (hα : α ∈ s0) :
    α ∉ innerImage (Carrier .M22) ⊤ ↔ autTab α ∈ s0Outer := by
  have hnd := (s0Check_spec).1.2.1
  rw [s0Tabs_eq] at hnd
  have hs : autTab α ∈ s0Inner ++ s0Outer := by
    rw [← s0Tabs_eq]
    exact (mem_s0_iff α).1 hα
  rw [inner_iff_of_mem_s0 hα]
  constructor
  · intro h
    exact (List.mem_append.1 hs).resolve_left h
  · intro h hin
    exact (List.nodup_append.1 hnd).2.2 _ hin _ h rfl

theorem autTab_mem_jInn_iff (α : MulAut (Carrier .M22)) :
    autTab α ∈ jInn ↔ α ∈ jSub ∧ α ∈ innerImage (Carrier .M22) ⊤ := by
  simp only [jInn, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mem_jSub.2 h1, (inner_iff_of_mem_s0 (jSub_le (mem_jSub.2 h1))).2 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_jSub.1 h1, (inner_iff_of_mem_s0 (jSub_le h1)).1 h2⟩

theorem autTab_mem_jOut_iff (α : MulAut (Carrier .M22)) :
    autTab α ∈ jOut ↔ α ∈ jSub ∧ α ∉ innerImage (Carrier .M22) ⊤ := by
  simp only [jOut, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mem_jSub.2 h1, (outer_iff_of_mem_s0 (jSub_le (mem_jSub.2 h1))).2 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_jSub.1 h1, (outer_iff_of_mem_s0 (jSub_le h1)).1 h2⟩

end

end CFSG.EvenSporadicStandard.M22Std.HS08H
