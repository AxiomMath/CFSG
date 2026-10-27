module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace Classif

variable {Ω : Type*} [DecidableEq Ω]

@[expose] def IsCell (ω : Perm Ω) (E : Subgroup (Perm Ω)) (F : Finset Ω) : Prop :=
  F.card = 4 ∧ (∀ z ∈ F, ω z ∈ F) ∧ (∀ e ∈ E, ∀ z ∈ F, e z ∈ F) ∧
    (∀ e ∈ E, ∀ z, z ∉ F → e z = z ∨ e z = ω z) ∧ ∃ e ∈ E, ∃ z ∈ F, e z ≠ z ∧ e z ≠ ω z

theorem card_four {a b c d : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset Ω).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]),
    Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

section Cells

variable {ω : Perm Ω} {E : Subgroup (Perm Ω)} {F : Finset Ω}

theorem cross_all_of_cross (hωω : ∀ x, ω (ω x) = x) (hmatch : ∀ x, ω x ≠ x) {e : Perm Ω}
    (hcard : F.card = 4) (hωF : ∀ z ∈ F, ω z ∈ F) (heF : ∀ z ∈ F, e z ∈ F)
    (hecomm : ∀ z, ω (e z) = e (ω z)) {z1 : Ω} (hz1 : z1 ∈ F) (hc1 : e z1 ≠ z1)
    (hc2 : e z1 ≠ ω z1) : ∀ z ∈ F, e z ≠ z ∧ e z ≠ ω z := by
  have hωinj : ∀ {x y}, ω x = ω y → x = y := fun {x y} h => by
    have := congrArg ω h
    rwa [hωω, hωω] at this
  obtain ⟨w, hw⟩ : ∃ w, e z1 = w := ⟨_, rfl⟩
  have hwF : w ∈ F := hw ▸ heF z1 hz1
  have hωz1F : ω z1 ∈ F := hωF z1 hz1
  have hωwF : ω w ∈ F := hωF w hwF
  have hcr1 : ω (e z1) = e (ω z1) := hecomm z1
  have h1 : e (ω z1) = ω w := by rw [← hcr1, hw]
  have hwz1 : w ≠ z1 := hw ▸ hc1
  have hwωz1 : w ≠ ω z1 := hw ▸ hc2
  have hωwz1 : ω w ≠ z1 := fun h' => hwωz1 (by rw [← h', hωω])
  have hωwωz1 : ω w ≠ ω z1 := fun h' => hwz1 (hωinj h')
  have hFeq : F = {z1, ω z1, w, ω w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption
    · rw [hcard, card_four (Ne.symm (hmatch z1)) hwz1.symm hωwz1.symm hwωz1.symm
        hωwωz1.symm (hmatch w).symm]
  have hew : e w ≠ w := by
    intro h'
    exact hwz1 (e.injective (h'.trans hw.symm))
  have hewω : e w ≠ ω w := by
    intro h'
    have h2 : e (ω w) = w := by rw [← hecomm w, h', hωω]
    exact hωwz1 (e.injective (h2.trans hw.symm))
  intro z hz
  rw [hFeq] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨hc1, hc2⟩
  · rw [h1]
    exact ⟨fun h' => hωwωz1 h', fun h' => hωwz1 (by rw [h', hωω])⟩
  · exact ⟨hew, hewω⟩
  · rw [← hecomm w]
    exact ⟨fun h' => hew (hωinj h'), fun h' => hewω (hωinj h')⟩

theorem cell_cross_all (hωω : ∀ x, ω (ω x) = x) (hmatch : ∀ x, ω x ≠ x)
    (hEcomm : ∀ e ∈ E, ∀ z, ω (e z) = e (ω z)) (h : IsCell ω E F) :
    ∃ e ∈ E, ∀ z ∈ F, e z ≠ z ∧ e z ≠ ω z := by
  obtain ⟨hcard, hωF, hEF, hoff, e, he, z1, hz1, hc1, hc2⟩ := h
  exact ⟨e, he, cross_all_of_cross hωω hmatch hcard hωF (hEF e he) (hEcomm e he) hz1 hc1 hc2⟩

theorem cell_eq_of_mem (hωω : ∀ x, ω (ω x) = x) (hmatch : ∀ x, ω x ≠ x)
    {e : Perm Ω} (hcard : F.card = 4) (hωF : ∀ z ∈ F, ω z ∈ F) (heF : ∀ z ∈ F, e z ∈ F)
    (hcr : ∀ z ∈ F, e z ≠ z ∧ e z ≠ ω z) {x : Ω} (hx : x ∈ F) :
    F = {x, ω x, e x, ω (e x)} := by
  have hωinj : ∀ {x y}, ω x = ω y → x = y := fun {x y} h => by
    have := congrArg ω h
    rwa [hωω, hωω] at this
  have hc := hcr x hx
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hx
    · exact hωF _ hx
    · exact heF _ hx
    · exact hωF _ (heF _ hx)
  · rw [hcard, card_four (hmatch x).symm hc.1.symm
      (fun h => hc.2 (by have := congrArg ω h; rw [hωω] at this; exact this.symm)) (fun h => hc.2 h.symm)
      (fun h => hc.1 (hωinj h).symm) (hmatch (e x)).symm]

theorem cell_swap_blocks (hωω : ∀ x, ω (ω x) = x) {e : Perm Ω} {x y : Ω} (hy : e x = y)
    (hF : F = {x, ω x, y, ω y}) (heF : ∀ z ∈ F, e z ∈ F)
    (hcr : ∀ z ∈ F, e z ≠ z ∧ e z ≠ ω z) :
    ∀ a, (a = y ∨ a = ω y) → (e a = x ∨ e a = ω x) := by
  subst hy
  intro a ha
  have haF : a ∈ F := by
    rw [hF]; rcases ha with rfl | rfl <;> simp
  have h1 := heF a haF
  have h2 := hcr a haF
  rw [hF] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases ha with rfl | rfl
  · rcases h1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h2.1
    · exact absurd h h2.2
  · rcases h1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (by
        intro h'; apply h2.2; rw [hωω]; exact h')
    · exact absurd h h2.1

theorem inv_mem_of_forall_mem {g : Perm Ω} (hgF : ∀ z ∈ F, g z ∈ F) {z : Ω} (hz : z ∈ F) :
    g⁻¹ z ∈ F := by
  have hsub : F.image g ⊆ F := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ht
    exact hgF y hy
  have heq : F.image g = F :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ g.injective])
  have : z ∈ F.image g := by rw [heq]; exact hz
  obtain ⟨y, hy, hyz⟩ := Finset.mem_image.1 this
  have : g⁻¹ z = y := by rw [← hyz]; simp
  rw [this]; exact hy

theorem blockTrivial_of_two_cross (hωω : ∀ x, ω (ω x) = x) (hmatch : ∀ x, ω x ≠ x)
    {g1 g2 : Perm Ω} (hcard : F.card = 4) (hωF : ∀ z ∈ F, ω z ∈ F)
    (hg1F : ∀ z ∈ F, g1 z ∈ F) (hg2F : ∀ z ∈ F, g2 z ∈ F)
    (hcr1 : ∀ z ∈ F, g1 z ≠ z ∧ g1 z ≠ ω z) (hcr2 : ∀ z ∈ F, g2 z ≠ z ∧ g2 z ≠ ω z) :
    ∀ y ∈ F, g2⁻¹ (g1 y) = y ∨ g2⁻¹ (g1 y) = ω y := by
  intro y hy
  have hF := cell_eq_of_mem hωω hmatch hcard hωF hg1F hcr1 hy
  have hv : g2⁻¹ (g1 y) ∈ F := inv_mem_of_forall_mem hg2F (hg1F y hy)
  have hgv : g2 (g2⁻¹ (g1 y)) = g1 y := by simp
  obtain ⟨v, hvdef⟩ : ∃ v, g2⁻¹ (g1 y) = v := ⟨_, rfl⟩
  rw [hvdef] at hv hgv ⊢
  have hv' := hv
  rw [hF] at hv'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
  rcases hv' with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    exact (hcr2 v hv).1 (by rw [hgv, h])
  · exfalso
    exact (hcr2 v hv).2 (by rw [hgv, h, hωω])

variable {W : Subgroup (Perm Ω)}

theorem cells_eq_or_disjoint (hW : IsPGroup 2 W) (hωω : ∀ x, ω (ω x) = x) (hmatch : ∀ x, ω x ≠ x)
    (hcomm : ∀ w ∈ W, ∀ z, ω (w z) = w (ω z)) (hsw : ∀ z, swap z (ω z) ∈ W)
    {E₁ E₂ : Subgroup (Perm Ω)} (hE₁ : E₁ ≤ W) (hE₂ : E₂ ≤ W) {F₁ F₂ : Finset Ω}
    (c₁ : IsCell ω E₁ F₁) (c₂ : IsCell ω E₂ F₂) : F₁ = F₂ ∨ Disjoint F₁ F₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hnd⟩ := hcon
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨x, hx1, hx2⟩ := hnd
  have hωinj : ∀ {x y}, ω x = ω y → x = y := fun {x y} h => by
    have := congrArg ω h
    rwa [hωω, hωω] at this
  obtain ⟨e1, he1, hcr1⟩ := cell_cross_all hωω hmatch (fun e he => hcomm e (hE₁ he)) c₁
  obtain ⟨e2, he2, hcr2⟩ := cell_cross_all hωω hmatch (fun e he => hcomm e (hE₂ he)) c₂
  obtain ⟨hcard1, hωF1, hEF1, hoff1, -⟩ := c₁
  obtain ⟨hcard2, hωF2, hEF2, hoff2, -⟩ := c₂
  have hF1 := cell_eq_of_mem hωω hmatch hcard1 hωF1 (hEF1 e1 he1) hcr1 hx1
  have hF2 := cell_eq_of_mem hωω hmatch hcard2 hωF2 (hEF2 e2 he2) hcr2 hx2
  obtain ⟨y1, hy1⟩ : ∃ y1, e1 x = y1 := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y2, e2 x = y2 := ⟨_, rfl⟩
  rw [hy1] at hF1
  rw [hy2] at hF2
  have hc1 := hcr1 x hx1
  have hc2 := hcr2 x hx2
  rw [hy1] at hc1
  rw [hy2] at hc2
  have hny : ¬ (y1 = y2 ∨ y1 = ω y2) := by
    intro h
    apply hne
    rw [hF1, hF2]
    rcases h with rfl | rfl
    · rfl
    · ext t
      simp only [Finset.mem_insert, Finset.mem_singleton, hωω]
      tauto
  push Not at hny
  obtain ⟨hn1, hn2⟩ := hny
  have hn3 : ω y1 ≠ y2 := fun h => hn2 (by rw [← h, hωω])
  have hn4 : ω y1 ≠ ω y2 := fun h => hn1 (hωinj h)
  have hy2F1 : y2 ∉ F₁ := by
    rw [hF1]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hc2.1, hc2.2, hn1.symm, hn3.symm⟩
  have hωy2F1 : ω y2 ∉ F₁ := fun h => hy2F1 (by simpa [hωω] using hωF1 _ h)
  have hy1F2 : y1 ∉ F₂ := by
    rw [hF2]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hc1.1, hc1.2, hn1, hn2⟩
  have hωy1F2 : ω y1 ∉ F₂ := fun h => hy1F2 (by simpa [hωω] using hωF2 _ h)
  have hg : e1 * e2 ∈ W := W.mul_mem (hE₁ he1) (hE₂ he2)
  have hgc : ∀ z, ω ((e1 * e2) z) = (e1 * e2) (ω z) := fun z => hcomm _ hg z
  have hsw1 : ∀ a, (a = y1 ∨ a = ω y1) → (e1 a = x ∨ e1 a = ω x) :=
    cell_swap_blocks hωω hy1 hF1 (hEF1 e1 he1) hcr1
  have hsw2 : ∀ a, (a = y2 ∨ a = ω y2) → (e2 a = x ∨ e2 a = ω x) :=
    cell_swap_blocks hωω hy2 hF2 (hEF2 e2 he2) hcr2
  have hfwd1 : ∀ u, (u = x ∨ u = ω x) → (e1 u = y1 ∨ e1 u = ω y1) := by
    intro u hu
    rcases hu with rfl | rfl
    · exact Or.inl hy1
    · exact Or.inr (by rw [← hcomm e1 (hE₁ he1) x, hy1])
  have hfwd2 : ∀ u, (u = x ∨ u = ω x) → (e2 u = y2 ∨ e2 u = ω y2) := by
    intro u hu
    rcases hu with rfl | rfl
    · exact Or.inl hy2
    · exact Or.inr (by rw [← hcomm e2 (hE₂ he2) x, hy2])
  obtain ⟨a1, ha1⟩ : ∃ a1, (e1 * e2) x = a1 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2, (e1 * e2) a1 = a2 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a3, (e1 * e2) a2 = a3 := ⟨_, rfl⟩
  have hA1 : a1 = y2 ∨ a1 = ω y2 := by
    rw [← ha1, Perm.mul_apply, hy2]
    rcases hoff1 e1 he1 y2 hy2F1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hA2 : a2 = y1 ∨ a2 = ω y1 := by
    rw [← ha2, Perm.mul_apply]
    exact hfwd1 _ (hsw2 a1 hA1)
  have hA3 : a3 = x ∨ a3 = ω x := by
    rw [← ha3, Perm.mul_apply]
    apply hsw1
    have hy2' : a2 ∉ F₂ := by
      rcases hA2 with rfl | rfl
      · exact hy1F2
      · exact hωy1F2
    rcases hoff2 e2 he2 a2 hy2' with h | h
    · rw [h]; exact hA2
    · rw [h]
      rcases hA2 with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (hωω _)
  have hax2 : ∀ a, (a = y2 ∨ a = ω y2) → a ≠ x ∧ a ≠ ω x := by
    intro a ha
    rcases ha with rfl | rfl
    · exact hc2
    · refine ⟨fun h => hc2.2 ?_, fun h => hc2.1 ?_⟩
      · have := congrArg ω h; rwa [hωω] at this
      · exact hωinj h
  have hax1 : ∀ a, (a = y1 ∨ a = ω y1) → a ≠ x ∧ a ≠ ω x := by
    intro a ha
    rcases ha with rfl | rfl
    · exact hc1
    · refine ⟨fun h => hc1.2 ?_, fun h => hc1.1 ?_⟩
      · have := congrArg ω h; rwa [hωω] at this
      · exact hωinj h
  have hab : ∀ a b, (a = y2 ∨ a = ω y2) → (b = y1 ∨ b = ω y1) → a ≠ b := by
    intro a b ha hb h
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hn1 (ha.symm.trans (h.trans hb)).symm
    · exact hn3 (ha.symm.trans (h.trans hb)).symm
    · exact hn2 (ha.symm.trans (h.trans hb)).symm
    · exact hn4 (ha.symm.trans (h.trans hb)).symm
  have hω2 : ∀ a, (a = y2 ∨ a = ω y2) → (ω a = y2 ∨ ω a = ω y2) := by
    intro a ha
    rcases ha with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (hωω _)
  have hω1 : ∀ a, (a = y1 ∨ a = ω y1) → (ω a = y1 ∨ ω a = ω y1) := by
    intro a ha
    rcases ha with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (hωω _)
  rcases hA3 with h3 | h3
  ·
    refine not_isPGroup_of_threeCycle hW hg (a := x) (b := a1) (c := a2) ?_ ?_ ?_ ha1 ha2
      (by rw [ha3, h3])
    · exact (hax2 a1 hA1).1.symm
    · exact hab a1 a2 hA1 hA2
    · exact (hax1 a2 hA2).1
  · have hg' : e1 * e2 * swap x (ω x) ∈ W := W.mul_mem hg (hsw x)
    have hsx : ∀ t, t ≠ x → t ≠ ω x → swap x (ω x) t = t := fun t h1 h2 =>
      swap_apply_of_ne_of_ne h1 h2
    refine not_isPGroup_of_threeCycle hW hg' (a := x) (b := ω a1) (c := ω a2) ?_ ?_ ?_ ?_ ?_ ?_
    · exact ((hax2 _ (hω2 a1 hA1)).1).symm
    · exact hab _ _ (hω2 a1 hA1) (hω1 a2 hA2)
    · exact (hax1 _ (hω1 a2 hA2)).1
    · rw [Perm.mul_apply, swap_apply_left, ← hgc x, ha1]
    · rw [Perm.mul_apply, hsx _ (hax2 _ (hω2 a1 hA1)).1 (hax2 _ (hω2 a1 hA1)).2, ← hgc a1, ha2]
    · rw [Perm.mul_apply, hsx _ (hax1 _ (hω1 a2 hA2)).1 (hax1 _ (hω1 a2 hA2)).2, ← hgc a2, ha3,
        h3, hωω]

end Cells

end Classif

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
