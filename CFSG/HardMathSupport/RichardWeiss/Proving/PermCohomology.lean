module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def vecAct (σ : Perm α) (z : α → ZMod 2) : α → ZMod 2 := fun i => z (σ.symm i)

omit [Fintype α] [DecidableEq α] in
theorem vecAct_apply (σ : Perm α) (z : α → ZMod 2) (i : α) :
    vecAct σ z i = z (σ.symm i) := rfl

section Cocycle

variable (f : alternatingGroup (α) → (α → ZMod 2))
  (hf : ∀ g h, f (g * h) = f g + vecAct (g : Equiv.Perm (α)) (f h))
include hf

theorem cocycle_one : f 1 = 0 := by
  have h := hf 1 1
  simp only [mul_one] at h
  have h2 : vecAct ((1 : alternatingGroup (α)) : Equiv.Perm (α)) (f 1) = f 1 := by
    funext i; rfl
  rw [h2] at h
  simpa using h

theorem cocycle_mul_apply_fix (a : α) (g h : alternatingGroup (α))
    (hg : (g : Perm (α)) a = a) : f (g * h) a = f g a + f h a := by
  have := congrFun (hf g h) a
  simp only [Pi.add_apply, vecAct_apply] at this
  have hs : (g : Perm (α)).symm a = a := (Equiv.symm_apply_eq _).2 hg.symm
  rw [hs] at this
  exact this

theorem cocycle_stab_zero (a : α) (g : alternatingGroup (α))
    (hga : (g : Perm (α)) a = a) : f g a = 0 := by
  classical
  have h0 := cocycle_one f hf
  let P : Perm {x : α // x ≠ a} → Prop := fun σ =>
    ∃ g : alternatingGroup (α), (g : Perm (α)) = Perm.ofSubtype σ ∧ f g a = 0
  have hfixa : ∀ σ : Perm {x : α // x ≠ a}, (Perm.ofSubtype σ) a = a := fun σ =>
    Perm.ofSubtype_apply_of_not_mem σ (by simp)
  have key : ∀ σ ∈ Subgroup.closure {c : Perm {x : α // x ≠ a} | c.IsThreeCycle}, P σ := by
    intro σ hσ
    refine Subgroup.closure_induction (p := fun σ _ => P σ) ?_ ?_ ?_ ?_ hσ
    · intro c hc
      have hsign : Perm.sign (Perm.ofSubtype c) = 1 := by
        rw [Perm.sign_ofSubtype]; exact hc.sign
      have hmem : Perm.ofSubtype c ∈ alternatingGroup (α) := mem_alternatingGroup.2 hsign
      refine ⟨⟨Perm.ofSubtype c, hmem⟩, rfl, ?_⟩
      set g : alternatingGroup (α) := ⟨Perm.ofSubtype c, hmem⟩ with hg
      have hga' : (g : Perm (α)) a = a := hfixa c
      have hg3 : g * g * g = 1 := by
        apply Subtype.ext
        change Perm.ofSubtype c * Perm.ofSubtype c * Perm.ofSubtype c = 1
        have h3 : c ^ 3 = 1 := by rw [← hc.orderOf]; exact pow_orderOf_eq_one c
        have := congrArg (Perm.ofSubtype (p := fun x : α => x ≠ a)) h3
        rw [map_pow, map_one] at this
        simpa [pow_succ, mul_assoc] using this
      have hgg : ((g * g : alternatingGroup (α)) : Perm (α)) a = a := by
        change (g : Perm (α)) ((g : Perm (α)) a) = a
        rw [hga', hga']
      have e1 := cocycle_mul_apply_fix f hf a g g hga'
      have e2 := cocycle_mul_apply_fix f hf a (g * g) g hgg
      rw [hg3] at e2
      rw [e1] at e2
      have h1 : f (1 : alternatingGroup (α)) a = 0 := by rw [h0]; rfl
      rw [h1] at e2
      have hx : ∀ x : ZMod 2, x + x + x = 0 → x = 0 := by decide
      exact hx _ e2.symm
    · refine ⟨1, ?_, ?_⟩
      · simp
      · rw [h0]; rfl
    · rintro x y - - ⟨g₁, hg₁, hx₁⟩ ⟨g₂, hg₂, hx₂⟩
      refine ⟨g₁ * g₂, ?_, ?_⟩
      · change (g₁ : Perm (α)) * (g₂ : Perm (α)) = _
        rw [hg₁, hg₂, map_mul]
      · rw [cocycle_mul_apply_fix f hf a g₁ g₂ (by rw [hg₁]; exact hfixa x), hx₁, hx₂]; rfl
    · rintro x - ⟨g₁, hg₁, hx₁⟩
      refine ⟨g₁⁻¹, ?_, ?_⟩
      · change ((g₁ : Perm (α)))⁻¹ = _
        rw [hg₁, map_inv]
      · have hfix : (g₁ : Perm (α)) a = a := by rw [hg₁]; exact hfixa x
        have e := cocycle_mul_apply_fix f hf a g₁ g₁⁻¹ hfix
        rw [mul_inv_cancel, h0] at e
        have h1 : (0 : α → ZMod 2) a = 0 := rfl
        rw [h1, hx₁] at e
        simpa using e.symm
  have h₁ : ∀ x : α, (fun y => y ≠ a) ((g : Perm (α)) x) ↔ (fun y => y ≠ a) x := by
    intro x
    constructor
    · intro h hx; apply h; rw [hx, hga]
    · intro h hx; apply h; apply (g : Perm (α)).injective; rw [hx, hga]
  have h₂ : ∀ x : α, (g : Perm (α)) x ≠ x → (fun y => y ≠ a) x := by
    intro x hx hxa; apply hx; rw [hxa, hga]
  let σ0 : Perm {x : α // x ≠ a} := (g : Perm (α)).subtypePerm (p := fun y => y ≠ a) h₁
  have hsign : Perm.sign σ0 = 1 := by
    rw [Perm.sign_subtypePerm _ h₁ h₂]; exact mem_alternatingGroup.1 g.2
  have hmem : σ0 ∈ Subgroup.closure {c : Perm {x : α // x ≠ a} | c.IsThreeCycle} := by
    rw [closure_three_cycles_eq_alternating]; exact mem_alternatingGroup.2 hsign
  obtain ⟨g', hg', hz⟩ := key σ0 hmem
  have : g' = g := by
    apply Subtype.ext
    rw [hg']
    exact Perm.ofSubtype_subtypePerm h₁ h₂
  rw [← this]; exact hz

end Cocycle

theorem exists_alt_apply (hm : 3 ≤ Fintype.card α) (a i : α) :
    ∃ r : alternatingGroup (α), (r : Perm (α)) a = i := by
  classical
  by_cases hia : i = a
  · exact ⟨1, by simp [hia]⟩
  · obtain ⟨b, hba, hbi⟩ : ∃ b : α, b ≠ a ∧ b ≠ i := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (α)) ⊆ {a, i} := by
        intro x _
        by_cases hxa : x = a
        · simp [hxa]
        · simp [h x hxa]
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, i} : Finset (α)).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ] at h1
      omega
    have hai : a ≠ i := fun h => hia h.symm
    have hib : i ≠ b := fun h => hbi h.symm
    refine ⟨⟨swap a i * swap i b, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hai, Perm.sign_swap hib]
      decide
    · change (swap a i) ((swap i b) a) = i
      rw [swap_apply_of_ne_of_ne hai hba.symm, swap_apply_left]

theorem cocycle_vec_coboundary (hm : 3 ≤ Fintype.card α)
    (f : alternatingGroup (α) → (α → ZMod 2))
    (hf : ∀ g h, f (g * h) = f g + vecAct (g : Equiv.Perm (α)) (f h)) :
    ∃ w : α → ZMod 2, ∀ g, f g = vecAct (g : Equiv.Perm (α)) w - w := by
  classical
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  choose r hr using fun i => exists_alt_apply hm a i
  refine ⟨fun i => f (r i) i, ?_⟩
  intro g
  funext i
  set j : α := (g : Perm (α)).symm i with hj
  have hgj : (g : Perm (α)) j = i := by rw [hj]; exact Equiv.apply_symm_apply _ _
  have hri : ((r i : Perm (α))⁻¹) i = a := by
    have h := hr i
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    exact h.symm
  have hτ : (((r i)⁻¹ * g * r j : alternatingGroup (α)) : Perm (α)) a = a := by
    change ((r i : Perm (α))⁻¹) ((g : Perm (α)) ((r j : Perm (α)) a)) = a
    rw [hr j, hgj]
    exact hri
  have hτ0 := cocycle_stab_zero f hf a _ hτ
  have e1 : f (g * r j) i = f g i + f (r j) j := by
    have := congrFun (hf g (r j)) i
    simpa [vecAct_apply] using this
  have heq : g * r j = r i * ((r i)⁻¹ * g * r j) := by group
  have e2 : f (g * r j) i = f (r i) i := by
    rw [heq]
    have := congrFun (hf (r i) ((r i)⁻¹ * g * r j)) i
    rw [this]
    have hs : (r i : Perm (α)).symm i = a := by
      have h := hr i
      rw [Equiv.symm_apply_eq]; exact h.symm
    simp only [Pi.add_apply, vecAct_apply, hs, hτ0]
    simp
  have hc : ∀ p x y : ZMod 2, p + x = y → p = x - y := by decide
  have h3 := hc _ _ _ (e1.symm.trans e2)
  simpa [vecAct_apply, hj] using h3

end CFSG.HardMathSupport.RichardWeiss.Proving
