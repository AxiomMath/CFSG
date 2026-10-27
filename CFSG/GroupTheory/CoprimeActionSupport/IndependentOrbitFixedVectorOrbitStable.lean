module


public import CFSG.GroupTheory.CoprimeActionSupport.IndependentSummandFixedVectorSupportStable

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitFixedVectorOrbitStable

open CFSG.GroupTheory.CoprimeActionSupport.IndependentSummandFixedVectorSupportStable

theorem orbit_stable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {H : Type*} [Group H] {I : Type*} [Finite I] [MulAction H I]
    (U : I → Submodule F V) (hU : iSupIndep U)
    (ρ : Representation F H V) (hperm : ∀ (h : H) (i : I), (U i).map (ρ h) = U (h • i))
    (S B : Subgroup H) (i : I) (w : V) (hw0 : w ≠ 0)
    (hw : w ∈ ⨆ s : S, U (s.val • i))
    (hS : ∀ s : S, ρ s.val w = w) (hB : ∀ b : B, ρ b.val w = w) :
    ∀ b : B, ∀ s : S, ∃ t : S, b.val • (s.val • i) = t.val • i := by
  have decompose [Fintype I] (U : I → Submodule F V) (O : Set I) (v : V)
      (hv : v ∈ ⨆ j ∈ O, U j) :
      ∃ w : I → V, (∀ j, w j ∈ U j) ∧ (∀ j, j ∉ O → w j = 0) ∧ ∑ j, w j = v := by
    classical
    induction hv using Submodule.iSup_induction' with
    | mem j x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hj x hx =>
        refine ⟨fun k => if k = j then x else 0, ?_, ?_, ?_⟩
        · intro k; by_cases h : k = j
          · subst h; simpa using hx
          · simp [h]
        · intro k hk; have : k ≠ j := fun h => hk (h ▸ hj)
          simp [this]
        · simp
      | zero => exact ⟨0, fun j => zero_mem _, fun _ _ => rfl, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha1, ha2, ha3⟩ := hx
        obtain ⟨b, hb1, hb2, hb3⟩ := hy
        exact ⟨a + b, fun j => add_mem (ha1 j) (hb1 j), fun j hj => by simp [ha2 j hj, hb2 j hj],
          by simp [Finset.sum_add_distrib, ha3, hb3]⟩
    | zero => exact ⟨0, fun j => zero_mem _, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha1, ha2, ha3⟩ := hx
      obtain ⟨b, hb1, hb2, hb3⟩ := hy
      exact ⟨a + b, fun j => add_mem (ha1 j) (hb1 j), fun j hj => by simp [ha2 j hj, hb2 j hj],
        by simp [Finset.sum_add_distrib, ha3, hb3]⟩
  classical
  have := Fintype.ofFinite I
  set O : Set I := Set.range (fun s : S => s.val • i) with hO
  have hw' : w ∈ ⨆ j ∈ O, U j := by
    have hle : (⨆ s : S, U (s.val • i)) ≤ ⨆ j ∈ O, U j :=
      iSup_le fun s => le_iSup₂_of_le (s.val • i) ⟨s, rfl⟩ le_rfl
    exact hle hw
  obtain ⟨c, hc1, hc2, hc3⟩ := decompose U O w hw'
  obtain ⟨j0, hj0⟩ := support_nonempty (F := F) c w hc3 hw0
  have hj0O : j0 ∈ O := by
    by_contra h; exact hj0 (hc2 j0 h)
  obtain ⟨s0, hs0⟩ := hj0O
  have hall : ∀ s : S, c (s.val • i) ≠ 0 := by
    intro s
    have hs' : (s * s0⁻¹ : S).val • j0 = s.val • i := by
      rw [← hs0]; simp [mul_smul]
    have := (stable_support U hU ρ hperm S c hc1 w hc3 hS (s * s0⁻¹) j0).1 hj0
    rwa [hs'] at this
  intro b s
  have h1 := (stable_support U hU ρ hperm B c hc1 w hc3 hB b (s.val • i)).1 (hall s)
  by_contra hcon
  push Not at hcon
  exact h1 (hc2 _ (fun ⟨t, ht⟩ => hcon t ht.symm))

end CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitFixedVectorOrbitStable
