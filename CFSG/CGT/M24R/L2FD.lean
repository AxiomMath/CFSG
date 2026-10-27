module

public import CFSG.CGT.M24R.L2SubB

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

@[expose] def d8 (i : Fin 3) : N8 := n8 (dWord10 i)

@[expose] def th8 (i : Fin 3) : N8 := n8 (thetaWord10 i)

abbrev D8 : Subgroup N8 := Subgroup.normalizer (B8 : Set N8)

@[expose] def wv {H : Type*} [Group H] (u : Fin 3 → H) (w : List (Fin 3)) : H := (w.map u).prod

theorem wv_nil {H : Type*} [Group H] (u : Fin 3 → H) : wv u [] = 1 := rfl

theorem wv_cons {H : Type*} [Group H] (u : Fin 3 → H) (k : Fin 3) (w : List (Fin 3)) :
    wv u (k :: w) = u k * wv u w := by
  simp [wv]

theorem evT_size (a : Fin 3 → Table) (w : List (Fin 3)) : (evT a w).size = 16 := by
  have key : ∀ (w : List (Fin 3)) (X : Table), X.size = 16 →
      (w.foldl (fun X k => compT 16 X (a k)) X).size = 16 := by
    intro w
    induction w with
    | nil => intro X h; exact h
    | cons l w ih => intro X _; exact ih _ (compT_size _ _)
  exact key w _ idT_size

section Tab


theorem evT_isTab {a : Fin 3 → Table} {u : Fin 3 → N8} (w : List (Fin 3))
    (h : ∀ k ∈ w, IsTab (a k) (u k)) : IsTab (evT a w) (wv u w) := by
  have key : ∀ (w : List (Fin 3)), (∀ k ∈ w, IsTab (a k) (u k)) → ∀ (X : Table) (x : N8),
      IsTab X x → IsTab (w.foldl (fun X k => compT 16 X (a k)) X) (x * wv u w) := by
    intro w
    induction w with
    | nil => intro _ X x hX; simpa [wv_nil] using hX
    | cons k w ih =>
      intro hw X x hX
      rw [List.foldl_cons, wv_cons, ← mul_assoc]
      exact ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')) _ _
        (hX.mul (hw k List.mem_cons_self))
  have := key w h (idT 16) 1 IsTab.one
  rwa [one_mul] at this

theorem isTab_dT (i : Fin 3) : IsTab (dT i) (d8 i) := isTab_wTab _

theorem isTab_thT (i : Fin 3) : IsTab (thT i) (th8 i) := isTab_wTab _

variable (hcard : Nat.card N8 = 322560)
include hcard

omit hcard in
theorem dCheck_spec : (∀ i : Fin 3, normB (dT i) = true ∧ normB (thT i) = true) ∧
    (∀ z ∈ (mkCtx ()).dList, commT ((mkCtx ()).tab z) (dT 0) = false ∨
      commT ((mkCtx ()).tab z) (dT 1) = false ∨ commT ((mkCtx ()).tab z) (dT 2) = false ∨
      ((mkCtx ()).tab z == idT 16) = true) ∧
    ∀ i : Fin 3, (evT dT (thWord i) == thT i) = true ∧ (evT thT (thWord i) == dT i) = true := by
  have h := Certificates.certificate21193.2.2.2.2.2.2.2.1
  simp only [dCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun z hz => ?_, h3⟩
  rcases h2 z hz with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem d8_mem (i : Fin 3) : d8 i ∈ D8 := (normB_iff hcard (isTab_dT i)).1 (dCheck_spec.1 i).1

theorem th8_mem (i : Fin 3) : th8 i ∈ D8 := (normB_iff hcard (isTab_thT i)).1 (dCheck_spec.1 i).2

theorem center8 (z : N8) (hz : z ∈ D8) (hc : ∀ i, z * d8 i = d8 i * z) : z = 1 := by
  obtain ⟨c, hc', rfl⟩ := el_of_mem_D hcard hz
  have hX := isTab_tab (mem_codes.1 ((mem_dList_iff hcard).1 hc').1).1
  have hcomm : ∀ i, commT ((mkCtx ()).tab c) (dT i) = true :=
    fun i => (hX.commT_iff hcard (isTab_dT i)).2 (hc i)
  rcases dCheck_spec.2.1 c hc' with h | h | h | h
  · rw [hcomm 0] at h; exact absurd h (by decide)
  · rw [hcomm 1] at h; exact absurd h (by decide)
  · rw [hcomm 2] at h; exact absurd h (by decide)
  · exact (hX.beq_iff hcard IsTab.one (tab_size c) idT_size).1 h

theorem theta_words8 (i : Fin 3) : wv d8 (thWord i) = th8 i ∧ wv th8 (thWord i) = d8 i := by
  obtain ⟨h1, h2⟩ := dCheck_spec.2.2 i
  refine ⟨?_, ?_⟩
  · rw [beq_iff_eq] at h1
    have := evT_isTab (u := d8) (thWord i) (fun k _ => isTab_dT k)
    rw [h1] at this
    exact this.eq_of_eq hcard (isTab_thT i)
  · rw [beq_iff_eq] at h2
    have := evT_isTab (u := th8) (thWord i) (fun k _ => isTab_thT k)
    rw [h2] at this
    exact this.eq_of_eq hcard (isTab_dT i)

end Tab

end CFSG.CGT.M24R
