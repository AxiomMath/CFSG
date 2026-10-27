module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def presParamsShort (ws subs : List (List (Fin m × Bool))) (k : ℕ) : Params :=
  { mkParams (2 * m) (invArr m) ((codes ws).filter fun w => w.length ≤ k) (codes subs) with
    rels := (codes ws).map fun w => (w, invWord (invArr m) w) }

theorem codes_facts (ws : List (List (Fin m × Bool))) {r : List ℕ}
    (hr : r ∈ codes ws ++ (codes ws).map (invWord (invArr m))) :
    (∀ y ∈ r, y < 2 * m) ∧
      evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) r = 1 := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hginv : ∀ x < 2 * m, presLetter rels ((invArr m).getD x 0) = (presLetter rels x)⁻¹ :=
    fun x hx => by rw [invArr_getD hx]; exact presLetter_invCode rels hx
  have hrel : ∀ r ∈ codes ws, evalWord (presLetter rels) r = 1 := by
    intro r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [evalWord_presLetter]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨letters_codes hr, hrel r hr⟩
  · simp only [List.mem_map] at hr
    obtain ⟨r0, hr0, rfl⟩ := hr
    have hl := letters_codes hr0
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [invWord, List.mem_map, List.mem_reverse] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [invArr_getD (hl z hz)]
      exact invCode_lt (hl z hz)
    · rw [evalWord_invWord (fun y hy => hginv y (hl y hy)), hrel r0 hr0, inv_one]

theorem goodParamsShort (ws subs : List (List (Fin m × Bool))) (k : ℕ) (H : Subgroup (PG m ws))
    (hsubs : ∀ w ∈ subs, PresentedGroup.mk _ (FreeGroup.mk w) ∈ H) :
    Good (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) H
      (presParamsShort ws subs k) := by
  have hg := goodParams ws subs H hsubs
  refine ⟨hg.inv_lt, hg.gen_inv, ?_, ?_, ?_⟩
  · intro x p hp
    obtain ⟨h1, r, hr, hpr⟩ := mem_scans (L := 2 * m) (inv := invArr m)
      (rels := (codes ws).filter fun w => w.length ≤ k) (subs := codes subs) hp
    have hr' : r ∈ codes ws ++ (codes ws).map (invWord (invArr m)) := by
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ (List.mem_of_mem_filter hr)
      · simp only [List.mem_map] at hr
        obtain ⟨r0, hr0, rfl⟩ := hr
        exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_mem_filter hr0))
    obtain ⟨hl, he⟩ := codes_facts ws hr'
    exact ⟨h1, letters_rotation hpr hl, evalWord_rotation hpr he⟩
  · intro p hp
    exact hg.subs p hp
  · intro p hp
    exact hg.rels p hp

theorem index_le_presentedShort (ws subs : List (List (Fin m × Bool))) (k : ℕ)
    (H : Subgroup (PG m ws)) (hsubs : ∀ w ∈ subs, PresentedGroup.mk _ (FreeGroup.mk w) ∈ H)
    {cap n : ℕ} (h : checkHLT (presParamsShort ws subs k) cap n = true) :
    H.FiniteIndex ∧ H.index ≤ n :=
  index_le_of_checkHLT (goodParamsShort ws subs k H hsubs) (by
    have := closure_presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
    simpa [presParamsShort, mkParams] using this) h

@[expose] def subsetCheckShort (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ) :
    Bool :=
  checkHLT (presParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k) cap n

theorem card_le_of_subsetCheckShort (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {k cap n : ℕ} (h : subsetCheckShort ws S k cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧
      Nat.card (PG m ws) ≤ n * Nat.card (PG (subsetOf m S).length
        (restrictWords (subsetOf m S) ws)) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  obtain ⟨hfi, hidx⟩ := index_le_presentedShort ws ((subsetOf m S).map fun x => [(x, true)]) k
    (genSub rels (subsetOf m S))
    (by
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact Subgroup.subset_closure ⟨x, hx, rfl⟩) h
  obtain ⟨hfinH, hsub⟩ := card_genSub_le ws (subsetOf m S)
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ genSub rels (subsetOf m S)) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (genSub rels (subsetOf m S))
  refine ⟨hfin, ?_⟩
  rw [← (genSub rels (subsetOf m S)).index_mul_card]
  exact Nat.mul_le_mul hidx hsub

end CFSG.CosetTable
