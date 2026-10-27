module

public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def relCheckF (ws : List (List (Fin m × Bool))) (cap : ℕ)
    (us : List (List (Fin m × Bool))) : Bool :=
  let P := presParams ws []
  let st := enumerate P cap
  (codes us).all fun w => walkRoot P.L st.tab st.fwd st.next 1 w == some 1

theorem eq_one_of_relCheckF (ws : List (List (Fin m × Bool))) {cap : ℕ}
    {us : List (List (Fin m × Bool))} (h : relCheckF ws cap us = true) :
    ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1 := by
  intro u hu
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hg := goodParams ws [] (⊥ : Subgroup (PG m ws)) (by simp)
  have hinv := enumerate_inv hg cap
  set st := enumerate (presParams ws []) cap
  have hcode : u.map letterCode ∈ codes us := List.mem_map_of_mem hu
  simp only [relCheckF, List.all_eq_true, beq_iff_eq] at h
  have hw := h _ hcode
  have hL : (presParams ws []).L = 2 * m := rfl
  rw [hL] at hw hinv
  have hrel := walkRoot_spec hinv st.next _ 1 1 (letters_codes hcode) (by
    have := hinv.next_two; omega) hw
  rw [rel_iff, Inv.rep_one hinv, Subgroup.mem_bot, one_mul, inv_one, mul_one,
    evalWord_presLetter] at hrel
  exact hrel

theorem exists_hom_range (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1) :
    ∃ π : PG hs.length R →* PG m ws,
      π.range = Subgroup.closure
        {g | ∃ s ∈ hs, g = PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
          (FreeGroup.mk s)} := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set H : Subgroup (PG m ws) :=
    Subgroup.closure {g | ∃ s ∈ hs, g = PresentedGroup.mk rels (FreeGroup.mk s)}
  set f : Fin hs.length → PG m ws :=
    fun i => PresentedGroup.mk rels (FreeGroup.mk (hs.getD i []))
  have hf : ∀ r ∈ {r : FreeGroup (Fin hs.length) | r ∈ R.map FreeGroup.mk},
      FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_substWord]
    exact hR _ (List.mem_map_of_mem hw)
  refine ⟨PresentedGroup.toGroup hf, ?_⟩
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    induction g using PresentedGroup.induction_on with
    | H x =>
      induction x using FreeGroup.induction_on with
      | one => simp
      | of i =>
        show PresentedGroup.toGroup hf (PresentedGroup.of i) ∈ H
        rw [PresentedGroup.toGroup.of]
        exact Subgroup.subset_closure
          ⟨_, by rw [List.getD_eq_getElem _ _ i.isLt]; exact List.getElem_mem _, rfl⟩
      | inv_of i hi =>
        rw [map_inv, map_inv]
        exact H.inv_mem hi
      | mul x y hx hy =>
        rw [map_mul, map_mul]
        exact H.mul_mem hx hy
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, hs', rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs'
    refine ⟨PresentedGroup.of ⟨i, hi⟩, ?_⟩
    rw [PresentedGroup.toGroup.of]
    simp only [f, List.getD_eq_getElem _ _ hi]

theorem card_le_of_wordRel (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1)
    {capI n : ℕ} (hidx : check (presParams ws hs) capI n = true) [Finite (PG hs.length R)] :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * Nat.card (PG hs.length R) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set H : Subgroup (PG m ws) :=
    Subgroup.closure {g | ∃ s ∈ hs, g = PresentedGroup.mk rels (FreeGroup.mk s)}
  obtain ⟨hfi, hidx'⟩ := index_le_presented ws hs H
    (fun w hw => Subgroup.subset_closure ⟨w, hw, rfl⟩) hidx
  obtain ⟨φ, hrange⟩ := exists_hom_range ws hs R hR
  replace hrange : φ.range = H := hrange
  have hsurj : Function.Surjective (fun g => (⟨φ g, g, rfl⟩ : φ.range)) :=
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  have hfinH : Finite H := hrange ▸ Finite.of_surjective _ hsurj
  have hcardH : Nat.card H ≤ Nat.card (PG hs.length R) := by
    rw [← hrange]; exact Nat.card_le_card_of_surjective _ hsurj
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient H
  refine ⟨hfin, ?_⟩
  rw [← H.index_mul_card]
  exact Nat.mul_le_mul hidx' hcardH

end CFSG.CosetTable
