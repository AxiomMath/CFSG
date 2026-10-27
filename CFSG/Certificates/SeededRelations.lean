module

public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

@[expose] def seedWord (P : Params) (fuel : ℕ) : List ℕ → ℕ → St → St
  | [], _, st => st
  | y :: w, c, st =>
    let r := find st.fwd st.next c
    let d := st.tab.getD (r * P.L + y) 0
    if d == 0 then
      let st' := processDed P fuel (define P st r y)
      let d' := st'.tab.getD (find st'.fwd st'.next r * P.L + y) 0
      if d' == 0 then st' else seedWord P fuel w d' st'
    else seedWord P fuel w d st

@[expose] def seedAll (P : Params) (fuel : ℕ) : List (List ℕ) → St → St
  | [], st => st
  | w :: ws, st => seedAll P fuel ws (seedWord P fuel w 1 st)

@[expose] def enumerateS (P : Params) (cap : ℕ) (seeds : List (List ℕ)) : St :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felsch P fuel (cap + 1) 1 (seedAll P fuel seeds (fillSubs P fuel P.subs (St.init P.L cap)))

section Soundness

variable {G : Type*} [Group G] {gen : ℕ → G} {H : Subgroup G} {P : Params}

theorem seedWord_inv (hP : Good gen H P) (fuel : ℕ) :
    ∀ (w : List ℕ) (c : ℕ) (st : St),
      SInv P.L gen H st → SInv P.L gen H (seedWord P fuel w c st) := by
  intro w
  induction w with
  | nil => intro c st h; exact h
  | cons y w ih =>
    intro c st h
    simp only [seedWord]
    split
    · split
      · exact processDed_inv hP _ _ (define_inv hP h _ _)
      · exact ih _ _ (processDed_inv hP _ _ (define_inv hP h _ _))
    · exact ih _ _ h

theorem seedAll_inv (hP : Good gen H P) (fuel : ℕ) :
    ∀ (ws : List (List ℕ)) (st : St),
      SInv P.L gen H st → SInv P.L gen H (seedAll P fuel ws st) := by
  intro ws
  induction ws with
  | nil => intro st h; exact h
  | cons w ws ih => intro st h; exact ih _ (seedWord_inv hP fuel w 1 st h)

theorem enumerateS_inv (hP : Good gen H P) (cap : ℕ) (seeds : List (List ℕ)) :
    SInv P.L gen H (enumerateS P cap seeds) :=
  felsch_inv hP _ _ _ _
    (seedAll_inv hP _ seeds _ (fillSubs_inv hP _ _ hP.subs _ (init_inv cap)))

end Soundness

variable {m : ℕ}

@[expose] def relCheckS (ws : List (List (Fin m × Bool))) (cap : ℕ)
    (us : List (List (Fin m × Bool))) : Bool :=
  let P := presParams ws []
  let st := enumerateS P cap (codes us)
  (codes us).all fun w => walkRoot P.L st.tab st.fwd st.next 1 w == some 1

theorem eq_one_of_relCheckS (ws : List (List (Fin m × Bool))) {cap : ℕ}
    {us : List (List (Fin m × Bool))} (h : relCheckS ws cap us = true) :
    ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1 := by
  intro u hu
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hg := goodParams ws [] (⊥ : Subgroup (PG m ws)) (by simp)
  have hinv := enumerateS_inv hg cap (codes us)
  set st := enumerateS (presParams ws []) cap (codes us)
  have hcode : u.map letterCode ∈ codes us := List.mem_map_of_mem hu
  simp only [relCheckS, List.all_eq_true, beq_iff_eq] at h
  have hw := h _ hcode
  have hL : (presParams ws []).L = 2 * m := rfl
  rw [hL] at hw hinv
  have hrel := walkRoot_spec hinv st.next _ 1 1 (letters_codes hcode) (by
    have := hinv.next_two; omega) hw
  rw [rel_iff, Inv.rep_one hinv, Subgroup.mem_bot, one_mul, inv_one, mul_one,
    evalWord_presLetter] at hrel
  exact hrel

end CFSG.CosetTable
