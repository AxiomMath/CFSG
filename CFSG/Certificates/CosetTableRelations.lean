module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

@[expose] def walkRoot (L : ℕ) (tab fwd : Array ℕ) (fuel : ℕ) : ℕ → List ℕ → Option ℕ
  | c, [] => some (find fwd fuel c)
  | c, y :: w =>
    let d := tab.getD (find fwd fuel c * L + y) 0
    if d = 0 then none else walkRoot L tab fwd fuel d w

section Walk

variable {G : Type*} [Group G] {L : ℕ} {gen : ℕ → G} {H : Subgroup G}

theorem walkRoot_spec {st : St} (h : SInv L gen H st) (fuel : ℕ) :
    ∀ (w : List ℕ) (c d : ℕ), (∀ y ∈ w, y < L) → c < st.next →
      walkRoot L st.tab st.fwd fuel c w = some d → Rel L gen H st.par c (evalWord gen w) d := by
  intro w
  induction w with
  | nil =>
    intro c d _ _ hw
    simp only [walkRoot, Option.some.injEq] at hw
    subst hw
    exact (find_spec h fuel c).1.of_eq (by simp [evalWord])
  | cons y w ih =>
    intro c d hl hc hw
    simp only [walkRoot] at hw
    split at hw
    · simp at hw
    · rename_i hne
      have hy : y < L := hl y (by simp)
      obtain ⟨hf1, hf2⟩ := find_spec h fuel c
      have hrel := h.tab_rel _ hne
      obtain ⟨hdiv, hmod⟩ := div_mod_letter (c := find st.fwd fuel c) hy
      rw [hdiv, hmod] at hrel
      have hlt := h.tab_lt _ hne
      have := ih _ d (fun y' hy' => hl y' (by simp [hy'])) hlt hw
      exact (hf1.trans hrel |>.trans this).of_eq (by simp [evalWord_cons])

end Walk

variable {m : ℕ}

@[expose] def relCheck (ws : List (List (Fin m × Bool))) (cap : ℕ)
    (us : List (List (Fin m × Bool))) : Bool :=
  let P := presParams ws []
  let st := enumerateHLT P cap
  (codes us).all fun w => walkRoot P.L st.tab st.fwd st.next 1 w == some 1

theorem eq_one_of_relCheck (ws : List (List (Fin m × Bool))) {cap : ℕ}
    {us : List (List (Fin m × Bool))} (h : relCheck ws cap us = true) :
    ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1 := by
  intro u hu
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hg := goodParams ws [] (⊥ : Subgroup (PG m ws)) (by simp)
  have hinv := enumerateHLT_inv hg cap
  set st := enumerateHLT (presParams ws []) cap
  have hcode : u.map letterCode ∈ codes us := List.mem_map_of_mem hu
  simp only [relCheck, List.all_eq_true, beq_iff_eq] at h
  have hw := h _ hcode
  have hL : (presParams ws []).L = 2 * m := rfl
  rw [hL] at hw hinv
  have hrel := walkRoot_spec hinv st.next _ 1 1 (letters_codes hcode) (by
    have := hinv.next_two; omega) hw
  rw [rel_iff, Inv.rep_one hinv, Subgroup.mem_bot, one_mul, inv_one, mul_one,
    evalWord_presLetter] at hrel
  exact hrel

theorem lift_of_mk {ws : List (List (Fin m × Bool))} (w : List (Fin m × Bool)) :
    FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) (FreeGroup.mk w) =
      PresentedGroup.mk _ (FreeGroup.mk w) := by
  have : FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) =
      PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [this]

noncomputable def mulEquivAppend (ws us : List (List (Fin m × Bool)))
    (h : ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1) : PG m (ws ++ us) ≃* PG m ws :=
  have hf : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk},
      FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_append] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_of_mk]
    rcases hw with hw | hw
    · exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
    · exact h w hw
  have hg : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk},
      FreeGroup.lift (PresentedGroup.of : Fin m → PG m (ws ++ us)) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_of_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (List.mem_append_left _ hw))
  MonoidHom.toMulEquiv (PresentedGroup.toGroup hf) (PresentedGroup.toGroup hg)
    (PresentedGroup.ext fun x => by simp)
    (PresentedGroup.ext fun x => by simp)

theorem card_le_of_append (ws us : List (List (Fin m × Bool)))
    (h : ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1) {n : ℕ}
    (hn : Finite (PG m (ws ++ us)) ∧ Nat.card (PG m (ws ++ us)) ≤ n) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have e := mulEquivAppend ws us h
  obtain ⟨hfin, hle⟩ := hn
  exact ⟨Finite.of_equiv _ e.toEquiv, (Nat.card_congr e.toEquiv).symm ▸ hle⟩

end CFSG.CosetTable
