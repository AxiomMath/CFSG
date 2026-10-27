module

public import CFSG.Certificates.Kernel.SporLatDcSortSound

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F CFSG.KC.SLDc

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tabA_getD (g : Γ) (p : ℕ) : (tab n g).toArray.getD p 0 = act n g p := img_tab g p

theorem tabA_size (g : Γ) : (tab n g).toArray.size = n := by simp [tab]

theorem good_evalElt (els : Array Γ) (L : ℕ → ℕ → ℕ) {w : List ℕ}
    (hw : ∀ l ∈ w, Good n (tab n (els.getD l 1)).toArray (L l)) :
    Good n (tab n (evalElt els w)).toArray (wordF L w) := by
  induction w with
  | nil =>
    refine ⟨tabA_size _, fun p hp => ⟨?_, hp⟩⟩
    rw [tabA_getD, evalElt_nil, act_one hp]
    rfl
  | cons l w ih =>
    have ih' := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hl := hw l List.mem_cons_self
    refine ⟨tabA_size _, fun p hp => ?_⟩
    obtain ⟨e1, h1⟩ := ih'.2 p hp
    obtain ⟨e2, h2⟩ := hl.2 _ h1
    rw [tabA_getD] at e1 e2
    rw [tabA_getD, evalElt_cons, act_mul _ _ hp, e1, e2]
    exact ⟨rfl, h2⟩

theorem good_tab_inv {g : Γ} {f f' : ℕ → ℕ} (hg : Good n (tab n g).toArray f)
    (hinv : ∀ p < n, f' (f p) = p) : Good n (tab n g⁻¹).toArray f' := by
  refine ⟨tabA_size _, fun p hp => ?_⟩
  have hq := act_lt g⁻¹ hp
  have e1 : act n g (act n g⁻¹ p) = p := by rw [← act_mul _ _ hp, mul_inv_cancel, act_one hp]
  have e2 : f (act n g⁻¹ p) = p := by rw [← (hg.2 _ hq).1, tabA_getD, e1]
  have e3 := hinv _ hq
  rw [e2] at e3
  rw [tabA_getD, e3]
  exact ⟨rfl, hq⟩

@[expose] def seqAct (t : Array ℕ) (x : List ℕ) : List ℕ := x.map fun p => t.getD p 0

@[expose] def seqLab : LabAct (List ℕ) := ⟨seqAct⟩

@[expose] def SeqValid (n : ℕ) (x : List ℕ) : Prop := ∀ p ∈ x, p < n

theorem seqAct_tab (g : Γ) (x : List ℕ) : seqAct (tab n g).toArray x = x.map (act n g) :=
  List.map_congr_left fun p _ => tabA_getD g p

theorem seqAct_good {g : Γ} {f : ℕ → ℕ} (hg : Good n (tab n g).toArray f) (x : List ℕ) :
    seqAct (tab n g).toArray x = x.map fun p => bif Nat.blt p n then f p else 0 := by
  refine List.map_congr_left fun p _ => ?_
  by_cases hp : p < n
  · rw [show Nat.blt p n = true from Nat.blt_eq.mpr hp, cond_true]
    exact (hg.2 p hp).1
  · rw [show Nat.blt p n = false from Bool.eq_false_iff.mpr fun h => hp (Nat.blt_eq.mp h),
      cond_false, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [tabA_size]; omega), Option.getD_none]

theorem seqLab_lawful : LabLawful Γ n seqLab (SeqValid n) where
  valid_act g x hx := by
    intro p hp
    have hp' : p ∈ seqAct (tab n g).toArray x := hp
    rw [seqAct_tab, List.mem_map] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    exact act_lt g (hx q hq)
  act_mul g h x hx := by
    show seqAct (tab n (g * h)).toArray x = seqAct (tab n g).toArray (seqAct (tab n h).toArray x)
    rw [seqAct_tab, seqAct_tab, seqAct_tab, List.map_map]
    exact List.map_congr_left fun p hp => act_mul g h (hx p hp)
  act_one {x} hx := by
    show seqAct (tab n (1 : Γ)).toArray x = x
    rw [seqAct_tab]
    exact (List.map_congr_left fun p hp => act_one (hx p hp)).trans (List.map_id' x)

theorem card_closure_of_omC [Finite Γ] (S : List Γ) (L : ℕ → ℕ → ℕ)
    (hS : ∀ l < S.length, Good n (tab n (S.getD l 1)).toArray (L l)) {x0 : List ℕ}
    (hx0 : ∀ p ∈ x0, p < n) (hsep : ∀ g : Γ, (∀ p ∈ x0, act n g p = p) → g = 1)
    {B : ℕ} {C : List (List (List ℕ))} {rows : List (List ℕ)} {par via ord : List ℕ}
    (h : omC (fun l x => x.map fun p => bif Nat.blt p n then L l p else 0) x0 S.length B C rows
      par via ord = true) :
    Nat.card (Subgroup.closure {x | x ∈ S}) = C.flatten.length := by
  classical
  let els : Array Γ := S.toArray
  let letters : Array (Array ℕ) := els.map fun g => (tab n g).toArray
  have hsz : els.size = letters.size := by simp [letters]
  have hls : letters.size = S.length := by simp [letters, els]
  have hgetD : ∀ l, els.getD l 1 = S.getD l 1 := fun l => by
    simp [els, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray := by
    intro l hl
    have hl' : l < els.size := by rw [hsz]; exact hl
    rw [getElem!_pos letters l hl, Array.getElem_map, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hl', Option.getD_some]
  have hP : ∀ l < letters.size, ∀ x, seqAct letters[l]! x =
      x.map fun p => bif Nat.blt p n then L l p else 0 := by
    intro l hl x
    rw [hel l hl, hgetD]
    exact seqAct_good (hS l (by rw [← hls]; exact hl)) x
  have hO : OmegaSpec seqLab.act letters x0 (omOf C rows par via) :=
    omC_sound (act := seqAct) hP (by rw [hls]; exact h)
  have hstab : stab (seqLab_lawful (Γ := Γ)) hx0 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have e : seqAct (tab n g).toArray x0 = x0 := hg
    rw [seqAct_tab] at e
    have e' := (List.map_eq_map_iff (g := id)).mp (e.trans (List.map_id x0).symm)
    exact hsep g fun p hp => e' p hp
  have hc := OmegaSpec.card_eq seqLab_lawful hx0 els hsz hel hO
    (H := Subgroup.closure {x | x ∈ S}) (by simp [els]) (by rw [hstab]; exact bot_le)
  rw [hc, hstab, Subgroup.card_bot, mul_one]
  simp [omOf]

end CFSG.QuasithinUnique.Ch1.SporLat

end
