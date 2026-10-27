module

public import Certificates.Data.Kernel.W4RowFi22W.Defs
public import CFSG.Certificates.Kernel.Census.BaseSound

public section

namespace CFSG.KC.W4F22

open CFSG.KC.Enum CFSG.KC.Census CFSG.KC.Census.Base

variable {n w h : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)} {E : List (List ℕ)}

@[expose] def actPerm (ℓ : ℕ → Equiv.Perm (Fin n)) : List ℕ → Equiv.Perm (Fin n)
  | [] => 1
  | k :: l => actPerm ℓ l * ℓ k

@[expose] def ev (ℓ : ℕ → Equiv.Perm (Fin n)) (E : List (List ℕ)) (i : ℕ) : Equiv.Perm (Fin n) :=
  actPerm ℓ (E.getD i [])

@[expose] def refPerm (ℓ : ℕ → Equiv.Perm (Fin n)) (E : List (List ℕ)) (r : ℕ) :
    Equiv.Perm (Fin n) :=
  if r % 2 = 1 then (ev ℓ E (r / 2))⁻¹ else ev ℓ E (r / 2)

@[expose] def refsPerm (ℓ : ℕ → Equiv.Perm (Fin n)) (E : List (List ℕ)) :
    List ℕ → Equiv.Perm (Fin n)
  | [] => 1
  | r :: rs => refsPerm ℓ E rs * refPerm ℓ E r

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem actW_cons (k : ℕ) (l : List ℕ) (p : ℕ) :
    actW w L (k :: l) p = actW w L l (at' w (L k) p) :=
  strictN_eq' _ _

theorem actPerm_append (a b : List ℕ) : actPerm ℓ (a ++ b) = actPerm ℓ b * actPerm ℓ a := by
  induction a with
  | nil => simp [actPerm]
  | cons k l ih => simp [actPerm, ih, mul_assoc]

theorem refPerm_two_mul (i : ℕ) : refPerm ℓ E (2 * i) = ev ℓ E i := by
  have h1 : ¬ (2 * i) % 2 = 1 := by omega
  rw [refPerm, if_neg h1, Nat.mul_div_cancel_left i (by norm_num)]

theorem refPerm_two_mul_add_one (i : ℕ) : refPerm ℓ E (2 * i + 1) = (ev ℓ E i)⁻¹ := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  rw [refPerm, if_pos h1, h2]

theorem refsPerm_cons (r : ℕ) (rs : List ℕ) :
    refsPerm ℓ E (r :: rs) = refsPerm ℓ E rs * refPerm ℓ E r := rfl

theorem refsPerm_append (a b : List ℕ) :
    refsPerm ℓ E (a ++ b) = refsPerm ℓ E b * refsPerm ℓ E a := by
  induction a with
  | nil => simp [refsPerm]
  | cons r l ih => simp [refsPerm, ih, mul_assoc]

theorem refsPerm_flatten_replicate (p : ℕ) (x : List ℕ) :
    refsPerm ℓ E (List.replicate p x).flatten = refsPerm ℓ E x ^ p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [List.replicate_succ, List.flatten_cons, refsPerm_append, ih, pow_succ]

theorem getD_wordOK (hE : ∀ x ∈ E, WordOK h x) (i : ℕ) : WordOK h (E.getD i []) := by
  rcases Nat.lt_or_ge i E.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact hE _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    intro k hk
    simp at hk

section Letters

variable (H : Letters n w h L ℓ)
include H

theorem actW_eq : ∀ (x : List ℕ), WordOK h x → ∀ p (hp : p < n),
    actW w L x p = (actPerm ℓ x ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => rfl
  | k :: l, hx, p, hp => by
    have hk := hx k List.mem_cons_self
    rw [actW_cons, H.at_eq k hk p hp,
      actW_eq l (fun j hj => hx j (List.mem_cons_of_mem _ hj)) _ (ℓ k ⟨p, hp⟩).2]
    simp [actPerm, Equiv.Perm.mul_apply]

theorem actPerm_inv : ∀ (x : List ℕ), WordOK h x →
    actPerm ℓ (List.map (lsw h) (List.reverse x)) = (actPerm ℓ x)⁻¹
  | [], _ => by simp [actPerm]
  | k :: l, hx => by
    have hk := hx k List.mem_cons_self
    rw [List.reverse_cons, List.map_append, actPerm_append,
      actPerm_inv l (fun j hj => hx j (List.mem_cons_of_mem _ hj))]
    simp [actPerm, ℓ_lsw H hk, mul_inv_rev]

theorem actWI_eq (x : List ℕ) (hx : WordOK h x) (p : ℕ) (hp : p < n) :
    actWI w h L x p = ((actPerm ℓ x)⁻¹ ⟨p, hp⟩ : ℕ) := by
  have hx' : WordOK h (List.map (lsw h) (List.reverse x)) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
    exact lsw_lt (hx j (List.mem_reverse.1 hj))
  unfold actWI
  rw [actW_eq H _ hx' p hp, actPerm_inv H x hx]

variable (hE : ∀ x ∈ E, WordOK h x)
include hE

theorem refAct_eq (r p : ℕ) (hp : p < n) : refAct w h L E r p = (refPerm ℓ E r ⟨p, hp⟩ : ℕ) := by
  unfold refAct refPerm ev
  have hd : Nat.div r 2 = r / 2 := rfl
  rw [hd]
  cases h2 : Nat.beq (Nat.mod r 2) 1
  · have h3 : ¬ r % 2 = 1 := Nat.ne_of_beq_eq_false h2
    rw [if_neg h3, cond_false]
    exact actW_eq H _ (getD_wordOK hE _) p hp
  · have h3 : r % 2 = 1 := Nat.eq_of_beq_eq_true h2
    rw [if_pos h3, cond_true]
    exact actWI_eq H _ (getD_wordOK hE _) p hp

theorem refsAct_eq : ∀ (rs : List ℕ) (p : ℕ) (hp : p < n),
    refsAct w h L E rs p = (refsPerm ℓ E rs ⟨p, hp⟩ : ℕ)
  | [], _, _ => rfl
  | r :: rs, p, hp => by
    have e : refsAct w h L E (r :: rs) p = refsAct w h L E rs (refAct w h L E r p) :=
      strictN_eq' _ _
    rw [e, refAct_eq H hE r p hp, refsAct_eq rs _ (refPerm ℓ E r ⟨p, hp⟩).2]
    simp [refsPerm, Equiv.Perm.mul_apply]

theorem relB_sound {bs : List ℕ} {rl : List ℕ × List ℕ} (hc : relB w h L E bs rl = true) :
    ∀ b ∈ bs, ∀ hb : b < n, (refsPerm ℓ E rl.1 ⟨b, hb⟩ : ℕ) = (refsPerm ℓ E rl.2 ⟨b, hb⟩ : ℕ) := by
  intro b hbs hb
  unfold relB at hc
  have e := Nat.eq_of_beq_eq_true (List.all_eq_true.1 hc b hbs)
  rwa [refsAct_eq H hE _ b hb, refsAct_eq H hE _ b hb] at e

theorem eq_of_relB {P : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} (hB : BaseOf P bs)
    {rl : List ℕ × List ℕ} (h1 : refsPerm ℓ E rl.1 ∈ P) (h2 : refsPerm ℓ E rl.2 ∈ P)
    (hc : relB w h L E bs rl = true) : refsPerm ℓ E rl.1 = refsPerm ℓ E rl.2 :=
  eq_of_base hB h1 h2 fun b hb hbs => relB_sound H hE hc b hbs hb

theorem movB_sound {m : List ℕ × ℕ} (hm : m.2 < n) (hc : movB w h L E m = true) :
    refsPerm ℓ E m.1 ≠ 1 := by
  intro e
  unfold movB at hc
  rw [Bool.not_eq_true', refsAct_eq H hE _ _ hm, e] at hc
  exact absurd (Nat.beq_refl m.2) (by simpa using hc)

end Letters

theorem lettersB_sound {m : ℕ} (hc : lettersB E m = true) : ∀ x ∈ E, ∀ k ∈ x, k < m := by
  intro x hx k hk
  unfold lettersB at hc
  exact Nat.blt_eq.mp (List.all_eq_true.1 (List.all_eq_true.1 hc x hx) k hk)

end CFSG.KC.W4F22

end
