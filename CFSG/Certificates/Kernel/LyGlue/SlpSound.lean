module

public import Certificates.Data.Kernel.LyGlue.Defs
import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.KC.LyGlue

open CFSG.KC.Enum CFSG.KS Equiv

variable {n : Nat}

@[expose] def prodP (B : Nat → Perm (Fin n)) (L : List Nat) : Perm (Fin n) := (L.map B).prod

theorem prodP_append (B : Nat → Perm (Fin n)) (L M : List Nat) :
    prodP B (L ++ M) = prodP B L * prodP B M := by
  simp [prodP, List.map_append, List.prod_append]

theorem prodP_flatMap (B : Nat → Perm (Fin n)) (g : Nat → List Nat) (L : List Nat) :
    prodP B (L.flatMap g) = (L.map fun k => prodP B (g k)).prod := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    rw [List.flatMap_cons, prodP_append, ih]
    rfl

theorem appL_eq {T : Nat → Nat → Nat} (C : Nat → Perm (Fin n)) :
    ∀ ls : List Nat, (∀ k ∈ ls, ∀ a : Fin n, T k a = C k a) →
      ∀ x : Fin n, appL T ls x = ((ls.map C).prod x : Nat)
  | [], _, x => rfl
  | k :: ls, h, x => by
    change T k (appL T ls x) = _
    rw [appL_eq C ls (fun l hl => h l (List.mem_cons_of_mem _ hl)) x, h k List.mem_cons_self,
      List.map_cons, List.prod_cons, Perm.mul_apply]

theorem findStep_spec {S : List (Nat × Nat × List Nat)} {k : Nat} (h : ∃ s ∈ S, s.1 = k) :
    findStep S k ∈ S ∧ (findStep S k).1 = k := by
  unfold findStep
  cases hf : S.find? (fun s => s.1 == k) with
  | none =>
    obtain ⟨s, hs, hk⟩ := h
    have := List.find?_eq_none.1 hf s hs
    simp [hk] at this
  | some s =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [beq_iff_eq] at h2
    exact ⟨h1, h2⟩

theorem progOK_spec {S : List (Nat × Nat × List Nat)} {nb : Nat} (h : progOK S nb = true)
    {s : Nat × Nat × List Nat} (hs : s ∈ S) :
    nb ≤ s.1 ∧ s.2.1 < s.1 ∧ (∀ l ∈ s.2.2, l < s.1) ∧
      ∀ l ∈ s.2.1 :: s.2.2, l < nb ∨ ∃ t ∈ S, t.1 = l := by
  have := List.all_eq_true.1 h s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.any_eq_true, beq_iff_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  exact ⟨h1, h2, h3, h4⟩

theorem stepPt_spec {T : Nat → Nat → Nat} {s : Nat × Nat × List Nat} (h : stepPt n T s = true)
    (a : Fin n) : T s.1 a = appL T s.2.2 (T s.2.1 a) :=
  Nat.eq_of_beq_eq_true (allN_spec h a a.2)

theorem slp_sound {S : List (Nat × Nat × List Nat)} {nb : Nat} {T : Nat → Nat → Nat}
    {B : Nat → Perm (Fin n)} (hB : ∀ k < nb, ∀ a : Fin n, T k a = B k a) (hB0 : B 0 = 1)
    (hnb : 0 < nb) (hprog : progOK S nb = true) (hsteps : ∀ s ∈ S, stepPt n T s = true) :
    ∀ f k, k < f → (k < nb ∨ ∃ s ∈ S, s.1 = k) →
      ∀ a : Fin n, T k a = (prodP B (flat S nb f k) a : Nat) := by
  intro f
  induction f with
  | zero => intro k hk; omega
  | succ f ih =>
    intro k hk hdef a
    by_cases h0 : k = 0
    · subst h0
      rw [flat, if_pos rfl, hB 0 hnb, hB0]
      rfl
    by_cases hb : k < nb
    · rw [flat, if_neg h0, if_pos hb, hB k hb]
      simp [prodP]
    · rw [flat, if_neg h0, if_neg hb]
      have hex : ∃ s ∈ S, s.1 = k := hdef.resolve_left hb
      obtain ⟨hmem, hout⟩ := findStep_spec hex
      set s := findStep S k
      obtain ⟨-, hin, hlets, hdefs⟩ := progOK_spec hprog hmem
      rw [hout] at hin hlets
      have hst := stepPt_spec (hsteps s hmem) a
      have hinp := ih s.2.1 (by omega) (hdefs s.2.1 List.mem_cons_self) a
      have hl : ∀ l ∈ s.2.2, ∀ x : Fin n, T l x = (prodP B (flat S nb f l) x : Nat) :=
        fun l hl => ih l (by have := hlets l hl; omega) (hdefs l (List.mem_cons_of_mem _ hl))
      rw [← hout, hst]
      have e : T s.2.1 a = ((prodP B (flat S nb f s.2.1) a : Fin n) : Nat) := hinp
      rw [e, appL_eq (fun l => prodP B (flat S nb f l)) s.2.2 hl, prodP_append, prodP_flatMap,
        Perm.mul_apply]

end CFSG.KC.LyGlue

end
