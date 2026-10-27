module

public import Certificates.Data.Kernel.Spor.MulTree
public import CFSG.Certificates.Kernel.Spor.ConjTreeSound
public import CFSG.Sporadic.FischerOddCore.Fi22SylowRecords

public section

namespace CFSG.KS.MulTree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore

variable {w : Nat} {GS PA LA : Nat → Nat}

theorem ev_zero (f z : Nat) : ev w GS PA LA f 0 z = z := by
  cases f <;> rfl

theorem ev_succ (f i z : Nat) : ev w GS PA LA (f + 1) (i + 1) z =
    pg w (mask w) (GS (LA (i + 1))) (ev w GS PA LA f (PA (i + 1)) z) := rfl

theorem ev_fuel {sz : Nat} (hPA : ∀ j < sz, 0 < j → PA j < j) :
    ∀ f g i z, i < sz → i ≤ f → i ≤ g → ev w GS PA LA f i z = ev w GS PA LA g i z
  | _, _, 0, z, _, _, _ => by rw [ev_zero, ev_zero]
  | f + 1, g + 1, i + 1, z, hi, hf, hg => by
    have hp := hPA (i + 1) hi (by omega)
    rw [ev_succ, ev_succ, ev_fuel hPA f g (PA (i + 1)) z (by omega) (by omega) (by omega)]
  | 0, _, _ + 1, _, _, hf, _ => absurd hf (by omega)
  | _ + 1, 0, _ + 1, _, _, _, hg => absurd hg (by omega)

theorem ev_lt {n gs sz : Nat} (hPA : ∀ j < sz, 0 < j → PA j < j)
    (hLA : ∀ j < sz, 0 < j → LA j < gs) (hG : ∀ k < gs, ∀ x < n, pg w (mask w) (GS k) x < n) :
    ∀ f i z, i < sz → z < n → ev w GS PA LA f i z < n
  | 0, _, _, _, hz => hz
  | _ + 1, 0, _, _, hz => hz
  | f + 1, i + 1, z, hi, hz => by
    rw [ev_succ]
    exact hG _ (hLA _ hi (by omega)) _
      (ev_lt hPA hLA hG f _ z (lt_trans (hPA _ hi (by omega)) hi) hz)

theorem unpack_get {n P x : Nat} (hx : x < n) : (unpack n w P)[x]! = pg w (mask w) P x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem mulTree_eq {n gs sz : Nat} {gens : Array (Array Nat)} {par lab : Array Nat}
    (hgens : ∀ k < gs, gens[k]! = unpack n w (GS k))
    (hG : ∀ k < gs, ∀ x < n, pg w (mask w) (GS k) x < n) (hsz : par.size = sz) (h0 : 0 < sz)
    (hpar : ∀ i < sz, 0 < i → par[i]! = PA i ∧ PA i < i)
    (hlab : ∀ i < sz, 0 < i → lab[i]! = LA i ∧ LA i < gs) :
    mulTree n gens par lab =
      Array.ofFn (n := sz) fun i => Array.ofFn (n := n) fun z => ev w GS PA LA sz i z.val := by
  have hPA : ∀ j < sz, 0 < j → PA j < j := fun j hj h => (hpar j hj h).2
  have hLA : ∀ j < sz, 0 < j → LA j < gs := fun j hj h => (hlab j hj h).2
  set V : Nat → Array Nat := fun i => Array.ofFn (n := n) fun z => ev w GS PA LA sz i z.val
  set step := fun (E : Array (Array Nat)) (i : Nat) =>
    E.push (compA n gens[lab[i + 1]!]! E[par[i + 1]!]!)
  have key : ∀ k, k < sz → (List.range k).foldl step #[idA n] =
      Array.ofFn (n := k + 1) fun i => V i.val := by
    intro k
    induction k with
    | zero =>
      intro _
      apply Array.ext
      · simp
      · intro i h1 h2
        have hi : i = 0 := by simpa using h2
        subst hi
        apply Array.ext
        · simp [V, idA]
        · intro z hz1 hz2
          simp [V, idA, ev_zero]
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      have hp := hpar (k + 1) hk (by omega)
      have hl := hlab (k + 1) hk (by omega)
      have hacc : (Array.ofFn (n := k + 1) fun i => V i.val)[par[k + 1]!]! = V (PA (k + 1)) := by
        rw [hp.1, getElem!_pos _ _ (by simpa using hp.2), Array.getElem_ofFn]
      have hc : compA n gens[lab[k + 1]!]! (V (PA (k + 1))) = V (k + 1) := by
        rw [hl.1, hgens _ hl.2]
        apply Array.ext
        · simp [compA, V]
        · intro z hz1 hz2
          have hz : z < n := by simpa [compA] using hz1
          rw [← getElem!_pos _ z hz1, ← getElem!_pos _ z hz2, compA_get hz]
          simp only [V]
          rw [getElem!_ofFn_nat _ hz, getElem!_ofFn_nat _ hz,
            unpack_get (ev_lt hPA hLA hG _ _ _ (lt_trans hp.2 hk) hz)]
          obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
          rw [ev_succ, ev_fuel hPA s (s + 1) (PA (k + 1)) z (lt_trans hp.2 hk) (by omega)
            (by omega)]
      change (Array.ofFn (n := k + 1) fun i => V i.val).push
        (compA n gens[lab[k + 1]!]! (Array.ofFn (n := k + 1) fun i => V i.val)[par[k + 1]!]!) = _
      rw [hacc, hc]
      exact CFSG.KS.ConjTree.ofFn_push V
  obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
  rw [mulTree, hsz, Nat.add_sub_cancel]
  exact key s (by omega)

theorem itn_rep {n : Nat} {t : Array Nat} {G : Equiv.Perm (Fin n)} (ht : Rep n t G) {g : Nat → Nat}
    (hg : ∀ z < n, g z = t[z]!) : ∀ k, ∀ z (hz : z < n), itn g k z = ((G ^ k) ⟨z, hz⟩ : Nat)
  | 0, z, hz => by rw [pow_zero]; rfl
  | k + 1, z, hz => by
    have ih := itn_rep ht hg k z hz
    change g (itn g k z) = _
    rw [pow_succ', Equiv.Perm.mul_apply, hg _ (by rw [ih]; exact Fin.isLt _), ih]
    exact ht _

end CFSG.KS.MulTree

end
