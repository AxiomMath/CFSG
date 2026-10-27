module

public import Certificates.Certificate12630
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

open Equiv

@[expose] def encP (g : Equiv.Perm (Fin 77)) : Array Nat := Array.ofFn fun i : Fin 77 => (g i : Nat)

theorem encP_getD (g : Equiv.Perm (Fin 77)) {k : Nat} (hk : k < 77) :
    (encP g).getD k 0 = (g ⟨k, hk⟩ : Nat) := by
  simp [encP, hk]

theorem encP_one : encP 1 = idA := by
  apply Array.ext
  · simp [encP, idA]
  · intro i h1 h2
    simp [encP, idA]

theorem encP_mul (g h : Equiv.Perm (Fin 77)) : encP (g * h) = comp (encP g) (encP h) := by
  apply Array.ext
  · simp [encP, comp]
  · intro i h1 h2
    have hi : i < 77 := by simpa [encP] using h1
    simp [encP, comp]

theorem encP_injective : Function.Injective encP := by
  intro g h e
  ext i
  have := congrArg (fun a => a.getD i.val 0) e
  simp only [encP_getD g i.2, encP_getD h i.2] at this
  exact this

@[expose] def evalPerm (g : Nat → Equiv.Perm (Fin 77)) (w : List Nat) : Equiv.Perm (Fin 77) :=
  w.foldl (fun acc k => acc * g k) 1

theorem encP_evalPerm (g : Nat → Equiv.Perm (Fin 77)) (e : Array (Array Nat))
    (he : ∀ k, encP (g k) = e.getD k idA) (w : List Nat) :
    encP (evalPerm g w) = evalW e w := by
  unfold evalPerm evalW
  suffices h : ∀ (acc : Equiv.Perm (Fin 77)),
      encP (w.foldl (fun a k => a * g k) acc) =
        w.foldl (fun a k => comp a (e.getD k idA)) (encP acc) by
    simpa [encP_one] using h 1
  induction w with
  | nil => intro acc; rfl
  | cons k w ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, encP_mul, he]

theorem evalPerm_mem (g : Nat → Equiv.Perm (Fin 77)) (H : Subgroup (Equiv.Perm (Fin 77)))
    (hg : ∀ k, g k ∈ H) (w : List Nat) : evalPerm g w ∈ H := by
  unfold evalPerm
  suffices h : ∀ (acc : Equiv.Perm (Fin 77)), acc ∈ H → w.foldl (fun a k => a * g k) acc ∈ H by
    exact h 1 H.one_mem
  induction w with
  | nil => intro acc h; exact h
  | cons k w ih => intro acc h; exact ih _ (H.mul_mem h (hg k))

theorem over77_of_certificate
    (pA pB pZ σ : Equiv.Perm (Fin 77)) (s : Fin 9 → Equiv.Perm (Fin 77))
    (hA : encP pA = dataA) (hB : encP pB = dataB) (hZ : encP pZ = dataZ)
    (hσ : encP σ = dataSigma) (hs : ∀ k : Fin 9, encP (s k) = dataS.getD k idA)
    (L : Subgroup (Equiv.Perm (Fin 77))) (hPL : Subgroup.closure {pA, pB, pZ} ≤ L)
    (hL : L ≤ Subgroup.closure (Set.range s))
    (hnot : ¬ L ≤ Subgroup.closure {pA, pB, pZ}) : σ ∈ L :=
  Certificates.certificate12630 pA pB pZ σ s hA hB hZ hσ hs L hPL hL hnot

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77
