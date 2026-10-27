module

public import Certificates.Data.Kernel.O8.EnumK
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Native

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2

@[expose] noncomputable def decE (D : Nat → Nat) (m : Nat) : Enum :=
  ⟨Array.ofFn (n := m) fun i => enKey D i.val, Array.ofFn (n := m) fun i => enPar D i.val,
    Array.ofFn (n := m) fun i => enGen D i.val, Array.ofFn (n := m) fun i => enDep D i.val⟩

@[expose] noncomputable def genPairsK (G GI : Nat → Nat) (ng : Nat) : Array (ℕ × ℕ) :=
  Array.ofFn (n := ng) fun j => (G j.val, GI j.val)

theorem genPairsK_eq {G GI : Nat → Nat} {ng : Nat} {gs : Array (ℕ × ℕ)} (hs : gs.size = ng)
    (hg : ∀ j < ng, gs.getD j (0, 0) = (G j, GI j)) : genPairsK G GI ng = gs := by
  subst hs
  apply Array.ext (by simp [genPairsK])
  intro j h1 h2
  have := hg j h2
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some] at this
  simp [genPairsK, this]

theorem memK_of_idx {A : Array ℕ} (hs : sortedK A = true) (hA : A.size < 2 ^ 17) {i : ℕ}
    (hi : i < A.size) : memK A (A.getD i 0) = true :=
  memK_of_mem hs (by omega) hi rfl

theorem decE_keys_getD {D : Nat → Nat} {m i : Nat} (hi : i < m) :
    (decE D m).keys.getD i 0 = enKey D i := by
  simp [decE, Array.getD_eq_getD_getElem?, hi]

theorem decE_keys_size (D : Nat → Nat) (m : Nat) : (decE D m).keys.size = m := by
  simp [decE]

theorem idK_eq : idK = ID12 := by
  decide +kernel

theorem decE_getD (D : Nat → Nat) (m i : Nat) :
    (decE D m).keys.getD i 0 = if i < m then enKey D i else 0 := by
  split_ifs with h
  · exact decE_keys_getD h
  · simp [decE, Array.getD_eq_getD_getElem?, h]

theorem memK_decE {gs : Array (ℕ × ℕ)} {D : Nat → Nat} {m q : Nat}
    (h : enumOK gs (decE D m) = true) (hm' : m < 2 ^ 17) (hq : q < m) :
    memK (decE D m).keys (enKey D q) = true := by
  rw [← decE_keys_getD hq]
  exact memK_of_idx (Enum.of_enumOK h).2.1 (by rwa [decE_keys_size])
    (by rwa [decE_keys_size])

end CFSG.KC.O8

end
