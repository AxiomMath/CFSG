module

public import Certificates.Data.Kernel.LocalQT.SylV
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr

import CFSG.Certificates.Kernel.LocalQTSylVProved
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.LQT.SV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.QuasithinUnique.Setup.X1

theorem bIf_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c <;> simp_all

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bindSV_aux {T : Nat → Nat} {M : Nat} : ∀ (L : List Nat) (i : Nat),
    List.rec (motive := fun _ => Nat → Bool)
      (fun i => allBlk i (fun j => Nat.beq (T j) (nat_lit 0)) (Nat.sub M i))
      (fun x _ ih i => Bool.rec (motive := fun _ => Bool) false (strictB (Nat.succ i) ih)
        (Bool.rec (motive := fun _ => Bool) true (Nat.beq (T i) x) (Nat.blt i M))) L i = true →
    ∀ k, i ≤ k → k < M → L.getD (k - i) 0 = T k
  | [], i, h, k, hik, hkM => by
    have h1 := allBlk_spec h (k - i) (by simp only [Nat.sub_eq]; omega)
    have e : Nat.add i (k - i) = k := by simp only [Nat.add_eq]; omega
    rw [e] at h1
    rw [List.getD_nil, Nat.eq_of_beq_eq_true h1]
  | x :: xs, i, h, k, hik, hkM => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rw [strictB_eq] at h2
    rcases Nat.eq_or_lt_of_le hik with e | hlt
    · subst e
      have hb : Nat.blt i M = true := by rw [Nat.blt_eq]; exact hkM
      have := (bIf_true h1).1 hb
      rw [Nat.sub_self, List.getD_cons_zero, Nat.eq_of_beq_eq_true this]
    · have := bindSV_aux xs (i + 1) h2 k hlt hkM
      have e : k - i = (k - (i + 1)) + 1 := by omega
      rw [e, List.getD_cons_succ, this]

theorem bindSV_spec {L : List Nat} {T : Nat → Nat} {M : Nat} (h : bindSV L T M = true) :
    ∀ i < M, L.getD i 0 = T i := by
  intro i hi
  have := bindSV_aux L 0 h i (Nat.zero_le i) hi
  rwa [Nat.sub_zero] at this

theorem sylSV_sound {n w N ng r K L : Nat} {G GI : List Nat} {E PT LT TB IS SR : Nat → Nat}
    {P : List Nat} {gens : List PArr} {par lab tab : List Nat}
    (hg : gens.map Prod.fst = G.map (unpack n w))
    (hh : headSV n w N ng G GI = true)
    (hp : ∀ i < N, par.getD i 0 = PT i) (hl : ∀ i < N, lab.getD i 0 = LT i)
    (ht : ∀ i < N * ng, tab.getD i 0 = TB i)
    (hKL : N ≤ K * L)
    (hc : ∀ s < K, chunkSV n w N ng G E PT LT TB (Nat.mul s L) L = true)
    (hs : sortAllSV N E IS SR = true)
    (hq : pairsSV w N E P r = true) (hP : ∀ p ∈ P, p < n) :
    sylVerify n N gens par lab tab (sylBuild n N gens par lab) r = true ∧
      ∀ k < N, (sylBuild n N gens par lab)[k]! = unpack n w (E k) := by
  exact Pf.sylSV_sound' hg hh hp hl ht hKL hc hs hq hP

end CFSG.KC.LQT.SV

end
