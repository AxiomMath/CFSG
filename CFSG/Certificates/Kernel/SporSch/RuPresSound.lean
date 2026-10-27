module

public import Certificates.Data.Kernel.SporSch.RuPres
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Bridge

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem rep_wordPKFrom {n w : Nat} {G GI : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hG : ∀ i, Rep n (unpack n w (G i)) (g i)) (hGI : ∀ i, Rep n (unpack n w (GI i)) (g i)⁻¹)
    (hc : ∀ i, canonK n w (mask w) (n * w) (G i) = true ∧ canonK n w (mask w) (n * w) (GI i) = true)
    {P : Nat} {h : Equiv.Perm (Fin n)} (hP : Rep n (unpack n w P) h)
    (hPc : canonK n w (mask w) (n * w) P = true) :
    ∀ v, Rep n (unpack n w (wordPKFrom n w G GI v P)) (wordProd g v * h) ∧
      canonK n w (mask w) (n * w) (wordPKFrom n w G GI v P) = true
  | [] => by
    refine ⟨?_, hPc⟩
    change Rep n (unpack n w P) (wordProd g [] * h)
    simpa [wordProd] using hP
  | l :: v => by
    obtain ⟨ih, ihc⟩ := rep_wordPKFrom hG hGI hc hP hPc v
    obtain ⟨i, b⟩ := l
    change Rep n (unpack n w (strictN (wordPKFrom n w G GI v P) (fun a =>
        pcomp n w (mask w) (Bool.rec (GI i) (G i) b) a))) (wordProd g ((i, b) :: v) * h) ∧
      canonK n w (mask w) (n * w) (strictN (wordPKFrom n w G GI v P) (fun a =>
        pcomp n w (mask w) (Bool.rec (GI i) (G i) b) a)) = true
    rw [strictN_eq]
    have hw : wordProd g ((i, b) :: v) * h = (if b then g i else (g i)⁻¹) * (wordProd g v * h) := by
      simp [wordProd, mul_assoc]
    rw [hw]
    cases b
    · refine ⟨?_, canonK_pcomp (hc i).2 ihc⟩
      rw [← compA_unpack (hc i).2 ihc]
      exact rep_compA (hGI i) ih
    · refine ⟨?_, canonK_pcomp (hc i).1 ihc⟩
      rw [← compA_unpack (hc i).1 ihc]
      exact rep_compA (hG i) ih

theorem takeL_eq : ∀ (k : Nat) (l : List (Nat × Bool)), takeL k l = l.take k
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | k + 1, x :: l => by
    change x :: takeL k l = x :: l.take k
    rw [takeL_eq k l]

theorem dropL_eq : ∀ (k : Nat) (l : List (Nat × Bool)), dropL k l = l.drop k
  | _, [] => by cases ‹Nat› <;> rfl
  | 0, _ :: _ => rfl
  | k + 1, _ :: l => dropL_eq k l

theorem wAt_eq : ∀ (W : List (List (Nat × Bool))) (r : Nat), wAt W r = W.getD r []
  | [], _ => by cases ‹Nat› <;> rfl
  | _ :: _, 0 => rfl
  | _ :: W, r + 1 => wAt_eq W r

theorem wordEqL_sound : ∀ {v u : List (Nat × Bool)}, wordEqL v u = true → v = u
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [wordEqL])
  | _ :: _, [], h => absurd h (by simp [wordEqL])
  | (a, b) :: v, (c, d) :: u, h => by
    change bAnd(Nat.beq a c, bAnd(Bool.rec (Bool.not d) d b, wordEqL v u)) = true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    have e1 : a = c := Nat.eq_of_beq_eq_true h1
    have e2 : b = d := by cases b <;> cases d <;> simp_all
    rw [e1, e2, wordEqL_sound h4]

theorem lenL_eq : ∀ (v : List (Nat × Bool)), lenL v = v.length
  | [] => rfl
  | _ :: v => congrArg Nat.succ (lenL_eq v)

theorem word_chain {n w : Nat} {G GI : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hG : ∀ i, Rep n (unpack n w (G i)) (g i)) (hGI : ∀ i, Rep n (unpack n w (GI i)) (g i)⁻¹)
    (hc : ∀ i, canonK n w (mask w) (n * w) (G i) = true ∧ canonK n w (mask w) (n * w) (GI i) = true)
    (hid : canonK n w (mask w) (n * w) (pidn n w) = true) (hidA : idA n = unpack n w (pidn n w))
    {W : List (Nat × Bool)} {c K : Nat} {T : Nat → Nat} (hlen : W.length ≤ c * K)
    (hend : T K = pidn n w)
    (hstep : ∀ q < K, wordPKFrom n w G GI ((W.drop (c * q)).take c) (T (q + 1)) = T q) :
    Rep n (unpack n w (T 0)) (wordProd g W) ∧ canonK n w (mask w) (n * w) (T 0) = true := by
  have key : ∀ i ≤ K, Rep n (unpack n w (T (K - i))) (wordProd g (W.drop (c * (K - i)))) ∧
      canonK n w (mask w) (n * w) (T (K - i)) = true := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le hlen, hend]
      refine ⟨?_, hid⟩
      rw [← hidA]
      simpa [wordProd] using (rep_idA (n := n))
    | succ i ih =>
      intro hi
      have hq : K - (i + 1) < K := by omega
      have e : K - (i + 1) + 1 = K - i := by omega
      obtain ⟨r1, c1⟩ := ih (by omega)
      rw [← e] at r1 c1
      have h1 := rep_wordPKFrom hG hGI hc r1 c1 ((W.drop (c * (K - (i + 1)))).take c)
      rw [hstep _ hq] at h1
      refine ⟨?_, h1.2⟩
      have hs : W.drop (c * (K - (i + 1))) = (W.drop (c * (K - (i + 1)))).take c ++
          W.drop (c * (K - (i + 1) + 1)) := by
        rw [Nat.mul_succ, ← List.drop_drop, List.take_append_drop]
      rw [hs, show wordProd g ((W.drop (c * (K - (i + 1)))).take c ++
          W.drop (c * (K - (i + 1) + 1))) = wordProd g ((W.drop (c * (K - (i + 1)))).take c) *
          wordProd g (W.drop (c * (K - (i + 1) + 1))) by simp [wordProd]]
      exact h1.1
  have := key K (Nat.le_refl K)
  rwa [Nat.sub_self, Nat.mul_zero, List.drop_zero] at this

end CFSG.KS.SporSch

end
