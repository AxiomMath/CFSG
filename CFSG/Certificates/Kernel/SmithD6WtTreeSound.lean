module

public import Certificates.Data.Kernel.SmithD6.WtTree
public import CFSG.Certificates.Kernel.KeyTreeChunksSound
import CFSG.Certificates.Kernel.PkTreeSound

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree

theorem wtTreeGo_sound {D G : Nat} : ∀ (l : List Nat) (i : Nat), wtTreeGo D G l i = true →
    ∀ k < l.length, wtRecOK D G (l.getD k 0) (i + k) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | s :: l, i, h, k, hk => by
    have e : wtTreeGo D G (s :: l) i = bAnd(wtRecOK D G s i, wtTreeGo D G l (i + 1)) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases k with _ | k
    · simpa using h1
    · have := wtTreeGo_sound l (i + 1) h2 k (by simpa using hk)
      rw [List.getD_cons_succ, show i + (k + 1) = i + 1 + k by omega]
      exact this

theorem wtTree_induct {D G N : Nat} {W : Nat → Nat}
    (hrec : ∀ i < N, wtRecOK D G (W i) i = true)
    (hfind : ∀ x v, KT.find x wt64Tree = v + 1 → v < N ∧ W v = x)
    (Q : Nat → Prop) (h0 : Q 0)
    (hstep : ∀ g < 13, ∀ i < N, ∀ p < N,
      liftT (JT.gensT.getD g []) (W i) = W p → Q p → Q i) :
    ∀ i < N, Q i := by
  suffices H : ∀ n, ∀ i < N, pkGet D 6 i ≤ n → Q i from fun i hi => H _ i hi le_rfl
  intro n
  induction n with
  | zero =>
    intro i hi hd
    have h1 := (pkAnd_true (hrec i hi)).1
    simp [Nat.blt_eq] at h1
    omega
  | succ n ih =>
    intro i hi hd
    have h1 := hrec i hi
    unfold wtRecOK wtRecGo at h1
    obtain ⟨-, h2⟩ := pkAnd_true h1
    cases hb : Nat.beq (pkGet D 6 i) 1
    · have h3 := pkIf_false h2 hb
      obtain ⟨hg, h4⟩ := pkAnd_true h3
      unfold wtParOK at h4
      obtain ⟨hf, h5⟩ := pkAnd_true h4
      obtain ⟨-, hpd⟩ := pkAnd_true h5
      have hf' := Nat.blt_eq.mp hf
      obtain ⟨v, hv⟩ : ∃ v, KT.find (liftT (JT.gensT.getD (pkGet G 4 i) []) (W i)) wt64Tree =
          v + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hf').symm⟩
      rw [hv, Nat.pred_succ] at hpd
      have hpd' := Nat.blt_eq.mp hpd
      obtain ⟨hvN, hW⟩ := hfind _ v hv
      exact hstep _ (Nat.blt_eq.mp hg) i hi v hvN hW.symm (ih v hvN (by omega))
    · have h3 := Nat.eq_of_beq_eq_true (pkIf_true h2 hb)
      rw [h3]
      exact h0

end CFSG.KD.SmithD6

end
