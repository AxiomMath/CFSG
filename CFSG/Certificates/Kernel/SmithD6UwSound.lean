module

public import Certificates.Data.Kernel.SmithD6.UwCheck
public import CFSG.Certificates.Kernel.KeyTreeChunksSound
public import CFSG.Certificates.Kernel.PkTreeSound
import CFSG.Certificates.Kernel.SmithD6WtSound

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KC.Loop

theorem strictKB_eq (y : Nat) (k : Nat → Bool) : strictKB y k = k y := by
  cases y <;> rfl

theorem uwOrbGo_sound : ∀ (ss : List Nat) (rs : List (Nat × Nat)) (v : Nat),
    uwOrbGo ss rs v = true → rs.length = ss.length ∧
      ∀ i (h : i < ss.length) (h' : i < rs.length), uwRecOK (v + i) ss[i] rs[i] = true
  | [], rs, v, h => by
    have h' : isNilB rs = true := h
    rw [isNilB_eq] at h'
    subst h'
    simp
  | s :: ss, [], v, h => by
    have e : uwOrbGo (s :: ss) [] v = false := rfl
    rw [e] at h
    exact absurd h (by decide)
  | s :: ss, r :: rs, v, h => by
    have e : uwOrbGo (s :: ss) (r :: rs) v =
        bAnd(uwRecOK v s r, strictKB (Nat.succ v) (uwOrbGo ss rs)) := rfl
    rw [e, strictKB_eq] at h
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨ih1, ih2⟩ := uwOrbGo_sound ss rs (v + 1) h2
    refine ⟨by simp [ih1], fun i hi hi' => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := ih2 i (by simpa using hi) (by simpa using hi')
      rw [show v + (i + 1) = v + 1 + i by omega]
      simpa using this

theorem bIf_sound {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c
  · exact ⟨fun h' => absurd h' (by decide), fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => absurd h' (by decide)⟩

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem uwRecOK_sound {v s : Nat} {r : Nat × Nat} (h : uwRecOK v s r = true) :
    pkGet JU.uwK 2 v = uwClsK s ∧ uwRep (pkGet JU.uwK 2 v) ≤ v ∧ 0 < pkGet JU.uwD 5 v ∧
    (pkGet JU.uwD 5 v = 1 → v = uwRep (pkGet JU.uwK 2 v)) ∧
    (pkGet JU.uwD 5 v ≠ 1 → r.1 < 45 ∧ liftT (JU.uwT.getD r.1 []) r.2 = s ∧
      ∃ p, KT.find r.2 wt64Tree = p + 1 ∧ 0 < pkGet JU.uwD 5 p ∧
        pkGet JU.uwD 5 p < pkGet JU.uwD 5 v ∧ pkGet JU.uwK 2 p = pkGet JU.uwK 2 v) := by
  obtain ⟨h1, h⟩ := band_true h
  obtain ⟨h2, h⟩ := band_true h
  obtain ⟨h3, h⟩ := band_true h
  obtain ⟨hA, hB⟩ := bIf_sound h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.le_of_ble_eq_true h2, lt_of_blt h3, fun hd => ?_,
    fun hd => ?_⟩
  · exact Nat.eq_of_beq_eq_true (hA (by rw [hd]; rfl))
  · have hf : Nat.beq (pkGet JU.uwD 5 v) 1 = false := by
      cases hb : Nat.beq (pkGet JU.uwD 5 v) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hd
    have h' := hB hf
    obtain ⟨g1, h'⟩ := band_true h'
    obtain ⟨g2, h'⟩ := band_true h'
    unfold uwParOK at h'
    obtain ⟨p1, h'⟩ := band_true h'
    obtain ⟨p2, h'⟩ := band_true h'
    obtain ⟨p3, p4⟩ := band_true h'
    refine ⟨lt_of_blt g1, Nat.eq_of_beq_eq_true g2, Nat.pred (KT.find r.2 wt64Tree), ?_,
      lt_of_blt p2, lt_of_blt p3, Nat.eq_of_beq_eq_true p4⟩
    exact (Nat.succ_pred_eq_of_pos (lt_of_blt p1)).symm

theorem uwCnt_eq (c : Nat) :
    uwCnt c = ((List.range 75735).filter fun j => pkGet JU.uwK 2 j == c).length := by
  unfold uwCnt
  rw [pkSumBelow_eq _ (by decide)]
  generalize 75735 = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.filter_append, List.length_append, ih]
    congr 1
    by_cases hn : pkGet JU.uwK 2 n = c
    · have hb : Nat.beq (pkGet JU.uwK 2 n) c = true := by
        rw [hn]
        exact Nat.beq_refl c
      rw [hb]
      simp [hn]
    · have hb : Nat.beq (pkGet JU.uwK 2 n) c = false := by
        cases hb : Nat.beq (pkGet JU.uwK 2 n) c
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) hn
      rw [hb]
      simp [hn]

end CFSG.KD.SmithD6

end
