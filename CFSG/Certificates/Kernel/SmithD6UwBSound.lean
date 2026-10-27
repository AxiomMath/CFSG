module

public import Certificates.Data.Kernel.SmithD6.UwBCheck
public import CFSG.Certificates.Kernel.SmithD6UwSound
import CFSG.Certificates.Kernel.SmithD6WtSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KC.Loop

theorem ubGo_sound : ∀ (ss : List Nat) (rs : List (Nat × Nat × Nat)) (v : Nat),
    ubGo ss rs v = true → rs.length = ss.length ∧
      ∀ i (h : i < ss.length) (h' : i < rs.length), ubRecOK (v + i) ss[i] rs[i] = true
  | [], rs, v, h => by
    have h' : isNilB rs = true := h
    rw [isNilB_eq] at h'
    subst h'
    simp
  | s :: ss, [], v, h => by
    have e : ubGo (s :: ss) [] v = false := rfl
    rw [e] at h
    exact absurd h (by decide)
  | s :: ss, r :: rs, v, h => by
    have e : ubGo (s :: ss) (r :: rs) v =
        bAnd(ubRecOK v s r, strictKB (Nat.succ v) (ubGo ss rs)) := rfl
    rw [e, strictKB_eq] at h
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨ih1, ih2⟩ := ubGo_sound ss rs (v + 1) h2
    refine ⟨by simp [ih1], fun i hi hi' => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := ih2 i (by simpa using hi) (by simpa using hi')
      rw [show v + (i + 1) = v + 1 + i by omega]
      simpa using this

theorem ubBeqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem ubWitK_sound {s k : Nat} (h : ubWitK s k = true) :
    k / 4096 < k % 4096 ∧ k % 4096 < (k / 4096 ^^^ k % 4096) ∧ (k / 4096 ^^^ k % 4096) < 4096 ∧
      k / 4096 &&& 63 = 0 ∧ k % 4096 &&& 63 = 0 ∧
      (ubTop ^^^ rhoK (k / 4096) (rhoK (k % 4096) ubTop)) = s := by
  obtain ⟨h1, h⟩ := band_true h
  obtain ⟨h2, h⟩ := band_true h
  obtain ⟨h3, h⟩ := band_true h
  obtain ⟨h4, h⟩ := band_true h
  obtain ⟨h5, h6⟩ := band_true h
  exact ⟨lt_of_blt h1, lt_of_blt h2, lt_of_blt h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem ubRecOK_sound {v s : Nat} {r : Nat × Nat × Nat} (h : ubRecOK v s r = true) :
    pkGet JB.bK 2 v = ubKOf s ∧ (pkGet JB.bK 2 v ≠ 0 →
      ubRep (pkGet JB.bK 2 v) ≤ v ∧ 0 < pkGet JB.bD 5 v ∧
      (pkGet JB.bD 5 v = 1 → v = ubRep (pkGet JB.bK 2 v)) ∧
      (pkGet JB.bD 5 v ≠ 1 → r.1 < 30 ∧ liftT (JU.uwT.getD (15 + r.1) []) r.2.1 = s ∧
        ∃ p, KT.find r.2.1 wt64Tree = p + 1 ∧ 0 < pkGet JB.bD 5 p ∧
          pkGet JB.bD 5 p < pkGet JB.bD 5 v ∧ pkGet JB.bK 2 p = pkGet JB.bK 2 v) ∧
      (pkGet JB.bK 2 v = 1 → ubWitK s r.2.2 = true)) := by
  obtain ⟨h1, h⟩ := band_true h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun hk => ?_⟩
  have h := (bIf_sound h).2 (ubBeqF hk)
  obtain ⟨h2, h⟩ := band_true h
  obtain ⟨h3, h⟩ := band_true h
  obtain ⟨h4, h5⟩ := band_true h
  obtain ⟨hA, hB⟩ := bIf_sound h4
  refine ⟨Nat.le_of_ble_eq_true h2, lt_of_blt h3, fun hd => ?_, fun hd => ?_, fun h1 => ?_⟩
  · exact Nat.eq_of_beq_eq_true (hA (by rw [hd]; rfl))
  · have h' := hB (ubBeqF hd)
    obtain ⟨g1, h'⟩ := band_true h'
    obtain ⟨g2, h'⟩ := band_true h'
    unfold ubParOK at h'
    obtain ⟨p1, h'⟩ := band_true h'
    obtain ⟨p2, h'⟩ := band_true h'
    obtain ⟨p3, p4⟩ := band_true h'
    refine ⟨lt_of_blt g1, Nat.eq_of_beq_eq_true g2, Nat.pred (KT.find r.2.1 wt64Tree), ?_,
      lt_of_blt p2, lt_of_blt p3, Nat.eq_of_beq_eq_true p4⟩
    exact (Nat.succ_pred_eq_of_pos (lt_of_blt p1)).symm
  · exact (bIf_sound h5).1 (by rw [h1]; rfl)

theorem ubKeysGo_sound : ∀ (l : List (Nat × Nat × Nat)), ubKeysGo l = true →
    ∀ r ∈ l, r.2.2 = 0 ∨ lineTree.memB r.2.2 = true
  | [], _ => by simp
  | r :: l, h => by
    have e : ubKeysGo (r :: l) =
        bAnd(bIf(Nat.beq r.2.2 0, true, lineTree.memB r.2.2), ubKeysGo l) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · by_cases h0 : x.2.2 = 0
      · exact Or.inl h0
      · exact Or.inr ((bIf_sound h1).2 (ubBeqF h0))
    · exact ubKeysGo_sound l h2 x hx

theorem ubKeysAll_sound : ∀ (cs : List (List (Nat × Nat × Nat))),
    List.rec (motive := fun _ => Bool) true (fun ch _ ih => bAnd(ubKeysGo ch, ih)) cs = true →
    ∀ ch ∈ cs, ∀ r ∈ ch, r.2.2 = 0 ∨ lineTree.memB r.2.2 = true
  | [], _ => by simp
  | ch :: cs, h => by
    obtain ⟨h1, h2⟩ := band_true h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ubKeysGo_sound x h1
    · exact ubKeysAll_sound cs h2 x hx

theorem ubKeysOK_sound (h : ubKeysOK = true) :
    ∀ ch ∈ JB.bRC, ∀ r ∈ ch, r.2.2 = 0 ∨ lineTree.memB r.2.2 = true :=
  ubKeysAll_sound JB.bRC h

theorem ubCnt_eq (c : Nat) :
    ubCnt c = ((List.range 75735).filter fun j => pkGet JB.bK 2 j == c).length := by
  unfold ubCnt
  rw [pkSumBelow_eq _ (by decide)]
  generalize 75735 = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.filter_append, List.length_append, ih]
    congr 1
    by_cases hn : pkGet JB.bK 2 n = c
    · have hb : Nat.beq (pkGet JB.bK 2 n) c = true := by
        rw [hn]
        exact Nat.beq_refl c
      rw [hb]
      simp [hn]
    · rw [ubBeqF hn]
      simp [hn]

end CFSG.KD.SmithD6

end
