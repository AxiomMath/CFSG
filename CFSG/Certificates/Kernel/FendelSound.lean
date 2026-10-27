module

public import Certificates.Data.Kernel.Fendel
import CFSG.Certificates.Kernel.Spor.LevelTrSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.HexText
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Fendel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KS.HexText
open CFSG.KS.Text (hexV)

theorem levelTr_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {i k : Nat} (hi : i < nb)
    (hk : k < rcnt (LR i)) :
    ((rawLevels n S base)[i]!).tr[k]! = unpack n w (TR (roff n (n * w) (LR i) + k)) := by
  have hbl := Orb.base_lt_of_levels hb hl
  obtain ⟨A, P⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  have e : (rawLevels n S base)[i]! = CFSG.Certificates.ChainArrays.lev n S base i := rfl
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hk' : k < (CFSG.Certificates.ChainArrays.lev n S base i).pts.size := by
    rw [← A.cnt]
    exact hk
  have R := (A.tr k hk').1
  have Q := Orb.rep_unpack (P k hk).1
  have hsz : ((rawLevels n S base)[i]!.tr[k]!).size = n := by
    have hk2 : k < (rawLevels n S base)[i]!.pts.size := hk'
    rw [rawLevels_get (by omega)] at hk2 ⊢
    exact bfs_tr_size hk2
  rw [e] at hsz ⊢
  apply Array.ext
  · rw [hsz, unpack, Array.size_ofFn]
  · intro x h1 h2
    have hx : x < n := by rwa [hsz] at h1
    rw [← getElem!_pos _ x h1, ← getElem!_pos _ x h2, R ⟨x, hx⟩]
    exact (Q ⟨x, hx⟩).symm

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem run_cons (w : Nat) (ch : Char) (cs : List Char) (L : List Nat) (t v : Nat) :
    hexTabRun w (ch :: cs) L t v = strictB (hexV (Char.toNat ch)) (fun h =>
      bIf(Nat.blt h (nat_lit 16), strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) w,
          List.rec (motive := fun _ => Bool) false
            (fun x xs _ => bAnd(Nat.beq v' x, hexTabRun w cs xs (nat_lit 0) (nat_lit 0))) L,
          hexTabRun w cs L (Nat.succ t) v')),
      false)) := rfl

private theorem numA_cons (ch : Char) (cs : List Char) :
    ∀ m, numA (ch :: cs) 0 (m + 1) = hexV (Char.toNat ch) * 16 ^ m + numA cs 0 m
  | 0 => by simp [numA]
  | m + 1 => by
    rw [numA, numA_cons ch cs m, numA]
    simp only [Nat.zero_add, List.getElem!_cons_succ]
    rw [Nat.pow_succ]
    ring

private theorem getElem!_drop' (cs : List Char) (m k : Nat) : (cs.drop m)[k]! = cs[m + k]! := by
  simp only [getElem!_def, List.getElem?_drop]

private theorem numA_drop' (cs : List Char) (m o : Nat) :
    ∀ c, numA (cs.drop m) o c = numA cs (m + o) c
  | 0 => rfl
  | c + 1 => by
    simp only [numA]
    rw [numA_drop' cs m o c, getElem!_drop', Nat.add_assoc]

private theorem entry (w x : Nat) (xs : List Nat) : ∀ (cs : List Char) (t v : Nat), t < w →
    hexTabRun w cs (x :: xs) t v = true →
    w - t ≤ cs.length ∧ (∀ s < w - t, hexV (Char.toNat cs[s]!) < 16) ∧
      x = v * 16 ^ (w - t) + numA cs 0 (w - t) ∧ hexTabRun w (cs.drop (w - t)) xs 0 0 = true
  | [], t, v, _, h => by
    change Bool.rec (motive := fun _ => Bool) false false (Nat.beq t 0) = true at h
    revert h
    cases Nat.beq t 0 <;> simp
  | ch :: cs, t, v, ht, h => by
    rw [run_cons, strictB_eq'] at h
    cases hb : Nat.blt (hexV (Char.toNat ch)) 16
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    simp only [hb, strictB_eq'] at h
    have hb' : hexV (Char.toNat ch) < 16 := Nat.blt_eq.mp hb
    cases he : Nat.beq (Nat.succ t) w
    · simp only [he] at h
      have hne : t + 1 ≠ w := Nat.ne_of_beq_eq_false he
      obtain ⟨h1, h2, h3, h4⟩ := entry w x xs cs (t + 1) _ (by omega) h
      have em : w - t = (w - (t + 1)) + 1 := by omega
      rw [em]
      refine ⟨by simp; omega, fun s hs => ?_, ?_, ?_⟩
      · cases s with
        | zero => simpa using hb'
        | succ s =>
          simp only [List.getElem!_cons_succ]
          exact h2 s (by omega)
      · rw [h3, numA_cons, Nat.pow_succ]
        change (v * 16 + hexV (Char.toNat ch)) * 16 ^ (w - (t + 1)) + _ = _
        ring
      · rw [List.drop_succ_cons]
        exact h4
    · simp only [he] at h
      have e : t + 1 = w := Nat.eq_of_beq_eq_true he
      change Bool.rec (motive := fun _ => Bool) false (hexTabRun w cs xs 0 0)
        (Nat.beq (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) x) = true at h
      obtain ⟨hx, hr⟩ := (bAnd_iff _ _).1 h
      have em : w - t = 1 := by omega
      rw [em]
      refine ⟨by simp, fun s hs => ?_, ?_, by simpa using hr⟩
      · have : s = 0 := by omega
        subst this
        simpa using hb'
      · rw [← Nat.beq_eq.mp hx]
        simp [numA]

private theorem run_nil (w : Nat) : ∀ (cs : List Char) (t v : Nat), t < w →
    hexTabRun w cs [] t v = true → cs = []
  | [], _, _, _, _ => rfl
  | ch :: cs, t, v, ht, h => by
    rw [run_cons, strictB_eq'] at h
    cases hb : Nat.blt (hexV (Char.toNat ch)) 16
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    simp only [hb, strictB_eq'] at h
    cases he : Nat.beq (Nat.succ t) w
    · simp only [he] at h
      have hne : t + 1 ≠ w := Nat.ne_of_beq_eq_false he
      have hc := run_nil w cs (t + 1) _ (by omega) h
      subst hc
      exact absurd h Bool.false_ne_true
    · rw [he] at h
      exact absurd h Bool.false_ne_true

private theorem table (w : Nat) (hw : 0 < w) : ∀ (L : List Nat) (cs : List Char),
    hexTabRun w cs L 0 0 = true →
    cs.length = w * L.length ∧ (∀ k < cs.length, hexV (Char.toNat cs[k]!) < 16) ∧
      ∀ j < L.length, numA cs (w * j) w = L[j]!
  | [], cs, h => by
    have := run_nil w cs 0 0 hw h
    subst this
    exact ⟨rfl, fun k hk => absurd hk (by simp), fun j hj => absurd hj (by simp)⟩
  | x :: xs, cs, h => by
    obtain ⟨h1, h2, h3, h4⟩ := entry w x xs cs 0 0 hw h
    rw [Nat.sub_zero] at h1 h2 h3 h4
    obtain ⟨g1, g2, g3⟩ := table w hw xs (cs.drop w) h4
    rw [List.length_drop] at g1 g2
    refine ⟨by simp only [List.length_cons]; rw [Nat.mul_succ]; omega, fun k hk => ?_,
      fun j hj => ?_⟩
    · by_cases hkw : k < w
      · exact h2 k hkw
      · have := g2 (k - w) (by omega)
        rwa [getElem!_drop', Nat.add_sub_cancel' (by omega)] at this
    · cases j with
      | zero => simpa [Nat.zero_mul] using h3.symm
      | succ j =>
        have := g3 j (by simpa using hj)
        rw [numA_drop'] at this
        rw [Nat.mul_succ, Nat.add_comm (w * j) w, this]
        simp

theorem hexTab_sound {w : Nat} {L : List Nat} {cs : List Char} (h : hexTabK w L cs = true) :
    hexTable w L.length 0 (String.ofList cs) = L.toArray := by
  unfold hexTabK at h
  obtain ⟨hw, hr⟩ := (bAnd_iff _ _).1 h
  have hw' : 0 < w := Nat.blt_eq.mp hw
  obtain ⟨hlen, hdig, hval⟩ := table w hw' L cs hr
  have hasc : ∀ k < cs.length, k < cs.length ∧ (cs[k]!).toNat < 128 := fun k hk =>
    ⟨hk, by rcases hexV_dig (hdig k hk) with ⟨_, a, _⟩ | ⟨_, a, _⟩ <;> omega⟩
  apply Array.ext
  · simp [hexTable]
  · intro i h1 _
    have hi : i < L.length := by simpa [hexTable] using h1
    simp only [hexTable, Array.getElem_ofFn, List.getElem_toArray, Nat.zero_add]
    have hle : w * i + w ≤ cs.length := by
      rw [hlen, ← Nat.mul_succ]
      exact Nat.mul_le_mul_left w hi
    rw [num_bytes (o := w * i) hasc (fun c => hexAt (String.ofList cs).toUTF8 (w * i) c) rfl
      (fun c => rfl) w hle (fun s hs => hdig _ (by omega)), hval i hi,
      getElem!_pos L i hi]

end CFSG.KC.Fendel

end
