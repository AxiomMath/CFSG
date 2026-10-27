module

public import Certificates.Data.Kernel.Spor.KEnum
public import CFSG.Certificates.Kernel.Spor.FpBfsSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KS.KEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs CFSG.KS.KeyBfsG
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo

theorem mul_add_lt {k a b c : Nat} (ha : a < c) (hb : b < k) : k * a + b < k * c := by
  have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt ha)
  rw [Nat.mul_succ] at this
  omega

theorem kenumK_sound {k kk cnt cap R : Nat} {G T TI PL POS FP SRT SRI : Nat → Nat}
    {gens : Array (Array Nat)} {root : Array Nat}
    (hg : ∀ s < kk, gens[s]! = unpack 1782 11 (G s)) (hr : root = unpack 1782 11 R)
    (hh : kenumHdK 1782 11 (mask 11) (1782 * 11) k kk cnt R G T = true)
    (hp : ∀ i < cnt,
      kenumPtK 1782 11 (mask 11) (1782 * 11) k kk cnt G T TI PL POS FP SRT SRI i = true)
    (hcap : cnt ≤ cap) :
    keyBfsG fp (fun s x => compA 1782 gens[s]! x) k root (fp root) cap =
        (Array.ofFn (n := cnt) fun i => unpack 1782 11 (T i.val),
          Array.ofFn (n := cnt) fun i => if i.val = 0 then 0 else PL i.val / k,
          Array.ofFn (n := cnt) fun i => if i.val = 0 then 0 else PL i.val % k) ∧
      (∀ i < cnt, ∀ s < kk, POS (kk * i + s) < cnt ∧
        compA 1782 gens[s]! (unpack 1782 11 (T i)) = unpack 1782 11 (T (POS (kk * i + s)))) ∧
      (∀ i < cnt, invCand 1782 (unpack 1782 11 (T i)) = unpack 1782 11 (TI i) ∧
        isInvA 1782 (unpack 1782 11 (T i)) (unpack 1782 11 (TI i)) = true) ∧
      (∀ a < cnt, ∀ b < cnt, fp (unpack 1782 11 (T a)) = fp (unpack 1782 11 (T b)) → a = b) ∧
      (∀ i < cnt, 0 < i → PL i / k < i ∧ PL i % k < k ∧
        compA 1782 gens[PL i % k]! (unpack 1782 11 (T (PL i / k))) = unpack 1782 11 (T i)) ∧
      (∀ i < cnt, canonK 1782 11 (mask 11) (1782 * 11) (T i) = true) ∧
      (∀ s < kk, canonK 1782 11 (mask 11) (1782 * 11) (G s) = true) := by
  unfold kenumHdK at hh
  simp only [bAnd_iff] at hh
  obtain ⟨hk0, hkk, hc0, hT0, hcG⟩ := hh
  have hk0 := blt_true hk0
  have hkk : k ≤ kk := by simpa [Nat.ble_eq] using hkk
  have hc0 := blt_true hc0
  have hT0 : T 0 = R := Nat.eq_of_beq_eq_true hT0
  have hcG : ∀ s < kk, canonK 1782 11 (mask 11) (1782 * 11) (G s) = true :=
    fun s hs => allN_spec hcG s hs
  have sp : ∀ i < cnt, canonK 1782 11 (mask 11) (1782 * 11) (T i) = true ∧
      permOK 1782 11 (mask 11) (1782 * 11) (T i) (TI i) = true ∧
      FP i = fpK 11 (mask 11) (T i) ∧
      (i ≠ 0 → PL i / k < i ∧ POS (kk * (PL i / k) + PL i % k) = i ∧
        (i + 1 < cnt → PL i < PL (i + 1))) ∧
      (∀ s < kk, POS (kk * i + s) < cnt ∧
        T (POS (kk * i + s)) = pcomp 1782 11 (mask 11) (G s) (T i) ∧
        (s < k → POS (kk * i + s) = 0 ∨ PL (POS (kk * i + s)) ≤ k * i + s)) ∧
      (SRI i < cnt ∧ SRT (SRI i) = i) ∧
      (SRT i < cnt ∧ (i + 1 < cnt → FP (SRT i) < FP (SRT (i + 1)))) := by
    intro i hi
    have h := hp i hi
    unfold kenumPtK at h
    simp only [strictB_eq, bAnd_iff] at h
    obtain ⟨a1, a2, a3, a4, a5, ⟨a6, a7⟩, a8, -, a9⟩ := h
    refine ⟨a1, a2, Nat.eq_of_beq_eq_true a3, fun h0 => ?_, fun s hs => ?_,
      ⟨blt_true a6, Nat.eq_of_beq_eq_true a7⟩, blt_true a8, fun h1 => ?_⟩
    · have hz : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
      rw [hz] at a4
      simp only [bAnd_iff] at a4
      obtain ⟨b1, b2, b3⟩ := a4
      refine ⟨blt_true b1, Nat.eq_of_beq_eq_true b2, fun h1 => ?_⟩
      have hb : Nat.blt (Nat.succ i) cnt = true := by simpa [Nat.blt_eq] using h1
      rw [hb] at b3
      exact blt_true b3
    · have h := allN_spec a5 s hs
      simp only [bAnd_iff] at h
      obtain ⟨b1, b2, b3⟩ := h
      refine ⟨blt_true b1, Nat.eq_of_beq_eq_true b2, fun hsk => ?_⟩
      have hb : Nat.blt s k = true := by simpa [Nat.blt_eq] using hsk
      rw [hb] at b3
      by_cases hz : POS (kk * i + s) = 0
      · exact Or.inl hz
      · have hz' : Nat.beq (POS (Nat.add (Nat.mul kk i) s)) 0 = false :=
          Bool.eq_false_iff.2 fun e => hz (Nat.eq_of_beq_eq_true e)
        rw [hz'] at b3
        exact Or.inr (by simpa [Nat.ble_eq] using b3)
    · have hb : Nat.blt (Nat.succ i) cnt = true := by simpa [Nat.blt_eq] using h1
      rw [hb] at a9
      exact blt_true a9
  have hmul : ∀ i < cnt, ∀ s < kk, POS (kk * i + s) < cnt ∧
      compA 1782 gens[s]! (unpack 1782 11 (T i)) = unpack 1782 11 (T (POS (kk * i + s))) :=
    fun i hi s hs => ⟨((sp i hi).2.2.2.2.1 s hs).1, by
      rw [hg s hs, CFSG.KC.BfsPin.compA_unpack (hcG s hs) (sp i hi).1,
        ((sp i hi).2.2.2.2.1 s hs).2.1]⟩
  have hsort : ∀ j j', j < j' → j' < cnt → FP (SRT j) < FP (SRT j') := by
    intro j j' hj hj'
    induction j' with
    | zero => omega
    | succ j' ih =>
      rcases Nat.lt_or_ge j j' with a | a
      · exact Nat.lt_trans (ih a (by omega)) ((sp j' (by omega)).2.2.2.2.2.2.2 hj')
      · have e : j = j' := by omega
        subst e
        exact (sp j (by omega)).2.2.2.2.2.2.2 hj'
  have hinj : ∀ a < cnt, ∀ b < cnt, fp (unpack 1782 11 (T a)) = fp (unpack 1782 11 (T b)) →
      a = b := by
    intro a ha b hb e
    rw [fp_unpack, fp_unpack, ← (sp a ha).2.2.1, ← (sp b hb).2.2.1] at e
    obtain ⟨ra, ea⟩ := (sp a ha).2.2.2.2.2.1
    obtain ⟨rb, eb⟩ := (sp b hb).2.2.2.2.2.1
    rw [← ea, ← eb] at e
    rcases Nat.lt_trichotomy (SRI a) (SRI b) with c | c | c
    · exact absurd e (Nat.ne_of_lt (hsort _ _ c rb))
    · rw [← ea, ← eb, c]
    · exact absurd e (Nat.ne_of_gt (hsort _ _ c ra))
  have hdm : ∀ c, k * (c / k) + c % k = c := fun c => Nat.div_add_mod c k
  have Rec : GRec fp (fun s x => compA 1782 gens[s]! x) k root (fp root) cnt (k * cnt)
      (fun i => unpack 1782 11 (T i)) (fun i => if i = 0 then 0 else PL i / k)
      (fun i => if i = 0 then 0 else PL i % k) (fun e => POS (kk * (e / k) + e % k)) := by
    refine ⟨hk0, hc0, by rw [hT0, hr], rfl, by simp, by simp, hinj, fun i h0 hi => ?_,
      fun i h0 hi => ?_, ?_, fun e he => ?_⟩
    · obtain ⟨b1, b2, -⟩ := (sp i hi).2.2.2.1 (by omega)
      have hs : PL i % k < k := Nat.mod_lt _ hk0
      simp only [Nat.pos_iff_ne_zero.1 h0, ↓reduceIte]
      refine ⟨b1, hs, ?_⟩
      have := (hmul (PL i / k) (by omega) (PL i % k) (by omega)).2
      rw [b2] at this
      exact this.symm
    · have h1 : i + 1 ≠ 0 := by omega
      simp only [Nat.pos_iff_ne_zero.1 h0, h1, ↓reduceIte, hdm]
      exact ((sp i (by omega)).2.2.2.1 (by omega)).2.2 hi
    · by_cases h1 : cnt - 1 = 0
      · simp only [h1, ↓reduceIte]
        have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hc0)
        omega
      · simp only [h1, ↓reduceIte]
        exact mul_add_lt (((sp (cnt - 1) (by omega)).2.2.2.1 h1).1.trans (by omega))
          (Nat.mod_lt _ hk0)
    · have hed : e / k < cnt := (Nat.div_lt_iff_lt_mul hk0).2 (by rw [Nat.mul_comm]; exact he)
      have hek : e % k < k := Nat.mod_lt _ hk0
      obtain ⟨c1, c2⟩ := hmul (e / k) hed (e % k) (by omega)
      refine ⟨c1, by rw [c2], ?_⟩
      rcases ((sp (e / k) hed).2.2.2.2.1 (e % k) (by omega)).2.2 hek with z | z
      · exact Or.inl z
      · by_cases hz : POS (kk * (e / k) + e % k) = 0
        · exact Or.inl hz
        · right
          simp only [hz, ↓reduceIte, hdm]
          rw [hdm e] at z
          exact z
  have hcap' : (if cnt - 1 = 0 then 0 else PL (cnt - 1) / k) < cap := by
    by_cases h1 : cnt - 1 = 0
    · simp only [h1, ↓reduceIte]
      omega
    · simp only [h1, ↓reduceIte]
      have := ((sp (cnt - 1) (by omega)).2.2.2.1 h1).1
      omega
  obtain ⟨-, r2, r3, r4, r5⟩ := keyBfsG_rec Rec hcap'
  have hsz := r3 (Nat.le_refl _)
  have ext : ∀ {α : Type} [Inhabited α] (a : Array α) (f : Nat → α), a.size = cnt →
      (∀ i < cnt, a[i]! = f i) → a = Array.ofFn (n := cnt) fun i => f i.val :=
    fun a f ha hf => by
      apply Array.ext
      · simp [ha]
      · intro i h1 h2
        rw [Array.getElem_ofFn, ← getElem!_pos a i h1, hf i (by omega)]
  refine ⟨?_, hmul, fun i hi => CFSG.KS.Prim.invEqK_sound (sp i hi).2.1, hinj,
    fun i hi h0 => ?_, fun i hi => (sp i hi).1, hcG⟩
  swap
  · obtain ⟨b1, b2, -⟩ := (sp i hi).2.2.2.1 (by omega)
    have hs : PL i % k < k := Nat.mod_lt _ hk0
    have := (hmul (PL i / k) (by omega) (PL i % k) (by omega)).2
    rw [b2] at this
    exact ⟨b1, hs, this⟩
  generalize keyBfsG fp (fun s x => compA 1782 gens[s]! x) k root (fp root) cap = S at hsz r2 r4 r5
  obtain ⟨S1, S2, S3⟩ := S
  simp only at hsz r2 r4 r5
  rw [ext S1 _ hsz fun i hi => (r2 i hi).1, ext S2 _ (r4.trans hsz) fun i hi => (r2 i hi).2.1,
    ext S3 _ (r5.trans hsz) fun i hi => (r2 i hi).2.2]

end CFSG.KS.KEnum

end
