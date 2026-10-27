module

public import Certificates.Data.Kernel.Spor.PEnumT
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.HBfsReplayT
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Monster.B.Co2.Native CFSG.KS.BfsReplay

theorem penumPtT_spec {n w m nw k cnt cap i : Nat} {conj : Bool}
    {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtTK n w m nw conj G GI k cnt cap T PL POS SRT SRI i = true) :
    canonK n w m nw (T i) = true ∧
    (i ≠ 0 → parOf PL i < i ∧ parOf PL i < cap ∧ labOf PL i < k ∧
      T i = stepK n w m conj G GI (labOf PL i) (T (parOf PL i)) ∧
      (i + 1 < cnt → LexLt (parOf PL i) (labOf PL i) (parOf PL (i + 1)) (labOf PL (i + 1)))) ∧
    (i < cap → ∀ j < k, r32 POS (i * k + j) < cnt ∧
      T (r32 POS (i * k + j)) = stepK n w m conj G GI j (T i) ∧
      (r32 POS (i * k + j) = 0 ∨
        ¬ LexLt i j (parOf PL (r32 POS (i * k + j))) (labOf PL (r32 POS (i * k + j))))) := by
  unfold penumPtTK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hc, ht, hpos, -⟩ := h
  refine ⟨hc, fun hi => ?_, fun hic j hj => ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, Bool.and_eq_true,
      Nat.blt_eq] at ht
    obtain ⟨h1, h1', h2, h3, h4⟩ := ht
    refine ⟨h1, h1', h2, Nat.eq_of_beq_eq_true h3, fun hc => ?_⟩
    have hc' : Nat.succ i < cnt := hc
    simp only [hc', ↓reduceIte] at h4
    exact lexLtK_iffH.1 h4
  · have hb : Nat.blt i cap = true := Nat.blt_eq.mpr hic
    rw [CFSG.KS.Raw.Orb.bIf_eq, hb] at hpos
    simp only [↓reduceIte] at hpos
    have hq := allN_spec hpos j hj
    simp only [CFSG.KS.Raw.Orb.strictB_eq, Nat.mul_eq, Nat.add_eq, Bool.and_eq_true,
      Nat.blt_eq] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨h1, Nat.eq_of_beq_eq_true h2, ?_⟩
    by_cases h0 : r32 POS (i * k + j) = 0
    · exact Or.inl h0
    · right
      have e : Nat.beq (r32 POS (i * k + j)) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [e] at h3
      intro hl
      rw [← lexLtK_iffH] at hl
      rw [hl] at h3
      exact absurd h3 (by decide)

theorem mulTreeT_of {n cnt cap : Nat} {gens : Array Table} {key : Table → UInt64}
    {U : Nat → Table} {par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (R : CFSG.KS.HBfs.HReplayT key (fun j y => compT n y gens[j]!) gens.size (idT n) cnt cap U
      par lab pos) :
    mulTreeOK n gens (Array.ofFn (n := cnt) fun i => U i.val)
      (Array.ofFn (n := cnt) fun i => par i.val) (Array.ofFn (n := cnt) fun i => lab i.val) =
        true := by
  unfold mulTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.size_ofFn]
  refine ⟨⟨R.pos_cnt, ?_⟩, allInH_of fun i h1 h2 => ?_⟩
  · rw [ofFnH_get _ R.pos_cnt, R.root_eq]
    exact tblEqH_self n _
  · obtain ⟨a1, a2, a3⟩ := R.tree i (by omega) h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [ofFnH_get _ h2, ofFnH_get _ h2, ofFnH_get _ h2, ofFnH_get _ (by omega), ← a3]
    exact ⟨⟨a1, a2⟩, tblEqH_self n _⟩

theorem mulHT_sound {n w k cnt cap : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {gens : Array Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gens) (hh : penumHdTK (pidn n w) cnt T PL = true)
    (hp : ∀ i < cnt, penumPtTK n w (mask w) (n * w) true G GI k cnt cap T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    mulClosureH n gens cap = hRec n w cnt T PL ∧
      mulTreeOK n gens (hRec n w cnt T PL).1 (hRec n w cnt T PL).2.1 (hRec n w cnt T PL).2.2 =
        true ∧
      hkeysDistinct n (hRec n w cnt T PL).1.toList = true := by
  obtain ⟨hk, hgj⟩ := hg
  have hid := (CFSG.KC.BfsPin.PP.id hn).1
  have sp := fun i (hi : i < cnt) => penumPtT_spec (hp i hi)
  have hstep : ∀ j < k, ∀ t, canonK n w (mask w) (n * w) t = true →
      tabT (unpack n w (stepK n w (mask w) true G GI j t)) =
        compT n (tabT (unpack n w t)) gens[j]! := by
    intro j hj t ht
    have e : unpack n w (stepK n w (mask w) true G GI j t) =
        compA n (unpack n w t) (unpack n w (GI j)) := by
      change unpack n w (pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j)) = _
      rw [hG j hj, ← CFSG.KC.BfsPin.compA_unpack (CFSG.KC.BfsPin.canonK_pcomp hid ht)
        (hgj j hj).2, ← CFSG.KC.BfsPin.compA_unpack hid ht, ← CFSG.KC.BfsPin.idA_eq hn,
        compA_idA_unpack ht]
    rw [e, (hgj j hj).1, compT_tabT _ _ fun x _ => unpack_lt (hgj j hj).2]
  unfold penumHdTK at hh
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hh
  obtain ⟨hc0, hT0, hPL0⟩ := hh
  have R : CFSG.KS.HBfs.HReplayT (hkey n) (fun j y => compT n y gens[j]!) gens.size (idT n) cnt cap
      (fun i => tabT (unpack n w (T i))) (parOf PL) (labOf PL) (fun h j => r32 POS (h * k + j)) := by
    refine ⟨hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change tabT (unpack n w (T 0)) = idT n
      rw [Nat.eq_of_beq_eq_true hT0, idT_tabT n, CFSG.KC.BfsPin.idA_eq hn]
    · unfold parOf
      rw [Nat.eq_of_beq_eq_true hPL0]
      rfl
    · unfold labOf
      rw [Nat.eq_of_beq_eq_true hPL0]
      rfl
    · intro a ha b hb e
      refine hkeyK_inj hs a ha b hb ?_
      rw [← hkey_tabT (sp a ha).1, ← hkey_tabT (sp b hb).1, e]
    · intro i hi0 hi
      obtain ⟨h1, -, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
      refine ⟨h1, by rw [hk]; exact h2, ?_⟩
      change tabT (unpack n w (T i)) = compT n (tabT (unpack n w (T (parOf PL i)))) gens[labOf PL i]!
      rw [← hstep _ h2 _ (sp _ (by omega)).1, ← h3]
    · intro i hi0 hi
      exact ((sp i hi).2.1 (by omega)).2.1
    · intro i hi0 hi
      exact ((sp i (by omega)).2.1 (by omega)).2.2.2.2 hi
    · intro h hh hc j hj
      rw [hk] at hj
      obtain ⟨h1, h2, h3⟩ := (sp h hh).2.2 hc j hj
      refine ⟨h1, ?_, h3⟩
      change compT n (tabT (unpack n w (T h))) gens[j]! = tabT (unpack n w (T (r32 POS (h * k + j))))
      rw [← hstep _ hj _ (sp h hh).1, h2]
  have e1 : mulClosureH n gens cap =
      CFSG.KS.HBfs.hbfs (hkey n) (fun l y => compT n y gens[l]!) gens.size (idT n) cap := rfl
  unfold hRec
  refine ⟨e1.trans (CFSG.KS.HBfs.hbfs_replayT R), ?_, ?_⟩
  · have hm := mulTreeT_of R
    change mulTreeOK n gens (Array.ofFn (n := cnt) fun i => tabT (unpack n w (T i.val)))
      (Array.ofFn (n := cnt) fun i => parOf PL i.val)
      (Array.ofFn (n := cnt) fun i => labOf PL i.val) = true
    exact hm
  · exact hkeysDistinct_ofFn fun a ha b hb e => R.kinj a ha b hb (UInt64.toNat_inj.1 e)

end CFSG.KS.MulH

end
