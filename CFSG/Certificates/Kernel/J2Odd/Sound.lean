module

public import Certificates.Data.Kernel.J2Odd
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CFSG.KC.J2Odd.Pf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Enum
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

private theorem strictB_o (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem itP_succ (f : Nat → Nat) (k p : Nat) : itP f (k + 1) p = f (itP f k p) :=
  PF.strictN_eqP _ _

private theorem apPowW_itP {n : Nat} {W : List Table} {f : Nat → Nat}
    (hW : ∀ q < n, apW W q = f q) (hf : ∀ q < n, f q < n) {p : Nat} (hp : p < n) :
    ∀ k, apPowW W k p = itP f k p ∧ itP f k p < n
  | 0 => ⟨rfl, hp⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := apPowW_itP hW hf hp k
    rw [itP_succ]
    exact ⟨by rw [← hW _ h2, ← h1]; rfl, hf _ h2⟩

private theorem powFixW_false {n : Nat} {W : List Table} {f : Nat → Nat} {m p : Nat}
    (hW : ∀ q < n, apW W q = f q) (hf : ∀ q < n, f q < n) (hp : p < n)
    (hm : Nat.beq (itP f m p) p = false) : powFixW n W m = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [powFixW, CFSG.Sporadic.Th.allIn_eq_true] at h
  have := h p (Nat.zero_le _) hp
  rw [beq_iff_eq, (apPowW_itP hW hf hp m).1] at this
  rw [this] at hm
  exact Nat.ne_of_beq_eq_false hm rfl

private theorem pg_zero (w m j : Nat) : pg w m 0 j = 0 := by
  unfold pg
  simp

private theorem permOK_facts {n w p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    ∀ j < n, pg w (mask w) p j < n ∧ pg w (mask w) q (pg w (mask w) p j) = j := by
  unfold permOK at h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  intro j hj
  have := allN_spec h j hj
  rw [strictB_o] at this
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
  exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩

private theorem mem_of_permOK {n w : Nat} {L : List Nat} {k i : Nat} (hn : 1 < n)
    (h : permOK n w (mask w) (n * w) (lget L k) i = true) : lget L k ∈ L := by
  rw [lget_eq] at h ⊢
  by_cases hk : k < L.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  · exfalso
    rw [List.getD_eq_default _ _ (by omega)] at h
    have h0 := (permOK_facts h 0 (by omega)).2
    have h1 := (permOK_facts h 1 hn).2
    rw [pg_zero] at h0 h1
    omega

private theorem inv_facts {n w h i : Nat} (hn : n < 2 ^ 32)
    (hp : permOK n w (mask w) (n * w) h i = true) :
    (∀ q < n, ap (tabP n w h) q = pg w (mask w) h q ∧ pg w (mask w) h q < n) ∧
      invOK n (tabP n w h) (invT n (tabP n w h)) = true ∧
      ∀ q < n, ap (invT n (tabP n w h)) q = pg w (mask w) i q ∧ pg w (mask w) i q < n := by
  have hf := permOK_facts hp
  have ha : ∀ q < n, ap (tabP n w h) q = pg w (mask w) h q := fun q hq =>
    ap_tabP hq (by have := (hf q hq).1; omega)
  have hlt : ∀ q < n, ap (tabP n w h) q < n := fun q hq => by rw [ha q hq]; exact (hf q hq).1
  have hinj : ∀ q < n, ∀ q' < n, ap (tabP n w h) q = ap (tabP n w h) q' → q = q' := by
    intro q hq q' hq' e
    rw [ha q hq, ha q' hq'] at e
    rw [← (hf q hq).2, ← (hf q' hq').2, e]
  obtain ⟨-, hhit, -⟩ := CFSG.Sporadic.Th.foldl_set_inv (tabP n w h) hlt hinj n 0 (by omega)
    (Array.replicate n 0) (by simp)
  have hinv : ∀ q < n, ap (invT n (tabP n w h)) (ap (tabP n w h) q) = q := by
    intro q hq
    have := hhit q (Nat.zero_le _) (by omega)
    rw [← CFSG.Sporadic.Th.invT_eq_foldl] at this
    show ((invT n (tabP n w h))[ap (tabP n w h) q]!).toNat = q
    rw [this, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hsurj : ∀ r < n, ∃ q < n, ap (tabP n w h) q = r := by
    intro r hr
    let g : Fin n → Fin n := fun q => ⟨ap (tabP n w h) q, hlt q q.2⟩
    have gi : Function.Injective g := fun a b e =>
      Fin.ext (hinj a a.2 b b.2 (by have := congrArg Fin.val e; exact this))
    obtain ⟨q, hq⟩ := Finite.surjective_of_injective gi ⟨r, hr⟩
    exact ⟨q, q.2, congrArg Fin.val hq⟩
  refine ⟨fun q hq => ⟨ha q hq, (hf q hq).1⟩, ?_, fun r hr => ?_⟩
  · rw [invOK, CFSG.Sporadic.Th.allIn_eq_true]
    intro q _ hq
    rw [beq_iff_eq, hinv q hq]
  · obtain ⟨q, hq, rfl⟩ := hsurj r hr
    rw [hinv q hq, ha q hq, (hf q hq).2]
    exact ⟨rfl, hq⟩

private theorem ap_idT {n i : Nat} (hn : n < 2 ^ 32) (hi : i < n) : ap (idT n) i = i := by
  unfold ap idT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]

private theorem oddOne_sound {n w m : Nat} {L : List Nat} {X e : Nat} (hn : 1 < n)
    (hc : ∀ Y ∈ L, canonK n w (mask w) (n * w) Y = true)
    (hX : canonK n w (mask w) (n * w) X = true) (h : oddOne n w m L X e = true) :
    (tblEq n (tabP n w X) (idT n) || !powFixW n [tabP n w X] m ||
      (L.map (tabP n w)).any (fun h => let hi := invT n h; invOK n h hi &&
        !powFixW n [tabP n w X, h, tabP n w X, hi] m) ||
      (L.map (tabP n w)).any fun h₁ => let i₁ := invT n h₁; invOK n h₁ i₁ &&
        (L.map (tabP n w)).any fun h₂ => let i₂ := invT n h₂; invOK n h₂ i₂ &&
          !powFixW n [tabP n w X, h₁, tabP n w X, i₁, h₂, tabP n w X, i₂] m) = true := by
  obtain ⟨hn24, hw, -, hXr⟩ := PF.canon_facts hX
  have hn32 : n < 2 ^ 32 := by omega
  have hXa : ∀ q < n, ap (tabP n w X) q = pg w (mask w) X q := fun q hq =>
    ap_tabP hq (by have := hXr q hq; omega)
  unfold oddOne at h
  simp only [strictB_o] at h
  generalize Nat.land e 3 = t at h
  generalize Nat.land (Nat.shiftRight e 2) 511 = p at h
  generalize hk1 : Nat.land (Nat.shiftRight e 11) 2047 = k1 at h
  generalize hk2 : Nat.land (Nat.shiftRight e 22) 2047 = k2 at h
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  cases h0 : Nat.beq t 0
  · rw [h0] at h
    obtain ⟨hp, h⟩ := (bAnd_iff _ _).1 h
    have hp : p < n := Nat.blt_eq.mp hp
    cases h1c : Nat.beq t 1
    · rw [h1c] at h
      obtain ⟨hP1, h⟩ := (bAnd_iff _ _).1 h
      have hmem1 := mem_of_permOK hn hP1
      obtain ⟨hA1, hI1, hB1⟩ := inv_facts hn32 hP1
      have hW1 : tabP n w (lget L k1) ∈ L.map (tabP n w) := List.mem_map_of_mem hmem1
      cases h2c : Nat.beq t 2
      · rw [h2c] at h
        obtain ⟨hP2, h⟩ := (bAnd_iff _ _).1 h
        have hmem2 := mem_of_permOK hn hP2
        obtain ⟨hA2, hI2, hB2⟩ := inv_facts hn32 hP2
        have hW2 : tabP n w (lget L k2) ∈ L.map (tabP n w) := List.mem_map_of_mem hmem2
        cases hq : Nat.beq (itP (fun q => pg w (mask w) X (pg w (mask w) (lget L k1)
            (pg w (mask w) X (pg w (mask w) (pinvS n w (mask w) (lget L k1))
            (pg w (mask w) (lget L k2) (pg w (mask w) X
            (pg w (mask w) (pinvS n w (mask w) (lget L k2)) q))))))) m p) p
        · have hpow := powFixW_false (n := n)
            (W := [tabP n w X, tabP n w (lget L k1), tabP n w X, invT n (tabP n w (lget L k1)),
              tabP n w (lget L k2), tabP n w X, invT n (tabP n w (lget L k2))])
            (fun q hq => by
              obtain ⟨e1, l1⟩ := hB2 q hq
              have e2 := hXa _ l1
              have l2 := hXr _ l1
              obtain ⟨e3, l3⟩ := hA2 _ l2
              obtain ⟨e4, l4⟩ := hB1 _ l3
              have e5 := hXa _ l4
              have l5 := hXr _ l4
              obtain ⟨e6, l6⟩ := hA1 _ l5
              show ap _ (ap _ (ap _ (ap _ (ap _ (ap _ (ap _ q)))))) = _
              rw [e1, e2, e3, e4, e5, e6, hXa _ l6])
            (fun q hq => hXr _ (hA1 _ (hXr _ (hB1 _ (hA2 _ (hXr _ (hB2 q hq).2)).2).2)).2)
            hp hq
          right
          rw [List.any_eq_true]
          refine ⟨_, hW1, ?_⟩
          rw [Bool.and_eq_true, List.any_eq_true]
          exact ⟨hI1, _, hW2, by rw [Bool.and_eq_true]; exact ⟨hI2, by rw [hpow]; rfl⟩⟩
        · rw [hq] at h
          exact (Bool.false_ne_true h).elim
      · rw [h2c] at h
        cases hq : Nat.beq (itP (fun q => pg w (mask w) X (pg w (mask w) (lget L k1)
            (pg w (mask w) X (pg w (mask w) (pinvS n w (mask w) (lget L k1)) q)))) m p) p
        · have hpow := powFixW_false (n := n)
            (W := [tabP n w X, tabP n w (lget L k1), tabP n w X, invT n (tabP n w (lget L k1))])
            (fun q hq => by
              obtain ⟨e1, l1⟩ := hB1 q hq
              have e2 := hXa _ l1
              have l2 := hXr _ l1
              obtain ⟨e3, l3⟩ := hA1 _ l2
              show ap _ (ap _ (ap _ (ap _ q))) = _
              rw [e1, e2, e3, hXa _ l3])
            (fun q hq => hXr _ (hA1 _ (hXr _ (hB1 q hq).2)).2) hp hq
          left; right
          rw [List.any_eq_true]
          exact ⟨_, hW1, by rw [Bool.and_eq_true]; exact ⟨hI1, by rw [hpow]; rfl⟩⟩
        · rw [hq] at h
          exact (Bool.false_ne_true h).elim
    · rw [h1c] at h
      cases hq : Nat.beq (itP (fun q => pg w (mask w) X q) m p) p
      · have hpow := powFixW_false (n := n) (W := [tabP n w X]) (f := fun q => pg w (mask w) X q)
          (fun q hq => hXa q hq) (fun q hq => hXr q hq) hp hq
        left; left; right
        rw [hpow]; rfl
      · rw [hq] at h
        exact (Bool.false_ne_true h).elim
  · rw [h0] at h
    have hXe : X = pidn n w := Nat.eq_of_beq_eq_true h
    left; left; left
    rw [tblEq, CFSG.Sporadic.Th.allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hXa i hi, hXe, PF.pg_pidn hn24 hw hi, ap_idT hn32 hi]

private theorem oddK_rec {n w m : Nat} {L : List Nat} :
    ∀ (L' W : List Nat), List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
      (fun x _ ih W => bAnd(oddOne n w m L x (lget W 0),
        ih (List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) W))) L' W = true →
      ∀ X ∈ L', ∃ e, oddOne n w m L X e = true
  | [], _, _, X, hX => by simp at hX
  | x :: L', W, h, X, hX => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hX with rfl | hX
    · exact ⟨_, h1⟩
    · exact oddK_rec L' _ h2 X hX

theorem oddK_sound' {n w m : Nat} {L W : List Nat} (hn : 1 < n)
    (hc : ∀ X ∈ L, canonK n w (mask w) (n * w) X = true) (h : oddK n w m L W = true) :
    oddWitnessOK n m (L.map fun X => arrTable n (unpack n w X)) = true := by
  rw [oddWitnessOK, List.all_eq_true]
  intro x hx
  obtain ⟨X, hXL, rfl⟩ := List.mem_map.1 hx
  obtain ⟨e, he⟩ := oddK_rec L W h X hXL
  exact oddOne_sound hn hc (hc X hXL) he

end CFSG.KC.J2Odd.Pf

end
