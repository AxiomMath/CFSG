module

public import Certificates.Data.Kernel.B0SuzK
public import CFSG.Certificates.Kernel.HexaKGlue
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatTypeInputs
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.B0SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

theorem szOK_1782 : szOK 1782 11 = true := rfl

theorem idTab_eq_idA (n : Nat) : idTab n = idA n := rfl

attribute [local irreducible] unpack compA idA idTab

theorem allBelow_iff {m : Nat} {f : Nat → Bool} :
    CFSG.PSL3Four.Native.allBelow m f = true ↔ ∀ i < m, f i = true := by
  simp [CFSG.PSL3Four.Native.allBelow, List.all_eq_true]

theorem eqA_self (n : Nat) (t : Array Nat) : eqA n t t = true := by
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  simp

theorem compA_assoc {n : Nat} (a b e : Array Nat) (hc : ∀ i < n, e[i]! < n) :
    compA n (compA n a b) e = compA n a (compA n b e) := by
  have hs : ∀ x y : Array Nat, (compA n x y).size = n := fun x y => by simp [compA]
  apply Array.ext (by rw [hs, hs])
  intro i h1 h2
  have hi : i < n := by rwa [hs] at h1
  rw [← getElem!_pos (compA n (compA n a b) e) i h1, ← getElem!_pos (compA n a (compA n b e)) i h2,
    CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get (hc i hi),
    CFSG.Monster.B.Co2.compA_get hi, CFSG.Monster.B.Co2.compA_get hi]

theorem PP_get_lt {n w p : Nat} (hp : PP n w p) {i : Nat} (hi : i < n) :
    (unpack n w p)[i]! < n := by
  rw [unpack_getElem!, if_pos hi]
  exact hp.2.1 i hi

theorem idTab_unpack : idTab 1782 = unpack 1782 11 (pidn 1782 11) :=
  (idTab_eq_idA 1782).trans (idA_eq szOK_1782)

theorem permOK_unpack {p : Nat} (hp : PP 1782 11 p) :
    CFSG.Sporadic.SuzOddCore.permOK 1782 (unpack 1782 11 p) = true := by
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [invCand_PP hp, Bool.and_eq_true]
  exact ⟨by simp [unpack], CFSG.KS.Raw.Orb.isInvA_unpack (CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2)⟩

theorem conj_unpack {g y : Nat} (hg : PP 1782 11 g) (hy : PP 1782 11 y) :
    compA 1782 (compA 1782 (unpack 1782 11 g) (unpack 1782 11 y))
        (invCand 1782 (unpack 1782 11 g)) = unpack 1782 11 (conj 1782 11 g y) := by
  rw [invCand_PP hg, compA_assoc _ _ _ (fun i hi => PP_get_lt hg.inv hi), compA_PP hy hg.inv,
    compA_PP hg (hy.mul hg.inv)]
  unfold conj
  rw [strictN_eq']
  rfl

theorem bitB_eq (v i : Nat) : bitB v i = v.testBit i := by
  have e : Nat.land (Nat.shiftRight v i) 1 = (v >>> i) % 2 := Nat.and_one_is_mod _
  unfold bitB
  rw [e, Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  exact CFSG.KS.Raw.Orb.beq_dec _ _

theorem shiftRight_one_eq (j : Nat) : Nat.shiftRight j 1 = j / 2 := by
  rw [show Nat.shiftRight j 1 = j >>> 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem land_one_eq (j : Nat) : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j

theorem beq_false_of_notB {a b : Nat} (h : CFSG.KLie.CT.notB (Nat.beq a b) = true) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · rw [hb] at h
    exact absurd h (by decide)

theorem beq_symm_false {a b : Nat} (h : Nat.beq a b = false) : Nat.beq b a = false := by
  cases hb : Nat.beq b a
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb).symm (Nat.ne_of_beq_eq_false h)

theorem PP_tPowK {T : Nat} (hT : PP 1782 11 T) (b : Nat) : PP 1782 11 (tPowK T b) := by
  unfold tPowK
  cases Nat.beq b 1
  · exact PP.id szOK_1782
  · exact hT

theorem tPow_unpack {T : Nat} {tT : Array Nat} (ht : tT = unpack 1782 11 T) (b : Nat) :
    (if b == 1 then tT else idTab 1782) = unpack 1782 11 (tPowK T b) := by
  unfold tPowK
  rw [beq_nat]
  cases Nat.beq b 1
  · exact idTab_unpack
  · exact ht

private theorem qProd_step {A Qk : Nat} {a qk : Array Nat} (b : Bool) (hA : PP 1782 11 A)
    (ha : a = unpack 1782 11 A) (hQ : PP 1782 11 Qk) (hq : qk = unpack 1782 11 Qk) :
    PP 1782 11 (Bool.rec (motive := fun _ => Nat) A (mul 1782 11 A Qk) b) ∧
      (if b = true then compA 1782 a qk else a) =
        unpack 1782 11 (Bool.rec (motive := fun _ => Nat) A (mul 1782 11 A Qk) b) := by
  rw [ha, hq]
  cases b
  · exact ⟨hA, rfl⟩
  · exact ⟨hA.mul hQ, compA_PP hA hQ⟩

theorem qProdK_spec {Q : Nat → Nat} {qA : Nat → Array Nat} (hP : ∀ i < 6, PP 1782 11 (Q i))
    (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i)) (v : Nat) :
    PP 1782 11 (qProdK Q v) ∧
      (List.range 6).foldl (fun r i => if v.testBit i then compA 1782 r (qA i) else r)
        (idTab 1782) = unpack 1782 11 (qProdK Q v) := by
  have key : ∀ k, k ≤ 6 →
      PP 1782 11 (Nat.rec (motive := fun _ => Nat) (pidn 1782 11)
        (fun i acc => strictN acc fun acc => nIf(bitB v i, mul 1782 11 acc (Q i), acc)) k) ∧
      (List.range k).foldl (fun r i => if v.testBit i then compA 1782 r (qA i) else r)
          (idTab 1782) =
        unpack 1782 11 (Nat.rec (motive := fun _ => Nat) (pidn 1782 11)
          (fun i acc => strictN acc fun acc => nIf(bitB v i, mul 1782 11 acc (Q i), acc)) k) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨PP.id szOK_1782, idTab_unpack⟩
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hk6 : k < 6 := by omega
      have e : (Nat.rec (motive := fun _ => Nat) (pidn 1782 11)
          (fun i acc => strictN acc fun acc => nIf(bitB v i, mul 1782 11 acc (Q i), acc)) (k + 1)) =
          Bool.rec (motive := fun _ => Nat)
            (Nat.rec (motive := fun _ => Nat) (pidn 1782 11)
              (fun i acc => strictN acc fun acc => nIf(bitB v i, mul 1782 11 acc (Q i), acc)) k)
            (mul 1782 11 (Nat.rec (motive := fun _ => Nat) (pidn 1782 11)
              (fun i acc => strictN acc fun acc => nIf(bitB v i, mul 1782 11 acc (Q i), acc)) k)
              (Q k)) (bitB v k) := strictN_eq' _ _
      rw [e, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, bitB_eq]
      exact qProd_step (v.testBit k) ih1 ih2 (hP k hk6) (hq k hk6)
  exact key 6 le_rfl

theorem baseK_facts {T : Nat} {Q QP QE : Nat → Nat} (h : baseK T Q QP QE = true) :
    PP 1782 11 T ∧ Nat.beq (mul 1782 11 T T) (pidn 1782 11) = true ∧
      Nat.beq T (pidn 1782 11) = false ∧
      (∀ i < 6, PP 1782 11 (Q i) ∧ Nat.beq (mul 1782 11 (Q i) T) (mul 1782 11 T (Q i)) = true) ∧
      (∀ v < 64, QP v = qProdK Q v) ∧
      (∀ j < 128, QE j = mul 1782 11 (QP (Nat.shiftRight j 1)) (tPowK T (Nat.land j 1))) := by
  unfold baseK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨PP_of_permOK szOK_1782 h1, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((bAnd_iff _ _).1 h2).2
  · have := ((bAnd_iff _ _).1 h3).2
    cases hb : Nat.beq T (pidn 1782 11)
    · rfl
    · rw [hb] at this
      exact absurd this (by decide)
  · intro i hi
    have := allN_spec h4 i hi
    simp only [andB_eq, Bool.and_eq_true] at this
    refine ⟨PP_of_permOK szOK_1782 this.1, ?_⟩
    exact ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 this.2).2).2
  · exact fun v hv => Nat.eq_of_beq_eq_true (allN_spec h5 v hv)
  · exact fun j hj => Nat.eq_of_beq_eq_true (allN_spec h6 j hj)

theorem conjK_facts {T : Nat} {Q C QP : Nat → Nat} {act : Nat → Nat → Nat × Nat}
    (h : conjK T Q C QP act = true) :
    ∀ k < 10, PP 1782 11 (C k) ∧ ∀ i < 6,
      Nat.beq (conj 1782 11 (C k) (Q i))
        (mul 1782 11 (QP (act k i).1) (tPowK T (act k i).2)) = true := by
  intro k hk
  have := allN_spec h k hk
  simp only [andB_eq, Bool.and_eq_true] at this
  exact ⟨PP_of_permOK szOK_1782 this.1, fun i hi => allN_spec this.2 i hi⟩

theorem q0K_facts {T OT NM OM : Nat} {Q QP TM : Nat → Nat} {oact : Nat → Nat × Nat}
    (h : q0K T OT Q QP oact NM TM OM = true) :
    PP 1782 11 OT ∧
      (∀ i < 6, Nat.beq (conj 1782 11 OT (Q i))
        (mul 1782 11 (QP (oact i).1) (tPowK T (oact i).2)) = true) ∧
      ∀ j < NM, Nat.beq (TM j) OM = false := by
  unfold q0K at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨PP_of_permOK szOK_1782 h1, fun i hi => allN_spec h2 i hi, fun j hj => ?_⟩
  exact beq_false_of_notB (allN_spec h3 j hj)

theorem wordC_foldl {C : Nat → Nat} {cT : Nat → Array Nat} (hC : ∀ k < 10, PP 1782 11 (C k))
    (hc : ∀ k < 10, cT k = unpack 1782 11 (C k)) :
    ∀ (w : List Nat) (acc : Nat) (a : Array Nat), (∀ k ∈ w, k < 10) → PP 1782 11 acc →
      a = unpack 1782 11 acc →
      PP 1782 11 (List.foldl (fun r k => strictN r fun r => mul 1782 11 r (C k)) acc w) ∧
        List.foldl (fun r k => compA 1782 r (cT k)) a w =
          unpack 1782 11 (List.foldl (fun r k => strictN r fun r => mul 1782 11 r (C k)) acc w)
  | [], _, _, _, hp, ha => ⟨hp, ha⟩
  | k :: w, acc, a, hw, hp, ha => by
    have hk : k < 10 := hw k List.mem_cons_self
    have e : strictN acc (fun r => mul 1782 11 r (C k)) = mul 1782 11 acc (C k) := strictN_eq' _ _
    rw [List.foldl_cons, List.foldl_cons, e]
    exact wordC_foldl hC hc w (mul 1782 11 acc (C k)) (compA 1782 a (cT k))
      (fun k' hk' => hw k' (List.mem_cons_of_mem k hk')) (hp.mul (hC k hk))
      (by rw [ha, hc k hk]; exact compA_PP hp (hC k hk))

theorem wordC_unpack {C : Nat → Nat} {cT : Nat → Array Nat} (hC : ∀ k < 10, PP 1782 11 (C k))
    (hc : ∀ k < 10, cT k = unpack 1782 11 (C k)) {w : List Nat} (hw : ∀ k ∈ w, k < 10) :
    PP 1782 11 (wordC C w) ∧
      List.foldl (fun r k => compA 1782 r (cT k)) (idTab 1782) w = unpack 1782 11 (wordC C w) :=
  wordC_foldl hC hc w (pidn 1782 11) (idTab 1782) hw (PP.id szOK_1782) idTab_unpack

theorem commIs_unpack {g h c : Nat} (hg : PP 1782 11 g) (hh : PP 1782 11 h) (hc : PP 1782 11 c) :
    CFSG.ComponentClassification.AS81.SuzB0.commIs (unpack 1782 11 g) (unpack 1782 11 h)
      (unpack 1782 11 c) = commIsK g h c := by
  unfold CFSG.ComponentClassification.AS81.SuzB0.commIs commIsK
  rw [compA_PP hg hh, compA_PP hh hg, compA_PP hc (hh.mul hg),
    eqA_PP (hg.mul hh) (hc.mul (hh.mul hg))]
  rfl

theorem commutesA_unpack {g h : Nat} (hg : PP 1782 11 g) (hh : PP 1782 11 h) :
    CFSG.Sporadic.SuzOddCore.commutesA (unpack 1782 11 g) (unpack 1782 11 h) =
      Nat.beq (mul 1782 11 g h) (mul 1782 11 h g) := by
  unfold CFSG.Sporadic.SuzOddCore.commutesA
  rw [compA_PP hg hh, compA_PP hh hg, eqA_PP (hg.mul hh) (hh.mul hg)]
  rfl

end CFSG.KC.B0SuzK

end
