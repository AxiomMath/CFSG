module

public import Certificates.Data.Kernel.L34Norm
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.L34Norm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native
open CFSG.KC.HeAutK (cntR)
open CFSG.KLie.CT (andB orB notB anyN)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bv_le (b : Bool) : bv b ≤ 1 := by cases b <;> decide

theorem bv_eq_one {b : Bool} : bv b = 1 ↔ b = true := by cases b <;> decide

theorem anyN_iff {N : Nat} {f : Nat → Bool} : anyN N f = true ↔ ∃ i < N, f i = true := by
  induction N with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, hi, _⟩ => absurd hi (by omega)⟩
  | succ N ih =>
    change CFSG.KLie.CT.orB (f N) (anyN N f) = true ↔ _
    rw [CFSG.KC.L34KSnd.orB_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨N, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem cntR_zero (f : Nat → Bool) (lo : Nat) : cntR f lo 0 = 0 := rfl

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem cntR_succ (f : Nat → Bool) (lo k : Nat) :
    cntR f lo (k + 1) = cntR f lo k + bv (f (lo + k)) := by
  have e : cntR f lo (k + 1) = strictN (cntR f lo k) fun a =>
      Nat.add a (Bool.rec (motive := fun _ => Nat) 0 1 (f (Nat.add lo k))) := rfl
  rw [e, strictN_eq]
  rfl

theorem cntR_shift (f : Nat → Bool) (lo : Nat) :
    ∀ k, cntR f lo (k + 1) = bv (f lo) + cntR f (lo + 1) k
  | 0 => by rw [cntR_succ, cntR_zero, cntR_zero, Nat.add_zero, Nat.zero_add, Nat.add_zero]
  | k + 1 => by
    rw [cntR_succ, cntR_shift f lo k, cntR_succ, Nat.add_assoc,
      show lo + 1 + k = lo + (k + 1) by omega]

theorem cntR_add (f : Nat → Bool) (lo a : Nat) :
    ∀ b, cntR f lo (a + b) = cntR f lo a + cntR f (lo + a) b
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc, cntR_succ, cntR_add f lo a b, cntR_succ, Nat.add_assoc,
      Nat.add_assoc lo a b]

theorem cntR_congr {f g : Nat → Bool} (lo : Nat) :
    ∀ len, (∀ i < len, f (lo + i) = g (lo + i)) → cntR f lo len = cntR g lo len
  | 0, _ => rfl
  | len + 1, h => by
    rw [cntR_succ, cntR_succ, cntR_congr lo len fun i hi => h i (by omega), h len (by omega)]

structure Listed (f J : Nat → Nat) (lo len c e : Nat) : Prop where
  le : c ≤ e
  mem : ∀ k, lo ≤ k → k < lo + len → f k ≠ 0 →
    f k < 32 ∧ ∃ q, c ≤ q ∧ q < e ∧ J q = 32 * k + f k
  get : ∀ q, c ≤ q → q < e → ∃ k, lo ≤ k ∧ k < lo + len ∧ f k ≠ 0 ∧ f k < 32 ∧ J q = 32 * k + f k
  cnt : ∀ P : Nat → Bool, P 0 = false →
    cntR (fun k => P (f k)) lo len = cntR (fun q => P (J q % 32)) c (e - c)

variable {f J : Nat → Nat}

theorem curRun_succ (len lo c e : Nat) :
    curRun f J (len + 1) lo c e = strictB (f lo) fun v =>
      bIf(Nat.beq v (nat_lit 0), curRun f J len (Nat.succ lo) c e,
        CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.blt v (nat_lit 32)) (Nat.beq (J c) (Nat.add (Nat.mul (nat_lit 32) lo) v)))
          (curRun f J len (Nat.succ lo) (Nat.succ c) e)) := rfl

theorem curRun_of_zero {len lo c e : Nat} (h0 : f lo = 0) :
    curRun f J (len + 1) lo c e = curRun f J len (lo + 1) c e := by
  rw [curRun_succ, strictB_eq, h0]
  rfl

theorem curRun_of_ne {len lo c e : Nat} (h0 : f lo ≠ 0) :
    curRun f J (len + 1) lo c e = CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.blt (f lo) 32) (Nat.beq (J c) (32 * lo + f lo)))
      (curRun f J len (lo + 1) (c + 1) e) := by
  rw [curRun_succ, strictB_eq]
  generalize f lo = v at h0 ⊢
  cases v with
  | zero => exact absurd rfl h0
  | succ m => rfl

theorem Listed.nil (lo c : Nat) : Listed f J lo 0 c c :=
  ⟨le_refl _, fun _ _ _ _ => by omega, fun _ _ _ => by omega, fun _ _ => by rw [Nat.sub_self]; rfl⟩

theorem curRun_listed : ∀ len lo c e, curRun f J len lo c e = true → Listed f J lo len c e
  | 0, lo, c, e, h => by
    have hce : c = e := Nat.eq_of_beq_eq_true h
    subst hce
    exact Listed.nil lo c
  | len + 1, lo, c, e, h => by
    by_cases h0 : f lo = 0
    · rw [curRun_of_zero h0] at h
      have ih := curRun_listed len (lo + 1) c e h
      refine ⟨ih.le, fun k h1 h2 hk => ?_, fun q h1 h2 => ?_, fun P hP => ?_⟩
      · have hk' : k ≠ lo := fun e => hk (e ▸ h0)
        exact ih.mem k (by omega) (by omega) hk
      · obtain ⟨k, h3, h4, h5⟩ := ih.get q h1 h2
        exact ⟨k, by omega, by omega, h5⟩
      · rw [cntR_shift, ih.cnt P hP, h0, hP]
        exact Nat.zero_add _
    · rw [curRun_of_ne h0] at h
      obtain ⟨h1, h2⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
      obtain ⟨hv, hJ⟩ := CFSG.KC.L34KSnd.andB_iff.1 h1
      have hv : f lo < 32 := Nat.blt_eq.mp hv
      have hJ : J c = 32 * lo + f lo := Nat.eq_of_beq_eq_true hJ
      have ih := curRun_listed len (lo + 1) (c + 1) e h2
      have hce := ih.le
      refine ⟨by omega, fun k h3 h4 hk => ?_, fun q h3 h4 => ?_, fun P hP => ?_⟩
      · by_cases hkl : k = lo
        · subst hkl
          exact ⟨hv, c, le_refl _, by omega, hJ⟩
        · obtain ⟨hk32, q, h5, h6, h7⟩ := ih.mem k (by omega) (by omega) hk
          exact ⟨hk32, q, by omega, h6, h7⟩
      · by_cases hq : q = c
        · subst hq
          exact ⟨lo, le_refl _, by omega, h0, hv, hJ⟩
        · obtain ⟨k, h5, h6, h7⟩ := ih.get q (by omega) h4
          exact ⟨k, by omega, by omega, h7⟩
      · have hm : J c % 32 = f lo := by omega
        rw [cntR_shift, ih.cnt P hP, show e - c = (e - (c + 1)) + 1 by omega, cntR_shift, hm]

theorem Listed.join {lo a b c d e : Nat} (h1 : Listed f J lo a c d)
    (h2 : Listed f J (lo + a) b d e) : Listed f J lo (a + b) c e := by
  have hcd := h1.le
  have hde := h2.le
  refine ⟨by omega, fun k h3 h4 hk => ?_, fun q h3 h4 => ?_, fun P hP => ?_⟩
  · by_cases hka : k < lo + a
    · obtain ⟨h5, q, h6, h7, h8⟩ := h1.mem k h3 hka hk
      exact ⟨h5, q, h6, by omega, h8⟩
    · obtain ⟨h5, q, h6, h7, h8⟩ := h2.mem k (by omega) (by omega) hk
      exact ⟨h5, q, by omega, h7, h8⟩
  · by_cases hqd : q < d
    · obtain ⟨k, h5, h6, h7⟩ := h1.get q h3 hqd
      exact ⟨k, h5, by omega, h7⟩
    · obtain ⟨k, h5, h6, h7⟩ := h2.get q (by omega) h4
      exact ⟨k, by omega, by omega, h7⟩
  · rw [cntR_add, h1.cnt P hP, h2.cnt P hP, show e - c = (d - c) + (e - d) by omega, cntR_add,
      show c + (d - c) = d by omega]

theorem slices_listed {L : Nat} {C : Nat → Nat} :
    ∀ K, (∀ s < K, curSl f J L C s = true) → Listed f J 0 (L * K) (C 0) (C K)
  | 0, _ => Listed.nil 0 (C 0)
  | K + 1, h => by
    have ih := slices_listed K fun s hs => h s (by omega)
    have h2 : Listed f J (0 + L * K) L (C K) (C (K + 1)) := by
      rw [Nat.zero_add]
      exact curRun_listed L (L * K) (C K) (C (K + 1)) (h K (by omega))
    rw [Nat.mul_succ]
    exact ih.join h2

variable {n w : Nat}

theorem conjPt_iff {x a e : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (ha : canonK n w (mask w) (n * w) a = true) (he : canonK n w (mask w) (n * w) e = true) :
    conjPt n w x a e = true ↔
      comp n (unpack n w x) (unpack n w a) = comp n (unpack n w e) (unpack n w x) := by
  rw [CFSG.KC.L34KSnd.comp_unpack' hx ha, CFSG.KC.L34KSnd.comp_unpack' he hx]
  unfold conjPt
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h
    have e : pcomp n w (mask w) x a = pcomp n w (mask w) e x :=
      CFSG.KC.L34KSnd.eq_of_pg (canonK_pcomp hx ha) (canonK_pcomp he hx) fun i hi => by
        rw [CFSG.KC.L34KSnd.pg_pcomp' hx hi, CFSG.KC.L34KSnd.pg_pcomp' he hi]
        exact Nat.beq_eq.mp (h i hi)
    rw [e]
  · intro h i hi
    have h' : (unpack n w (pcomp n w (mask w) x a))[i]! =
        (unpack n w (pcomp n w (mask w) e x))[i]! := congrArg (fun t : Tab => t[i]!) h
    rw [unpack_get' hi, unpack_get' hi, CFSG.KC.L34KSnd.pg_pcomp' hx hi,
      CFSG.KC.L34KSnd.pg_pcomp' he hi] at h'
    exact Nat.beq_eq.mpr h'

theorem inPts_iff {N : Nat} {P : Nat → Nat} {x a : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (ha : canonK n w (mask w) (n * w) a = true)
    (hP : ∀ j < N, canonK n w (mask w) (n * w) (P j) = true) :
    inPts n w N P x a = true ↔
      ∃ j < N, comp n (unpack n w x) (unpack n w a) = comp n (unpack n w (P j)) (unpack n w x) := by
  unfold inPts
  rw [anyN_iff]
  exact exists_congr fun j => ⟨fun ⟨hj, h⟩ => ⟨hj, (conjPt_iff hx ha (hP j hj)).1 h⟩,
    fun ⟨hj, h⟩ => ⟨hj, (conjPt_iff hx ha (hP j hj)).2 h⟩⟩

theorem pairPt_iff {u v x : Nat} (hu : u < n) (hv : v < n) :
    pairPt w u v x = true ↔ ((unpack n w x)[u]! = u ∨ (unpack n w x)[u]! = v) ∧
      ((unpack n w x)[v]! = u ∨ (unpack n w x)[v]! = v) := by
  unfold pairPt
  rw [unpack_get' hu, unpack_get' hv, CFSG.KC.L34KSnd.andB_iff, CFSG.KC.L34KSnd.orB_iff,
    CFSG.KC.L34KSnd.orB_iff, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]

theorem o3Pt_iff {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    o3Pt n w (pidn n w) x = true ↔ unpack n w x ≠ idTab n ∧
      comp n (unpack n w x) (comp n (unpack n w x) (unpack n w x)) = idTab n := by
  have hsz := CFSG.KC.L34KSnd.canon_sz hx
  have hxx := canonK_pcomp hx hx
  have hb : Nat.beq x (pidn n w) = false ↔ x ≠ pidn n w :=
    ⟨fun h e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h, beq_false⟩
  unfold o3Pt
  rw [CFSG.KC.L34KSnd.andB_iff, CFSG.KC.L34KSnd.notB_iff, hb,
    CFSG.KC.L34KSnd.comp_unpack' hx hx, CFSG.KC.L34KSnd.comp_unpack' hx hxx,
    CFSG.KC.L34KSnd.idTab_unpack' hsz, CFSG.KS.Raw.Orb.allN_iff]
  refine and_congr ⟨fun h e => h (CFSG.KC.L34KSnd.unpack_inj' hx
    (CFSG.KC.L34KSnd.canon_pidn hsz) e), fun h e => h (by rw [e])⟩ ⟨fun h => ?_, fun h i hi => ?_⟩
  · have e : pcomp n w (mask w) x (pcomp n w (mask w) x x) = pidn n w :=
      CFSG.KC.L34KSnd.eq_of_pg (canonK_pcomp hx hxx) (CFSG.KC.L34KSnd.canon_pidn hsz)
        fun i hi => by
          rw [CFSG.KC.L34KSnd.pg_pcomp' hx hi, CFSG.KC.L34KSnd.pg_pcomp' hx hi,
            CFSG.KC.L34KSnd.pg_pidn' hsz hi]
          exact Nat.beq_eq.mp (h i hi)
    rw [e]
  · have h' := congrArg (fun t : Tab => t[i]!) h
    rw [unpack_get' hi, unpack_get' hi, CFSG.KC.L34KSnd.pg_pcomp' hx hi,
      CFSG.KC.L34KSnd.pg_pcomp' hx hi, CFSG.KC.L34KSnd.pg_pidn' hsz hi] at h'
    exact Nat.beq_eq.mpr h'

theorem nfixK_eq (x : Nat) :
    nfixK n w x = cntR (fun p => (unpack n w x)[p]! == p) 0 n := by
  unfold nfixK
  refine cntR_congr 0 n fun i hi => ?_
  rw [Nat.zero_add, unpack_get' hi]
  cases h : Nat.beq (pg w (mask w) x i) i
  · exact (beq_eq_false_iff_ne.2 (Nat.ne_of_beq_eq_false h)).symm
  · exact (beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)).symm

theorem o3Cat_le (n w e x : Nat) : o3Cat n w e x ≤ 4 := by
  unfold o3Cat
  cases o3Pt n w e x
  · exact Nat.zero_le _
  · dsimp only
    rw [strictN_eq]
    generalize nfixK n w x = f
    cases Nat.beq f 0 <;> cases Nat.beq f 6 <;> cases Nat.beq f 12 <;> decide

theorem o3Cat_spec (n w e x : Nat) :
    (o3Cat n w e x = 0 ↔ o3Pt n w e x = false) ∧
    (o3Cat n w e x = 1 ↔ o3Pt n w e x = true ∧ nfixK n w x = 0) ∧
    (o3Cat n w e x = 2 ↔ o3Pt n w e x = true ∧ nfixK n w x = 6) ∧
    (o3Cat n w e x = 3 ↔ o3Pt n w e x = true ∧ nfixK n w x = 12) := by
  unfold o3Cat
  cases o3Pt n w e x
  · dsimp only
    simp
  · dsimp only
    rw [strictN_eq]
    generalize nfixK n w x = f
    rcases (by omega : f = 0 ∨ f = 6 ∨ f = 12 ∨ (f ≠ 0 ∧ f ≠ 6 ∧ f ≠ 12)) with
      rfl | rfl | rfl | ⟨h0, h6, h12⟩
    · decide
    · decide
    · decide
    · rw [beq_false h0, beq_false h6, beq_false h12]
      simp [h0, h6, h12]

theorem normCode_bits (n w AN : Nat) (AP : Nat → Nat) (a b z u v e x : Nat) :
    normCode n w AN AP a b z u v e x % 2 =
        bv (CFSG.KLie.CT.andB (inPts n w AN AP x a) (inPts n w AN AP x b)) ∧
      normCode n w AN AP a b z u v e x / 2 % 2 = bv (commPt n w x z) ∧
      normCode n w AN AP a b z u v e x / 4 % 2 = bv (pairPt w u v x) ∧
      normCode n w AN AP a b z u v e x / 8 = o3Cat n w e x := by
  have h1 := bv_le (CFSG.KLie.CT.andB (inPts n w AN AP x a) (inPts n w AN AP x b))
  have h2 := bv_le (commPt n w x z)
  have h3 := bv_le (pairPt w u v x)
  unfold normCode
  simp only [Nat.add_eq, Nat.mul_eq]
  generalize bv (CFSG.KLie.CT.andB (inPts n w AN AP x a) (inPts n w AN AP x b)) = A at h1 ⊢
  generalize bv (commPt n w x z) = Z at h2 ⊢
  generalize bv (pairPt w u v x) = T at h3 ⊢
  generalize o3Cat n w e x = c
  omega

end CFSG.KC.L34Norm

end
