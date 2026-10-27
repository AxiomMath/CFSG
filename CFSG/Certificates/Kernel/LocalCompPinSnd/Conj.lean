
module

public import Certificates.Data.Kernel.LocalComp.ConjPin
public import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinBaseSound
import all CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.RawDefs
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.LocalComp.PinSnd

open CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
  CFSG.KC.LocalComp.ConjPin
open CFSG.KLie.CT (fget)

theorem rec_eq_foldl (step : Nat → Nat → Nat) (N : Nat) :
    ∀ r, r ≤ N → ∀ c, Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (step (Nat.sub (Nat.sub N r) 1) c) ih) r c =
        (List.range' (N - r) r).foldl (fun c j => step j c) c := by
  intro r
  induction r with
  | zero => intro _ c; rfl
  | succ r ih =>
    intro hr c
    have h1 : N - (r + 1) = Nat.sub (Nat.sub N r) 1 := by
      show N - (r + 1) = N - r - 1
      omega
    have h2 : Nat.sub (Nat.sub N r) 1 + 1 = N - r := by
      show N - r - 1 + 1 = N - r
      omega
    have e : List.range' (N - (r + 1)) (r + 1) =
        Nat.sub (Nat.sub N r) 1 :: List.range' (N - r) r := by
      rw [h1, List.range'_succ, h2]
    show strictN (step (Nat.sub (Nat.sub N r) 1) c)
        (Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
          (fun r ih c => strictN (step (Nat.sub (Nat.sub N r) 1) c) ih) r) =
        (List.range' (N - (r + 1)) (r + 1)).foldl (fun c j => step j c) c
    rw [strictN_app, ih (by omega) (step (Nat.sub (Nat.sub N r) 1) c), e, List.foldl_cons]

theorem loop_eq_foldl (step : Nat → Nat → Nat) (N c : Nat) :
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (step (Nat.sub (Nat.sub N r) 1) c) ih) N c =
        (List.range N).foldl (fun c j => step j c) c := by
  have := rec_eq_foldl step N N (Nat.le_refl N) c
  rw [Nat.sub_self] at this
  rw [this, List.range_eq_range']

theorem cStep_eq_genStep (n w m : Nat) (T : Nat → Nat) (t row g gi k c : Nat) :
    cStep n w m T t row g gi k c = genStep n w m T (pcomp n w m t gi) row g k c := rfl

theorem cStep_eq (n w m : Nat) (T : Nat → Nat) (t row g gi k c : Nat) :
    cStep n w m T t row g gi k c =
      if c = 0 then 0
      else if fget row k 16 < c then
        (if T (fget row k 16) = pcomp n w m g (pcomp n w m t gi) then c else 0)
      else if fget row k 16 = c then
        (if T c = pcomp n w m g (pcomp n w m t gi) then c + 1 else 0) else 0 :=
  genStep_eq n w m T (pcomp n w m t gi) row g k c

theorem cStep_zero (n w m : Nat) (T : Nat → Nat) (t row g gi k : Nat) :
    cStep n w m T t row g gi k 0 = 0 :=
  genStep_zero n w m T (pcomp n w m t gi) row g k

theorem cStep_spec {n w m : Nat} {T : Nat → Nat} {t row g gi k c r : Nat}
    (hr : cStep n w m T t row g gi k c = r) (h0 : r ≠ 0) :
    c ≠ 0 ∧ c ≤ r ∧ (∃ j < r, T j = pcomp n w m g (pcomp n w m t gi)) ∧
      ∀ j, c ≤ j → j < r → T j = pcomp n w m g (pcomp n w m t gi) :=
  genStep_spec hr h0

theorem cPoint_eq (n w m ng : Nat) (G GI T E : Nat → Nat) (i c : Nat) :
    cPoint n w m ng G GI T E i c =
      (List.range ng).foldl (fun c k => cStep n w m T (T i) (E i) (G k) (GI k) k c) c := by
  unfold cPoint
  rw [strictN_app, strictN_app]
  exact loop_eq_foldl (fun k c => cStep n w m T (T i) (E i) (G k) (GI k) k c) ng c

@[expose] noncomputable def rstK (n w m ng : Nat) (G GI T E : Nat → Nat) (i c : Nat) : Nat :=
  if i < c then cPoint n w m ng G GI T E i c else 0

theorem runCK_eq (n w m ng : Nat) (G GI T E : Nat → Nat) (N : Nat) :
    runCK n w m ng G GI T E N =
      (List.range N).foldl (fun c i => rstK n w m ng G GI T E i c) 1 := by
  unfold runCK
  simp only [nIf_ite, Nat.blt_eq]
  exact loop_eq_foldl (fun i c => rstK n w m ng G GI T E i c) N 1

open CFSG.KS.BfsReplay CFSG.KS.PEnum

def PInvC (n w ng : Nat) (gens ginv : Array Tab) (T : Nat → Nat) (c : Nat) (s : St) : Prop :=
  s.1.size = c ∧ s.2.1.size = c ∧ s.2.2.1.size = c ∧
    (∀ i < c, s.1[i]! = unpack n w (T i)) ∧
    (∀ x, s.2.2.2.contains x = true ↔ ∃ i < c, unpack n w (T i) = x) ∧
    (∀ i < c, i ≠ 0 → s.2.1[i]! < i ∧ s.2.2.1[i]! < ng ∧
      s.1[i]! = conjStep n gens ginv s.2.2.1[i]! s.1[s.2.1[i]!]!)

section Search

variable {n w ng N : Nat} {G GI T E : Nat → Nat} {gens ginv : Array Tab}

structure PinFC (n w ng N : Nat) (G GI T : Nat → Nat) (gens ginv : Array Tab) : Prop where
  size : gens.size = ng
  sizei : ginv.size = ng
  bind : ∀ k < ng, gens[k]! = unpack n w (G k)
  bindi : ∀ k < ng, ginv[k]! = unpack n w (GI k)
  canG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true
  canGI : ∀ k < ng, canonK n w (mask w) (n * w) (GI k) = true
  canT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true
  inj : ∀ a < N, ∀ b < N, T a = T b → a = b

theorem getElem!_ofFn_of_lt {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {k : Nat}
    (hk : k < m) : (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem comp_assoc_of_lt {p q r : Tab} (hr : ∀ i < n, r[i]! < n) :
    comp n (comp n p q) r = comp n p (comp n q r) := by
  unfold comp
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    rw [getElem!_ofFn_of_lt _ (hr i hi)]
    rw [getElem!_ofFn_of_lt _ hi]

theorem PinFC.step (P : PinFC n w ng N G GI T gens ginv) {j h : Nat} (hj : j < ng) (hh : h < N) :
    conjStep n gens ginv j (unpack n w (T h)) =
      unpack n w (pcomp n w (mask w) (G j) (pcomp n w (mask w) (T h) (GI j))) := by
  unfold conjStep conjTab
  rw [P.bind j hj, P.bindi j hj]
  have hGI : ∀ i < n, (unpack n w (GI j))[i]! < n := fun i hi => by
    rw [CFSG.KS.Raw.Orb.unpack_get hi]
    exact (CFSG.KS.PF.canon_facts (P.canGI j hj)).2.2.2 i hi
  rw [comp_assoc_of_lt hGI, comp_unpack (P.canT h hh) (P.canGI j hj),
    comp_unpack (P.canG j hj) (CFSG.KC.BfsPin.canonK_pcomp (P.canT h hh) (P.canGI j hj))]

theorem PinFC.uinj (P : PinFC n w ng N G GI T gens ginv) {a b : Nat} (ha : a < N) (hb : b < N)
    (e : unpack n w (T a) = unpack n w (T b)) : a = b :=
  P.inj a ha b hb (unpack_inj (P.canT a ha) (P.canT b hb) e)

theorem pin_innerC (P : PinFC n w ng N G GI T gens ginv) {h j c : Nat} (hh : h < c) (hj : j < ng)
    {s : St} (hI : PInvC n w ng gens ginv T c s)
    (h0 : cStep n w (mask w) T (T h) (E h) (G j) (GI j) j c ≠ 0)
    (hN : cStep n w (mask w) T (T h) (E h) (G j) (GI j) j c ≤ N) :
    ∃ s', innerBody (conjStep n gens ginv) (unpack n w (T h)) h j s = pure (ForInStep.yield s') ∧
      PInvC n w ng gens ginv T (cStep n w (mask w) T (T h) (E h) (G j) (GI j) j c) s' := by
  obtain ⟨h1, h2, h3, hget, hK, htr⟩ := hI
  have hcN : c ≤ N := le_trans (cStep_spec rfl h0).2.1 hN
  have hy := P.step hj (by omega : h < N)
  have e := cStep_eq n w (mask w) T (T h) (E h) (G j) (GI j) j c
  generalize fget (E h) j 16 = q at e
  generalize hY : pcomp n w (mask w) (G j) (pcomp n w (mask w) (T h) (GI j)) = y at e hy
  have hc0 : c ≠ 0 := by omega
  rw [ite_eq_right hc0] at e
  by_cases hlt : q < c
  · rw [ite_eq_left hlt] at e
    by_cases hT : T q = y
    · rw [ite_eq_left hT] at e
      rw [e]
      have hc : s.2.2.2.contains (unpack n w y) = true := (hK _).2 ⟨q, hlt, by rw [hT]⟩
      exact ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [innerBody, hy, hc],
        h1, h2, h3, hget, hK, htr⟩
    · rw [ite_eq_right hT] at e
      exact absurd e h0
  · rw [ite_eq_right hlt] at e
    by_cases heq : q = c
    · by_cases hT : T c = y
      · rw [ite_eq_left heq, ite_eq_left hT] at e
        rw [e] at hN ⊢
        have hnc : s.2.2.2.contains (unpack n w y) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          obtain ⟨i, hi, ei⟩ := (hK _).1 hc
          rw [← hT] at ei
          have := P.uinj (by omega) (by omega) ei
          omega
        refine ⟨(s.1.push (unpack n w y), s.2.1.push h, s.2.2.1.push j,
          s.2.2.2.insert (unpack n w y) s.1.size), by simp [innerBody, hy, hnc],
          by simp [h1], by simp [h2], by simp [h3], fun i hi => ?_, fun x => ?_,
          fun i hi hi0 => ?_⟩
        · rcases Nat.lt_or_ge i c with a | a
          · change (s.1.push _)[i]! = _
            rw [push_lt (by omega)]
            exact hget i a
          · have ei : i = s.1.size := by omega
            subst ei
            change (s.1.push _)[s.1.size]! = _
            rw [push_eq, h1, hT]
        · change (s.2.2.2.insert _ _).contains x = true ↔ _
          rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hK]
          constructor
          · rintro (ex | ⟨i, hi, ex⟩)
            · exact ⟨c, by omega, by rw [hT, ex]⟩
            · exact ⟨i, by omega, ex⟩
          · rintro ⟨i, hi, ex⟩
            rcases Nat.lt_or_ge i c with a | a
            · exact Or.inr ⟨i, a, ex⟩
            · have ei : i = c := by omega
              subst ei
              rw [← ex, hT]
              exact Or.inl rfl
        · change (s.2.1.push h)[i]! < i ∧ (s.2.2.1.push j)[i]! < ng ∧
            (s.1.push _)[i]! =
              conjStep n gens ginv (s.2.2.1.push j)[i]! (s.1.push _)[(s.2.1.push h)[i]!]!
          rcases Nat.lt_or_ge i c with a | a
          · obtain ⟨t1, t2, t3⟩ := htr i a hi0
            rw [push_lt (by omega : i < s.2.1.size), push_lt (by omega : i < s.2.2.1.size),
              push_lt (by omega : i < s.1.size), push_lt (by omega : s.2.1[i]! < s.1.size)]
            exact ⟨t1, t2, t3⟩
          · have ei : i = c := by omega
            subst ei
            have e2 : (s.2.1.push h)[i]! = h := by rw [← h2]; exact push_eq
            have e3 : (s.2.2.1.push j)[i]! = j := by rw [← h3]; exact push_eq
            have e1 : (s.1.push (unpack n w y))[i]! = unpack n w y := by rw [← h1]; exact push_eq
            rw [e1, e2, e3, push_lt (by omega : h < s.1.size), hget h hh, hy]
            exact ⟨hh, hj, rfl⟩
      · rw [ite_eq_left heq, ite_eq_right hT] at e
        exact absurd e h0
    · rw [ite_eq_right heq] at e
      exact absurd e h0

theorem foldl_zero_of {step : Nat → Nat → Nat} (hz : ∀ k, step k 0 = 0) :
    ∀ L : List Nat, L.foldl (fun c k => step k c) 0 = 0
  | [] => rfl
  | k :: L => by
    rw [List.foldl_cons, hz k]
    exact foldl_zero_of hz L

theorem foldl_ge_of {step : Nat → Nat → Nat} (hz : ∀ k, step k 0 = 0)
    (hm : ∀ k c, step k c ≠ 0 → c ≤ step k c) :
    ∀ (L : List Nat) (c : Nat), L.foldl (fun c k => step k c) c ≠ 0 →
      c ≤ L.foldl (fun c k => step k c) c
  | [], c, _ => Nat.le_refl c
  | k :: L, c, h => by
    rw [List.foldl_cons] at h ⊢
    have hk : step k c ≠ 0 := fun e => h (by rw [e]; exact foldl_zero_of hz L)
    exact le_trans (hm k c hk) (foldl_ge_of hz hm L (step k c) h)

theorem foldl_range_succ {step : Nat → Nat → Nat} (c m : Nat) :
    (List.range (m + 1)).foldl (fun c k => step k c) c =
      step m ((List.range m).foldl (fun c k => step k c) c) := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem foldl_range_prefix {step : Nat → Nat → Nat} (hz : ∀ k, step k 0 = 0)
    (hm : ∀ k c, step k c ≠ 0 → c ≤ step k c) (c : Nat) :
    ∀ m, (List.range m).foldl (fun c k => step k c) c ≠ 0 →
      ∀ j ≤ m, (List.range j).foldl (fun c k => step k c) c ≠ 0 ∧
        (List.range j).foldl (fun c k => step k c) c ≤
          (List.range m).foldl (fun c k => step k c) c ∧
        c ≤ (List.range j).foldl (fun c k => step k c) c := by
  intro m
  induction m with
  | zero =>
    intro h j hj
    have e : j = 0 := by omega
    subst e
    exact ⟨h, Nat.le_refl _, Nat.le_refl _⟩
  | succ m ih =>
    intro h j hj
    rw [foldl_range_succ] at h
    have hFm : (List.range m).foldl (fun c k => step k c) c ≠ 0 := fun e => h (by rw [e]; exact hz m)
    have hmm := hm m _ h
    rcases Nat.lt_or_ge j (m + 1) with a | a
    · obtain ⟨h1, h2, h3⟩ := ih hFm j (by omega)
      rw [foldl_range_succ]
      exact ⟨h1, le_trans h2 hmm, h3⟩
    · have e : j = m + 1 := by omega
      subst e
      obtain ⟨-, -, h3⟩ := ih hFm m (Nat.le_refl m)
      rw [foldl_range_succ]
      exact ⟨h, Nat.le_refl _, le_trans h3 hmm⟩

theorem foldl_steps_le {step : Nat → Nat → Nat} (hz : ∀ k, step k 0 = 0)
    (hm : ∀ k c, step k c ≠ 0 → c ≤ step k c) :
    ∀ (L : List Nat) (c : Nat), L.foldl (fun c k => step k c) c ≠ 0 →
      ∀ k ∈ L, ∃ c', c' ≠ 0 ∧ step k c' ≠ 0 ∧ step k c' ≤ L.foldl (fun c k => step k c) c
  | [], _, _, k, hk => absurd hk (List.not_mem_nil)
  | a :: L, c, h, k, hk => by
    rw [List.foldl_cons] at h ⊢
    have hac : step a c ≠ 0 := fun e => h (by rw [e]; exact foldl_zero_of hz L)
    have hc0 : c ≠ 0 := fun e => hac (by rw [e]; exact hz a)
    rcases List.mem_cons.1 hk with rfl | hk'
    · exact ⟨c, hc0, hac, foldl_ge_of hz hm L (step k c) h⟩
    · exact foldl_steps_le hz hm L (step a c) h k hk'

theorem cStep_mono {n w m : Nat} {T : Nat → Nat} {t row g gi k c : Nat}
    (h : cStep n w m T t row g gi k c ≠ 0) : c ≤ cStep n w m T t row g gi k c :=
  (cStep_spec rfl h).2.1

theorem cPoint_zero (n w m ng : Nat) (G GI T E : Nat → Nat) (i : Nat) :
    cPoint n w m ng G GI T E i 0 = 0 := by
  rw [cPoint_eq]
  exact foldl_zero_of (step := fun k c => cStep n w m T (T i) (E i) (G k) (GI k) k c)
    (fun k => cStep_zero n w m T (T i) (E i) (G k) (GI k) k) _

theorem cPoint_mono {n w m ng : Nat} {G GI T E : Nat → Nat} {i c : Nat}
    (h : cPoint n w m ng G GI T E i c ≠ 0) : c ≤ cPoint n w m ng G GI T E i c := by
  rw [cPoint_eq] at h ⊢
  exact foldl_ge_of (step := fun k c => cStep n w m T (T i) (E i) (G k) (GI k) k c)
    (fun k => cStep_zero n w m T (T i) (E i) (G k) (GI k) k) (fun k c h => cStep_mono h) _ c h

theorem rstK_zero (n w m ng : Nat) (G GI T E : Nat → Nat) (i : Nat) :
    rstK n w m ng G GI T E i 0 = 0 := by
  simp [rstK]

theorem rstK_mono {n w m ng : Nat} {G GI T E : Nat → Nat} {i c : Nat}
    (h : rstK n w m ng G GI T E i c ≠ 0) : c ≤ rstK n w m ng G GI T E i c := by
  unfold rstK at h ⊢
  by_cases hi : i < c
  · simp only [hi, if_true] at h ⊢
    exact cPoint_mono h
  · simp only [hi, if_false] at h
    exact absurd rfl h

theorem pin_pointC (P : PinFC n w ng N G GI T gens ginv) {h c : Nat} (hh : h < c) {s : St}
    (hI : PInvC n w ng gens ginv T c s)
    (h0 : cPoint n w (mask w) ng G GI T E h c ≠ 0) (hN : cPoint n w (mask w) ng G GI T E h c ≤ N) :
    PInvC n w ng gens ginv T (cPoint n w (mask w) ng G GI T E h c)
      (Id.run (forIn (List.range' 0 ng) (s.1, s.2.1, s.2.2.1, s.2.2.2)
        (innerBody (conjStep n gens ginv) (unpack n w (T h)) h))) := by
  rw [cPoint_eq] at h0 hN ⊢
  have hz : ∀ k, cStep n w (mask w) T (T h) (E h) (G k) (GI k) k 0 = 0 :=
    fun k => cStep_zero n w (mask w) T (T h) (E h) (G k) (GI k) k
  have hpre := foldl_range_prefix (step := fun k c' => cStep n w (mask w) T (T h) (E h) (G k) (GI k) k c')
    hz (fun k c' h' => cStep_mono h') c ng h0
  exact forIn_range'_yield ng 0 (s.1, s.2.1, s.2.2.1, s.2.2.2)
    (innerBody (conjStep n gens ginv) (unpack n w (T h)) h)
    (fun j s' => PInvC n w ng gens ginv T
      ((List.range j).foldl (fun c' k => cStep n w (mask w) T (T h) (E h) (G k) (GI k) k c') c) s')
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨hne, hle, -⟩ := hpre (j + 1) (by omega)
      obtain ⟨-, -, hge⟩ := hpre j (by omega)
      rw [foldl_range_succ] at hne hle ⊢
      exact pin_innerC P (by omega) hj hP hne (le_trans hle hN))
    hI

theorem pin_outerC (P : PinFC n w ng N G GI T gens ginv) {cap : Nat} (hcap : N ≤ cap) (hN0 : N ≠ 0)
    {x : Tab}
    (hrun : (List.range N).foldl (fun c i => rstK n w (mask w) ng G GI T E i c) 1 = N)
    (hT0 : x = unpack n w (T 0)) :
    PInvC n w ng gens ginv T N
      (Id.run (forIn (List.range' 0 cap) (initSt x cap)
        (outerBody (conjStep n gens ginv) ng))) := by
  have hRz : ∀ i, rstK n w (mask w) ng G GI T E i 0 = 0 := fun i => rstK_zero n w (mask w) ng G GI T E i
  refine forIn_range'_done cap 0 (initSt x cap) (outerBody (conjStep n gens ginv) ng)
    (fun h s => h ≤ N ∧ ∃ c, h ≤ c ∧ PInvC n w ng gens ginv T c s ∧
      (List.range' h (N - h)).foldl (fun c i => rstK n w (mask w) ng G GI T E i c) c = N)
    (PInvC n w ng gens ginv T N) (fun h hh s hP => ?_) (fun s hP => ?_)
    ⟨Nat.zero_le _, 1, Nat.zero_le _, ?_, by rw [Nat.sub_zero, ← List.range_eq_range']; exact hrun⟩
  · obtain ⟨hhN, c, hhc, hI, hr⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge h N with a | a
    · have e : N - h = (N - (h + 1)) + 1 := by omega
      rw [e, List.range'_succ, List.foldl_cons] at hr
      by_cases hlt : h < c
      · have hrh : rstK n w (mask w) ng G GI T E h c = cPoint n w (mask w) ng G GI T E h c := by
          simp [rstK, hlt]
        rw [hrh] at hr
        have hp0 : cPoint n w (mask w) ng G GI T E h c ≠ 0 := by
          intro z
          rw [z] at hr
          exact hN0 ((foldl_zero_of (step := fun i c => rstK n w (mask w) ng G GI T E i c) hRz _).symm.trans hr).symm
        have hpN : cPoint n w (mask w) ng G GI T E h c ≤ N := by
          have := foldl_ge_of (step := fun i c => rstK n w (mask w) ng G GI T E i c)
            hRz (fun i c h' => rstK_mono h') (List.range' (h + 1) (N - (h + 1))) _
            (by rw [hr]; exact hN0)
          rw [hr] at this
          exact this
        have hpc := cPoint_mono hp0
        have hhs : h < s.1.size := by rw [hI.1]; exact hlt
        have hsh : s.1[h]! = unpack n w (T h) := hI.2.2.2.1 h hlt
        refine Or.inl ⟨Id.run (forIn (List.range' 0 ng) (s.1, s.2.1, s.2.2.1, s.2.2.2)
          (innerBody (conjStep n gens ginv) (unpack n w (T h)) h)), ?_, by omega, _, by omega,
          pin_pointC P hlt hI hp0 hpN, hr⟩
        rw [outerBody, ite_eq_left hhs, hsh]
      · have hrh : rstK n w (mask w) ng G GI T E h c = 0 := by
          simp [rstK, hlt]
        rw [hrh] at hr
        exact absurd ((foldl_zero_of (step := fun i c => rstK n w (mask w) ng G GI T E i c) hRz _).symm.trans hr).symm hN0
    · have e : h = N := by omega
      subst e
      rw [Nat.sub_self] at hr
      change c = h at hr
      subst hr
      have hns : ¬ c < s.1.size := by rw [hI.1]; exact Nat.lt_irrefl _
      exact Or.inr ⟨_, by simp [outerBody, hns], hI⟩
  · obtain ⟨hcN, c, hc, hI, hr⟩ := hP
    have e : cap = N := by omega
    subst e
    rw [Nat.sub_self] at hr
    change c = cap at hr
    subst hr
    exact hI
  · refine ⟨rfl, rfl, rfl, fun i hi => ?_, fun x' => ?_, fun i hi hi0 => absurd hi (by omega)⟩
    · have e : i = 0 := by omega
      subst e
      simp [initSt, hT0]
    · simp only [initSt]
      rw [Std.HashMap.contains_insert, Std.HashMap.contains_emptyWithCapacity, Bool.or_false,
        beq_iff_eq, hT0]
      constructor
      · intro e
        exact ⟨0, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        have : i = 0 := by omega
        subst this
        exact e

theorem bfsCK_closure (hrun : (List.range N).foldl
      (fun c i => rstK n w (mask w) ng G GI T E i c) 1 = N) (hN0 : N ≠ 0) :
    ∀ i < N, ∀ k < ng, ∃ q < N,
      T q = pcomp n w (mask w) (G k) (pcomp n w (mask w) (T i) (GI k)) := by
  intro i hi k hk
  obtain ⟨c, hc, hne, hle⟩ := foldl_steps_le (step := fun i c => rstK n w (mask w) ng G GI T E i c)
    (fun i => rstK_zero n w (mask w) ng G GI T E i) (fun i c h' => rstK_mono h')
    (List.range N) 1 (by rw [hrun]; exact hN0) i (List.mem_range.2 hi)
  rw [hrun] at hle
  have hne' : rstK n w (mask w) ng G GI T E i c ≠ 0 := hne
  have hlt : i < c := by
    by_contra hnl
    exact hne' (by simp [rstK, hnl])
  have hr : rstK n w (mask w) ng G GI T E i c = cPoint n w (mask w) ng G GI T E i c := by
    simp [rstK, hlt]
  rw [hr, cPoint_eq] at hne' hle
  obtain ⟨c', -, hne2, hle2⟩ := foldl_steps_le
    (step := fun k c => cStep n w (mask w) T (T i) (E i) (G k) (GI k) k c)
    (fun k => cStep_zero n w (mask w) T (T i) (E i) (G k) (GI k) k) (fun k c h' => cStep_mono h')
    (List.range ng) c hne' k (List.mem_range.2 hk)
  obtain ⟨-, -, ⟨q, hq, hTq⟩, -⟩ := cStep_spec (rfl : cStep n w (mask w) T (T i) (E i) (G k) (GI k) k c' = _) hne2
  exact ⟨q, lt_of_lt_of_le hq (le_trans hle2 hle), hTq⟩

theorem orbit_of_bfsCK {n w ng N cap X : Nat} {G GI T E S : Nat → Nat} {gens ginv : Array Tab}
    {x : Tab} (hs : gens.size = ng) (hsi : ginv.size = ng)
    (hg : ∀ k < ng, gens[k]! = unpack n w (G k)) (hgi : ∀ k < ng, ginv[k]! = unpack n w (GI k))
    (hx : x = unpack n w X) (hk : bfsCK n w ng G GI X N T E S = true) (hf : N ≤ cap) :
    treeOK (conjStep n gens ginv) gens.size x (orbitBFS n gens ginv x cap) = true ∧
      (orbitBFS n gens ginv x cap).tabs = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
  have hk' := hk
  unfold bfsCK at hk'
  simp only [CFSG.KS.bAnd_iff] at hk'
  obtain ⟨hsz, hGc, hGIc, hTc, hT0, hdist, hrun⟩ := hk'
  have P : PinFC n w ng N G GI T gens ginv :=
    ⟨hs, hsi, hg, hgi, fun k hk => CFSG.KS.allN_spec hGc k hk,
      fun k hk => CFSG.KS.allN_spec hGIc k hk, fun i hi => CFSG.KS.allN_spec hTc i hi,
      distinctK_inj hdist⟩
  have hR : (List.range N).foldl (fun c i => rstK n w (mask w) ng G GI T E i c) 1 = N := by
    rw [← runCK_eq]
    exact Nat.eq_of_beq_eq_true hrun
  have hNne : N ≠ 0 := by
    intro e
    subst e
    simp at hR
  have hcl := bfsCK_closure hR hNne
  have hx0 : x = unpack n w (T 0) := by
    rw [hx, ← Nat.eq_of_beq_eq_true hT0]
  have hO := pin_outerC P hf hNne hR hx0
  unfold orbitBFS
  rw [CFSG.KS.BfsReplay.bfs_eq, hs]
  generalize Id.run (forIn (List.range' 0 cap) (CFSG.KS.BfsReplay.initSt x cap)
    (CFSG.KS.BfsReplay.outerBody (conjStep n gens ginv) ng)) = s at hO
  obtain ⟨h1, h2, h3, hget, -, htr⟩ := hO
  have htabs : s.1 = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
    apply Array.ext
    · simp [h1]
    · intro i hi1 hi2
      rw [Array.getElem_ofFn, ← getElem!_pos s.1 i hi1, hget i (by omega)]
  refine ⟨?_, htabs⟩
  unfold treeOK
  simp only
  have hinj : ∀ a < s.1.size, ∀ b < s.1.size, s.1[a]! = s.1[b]! → a = b := fun a ha b hb e => by
    rw [hget a (by omega), hget b (by omega)] at e
    exact P.uinj (by omega) (by omega) e
  obtain ⟨hi1, -⟩ := CFSG.KS.BfsReplay.indexOf_spec hinj
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨by omega, by rw [hget 0 (by omega), hx0]⟩,
    CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_⟩
  rw [h1] at hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨?_, CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_⟩, ?_⟩
  · unfold posOf
    exact hi1 i (by omega)
  · obtain ⟨q, hq, hx⟩ := hcl i hi j hj
    have e : conjStep n gens ginv j s.1[i]! = s.1[q]! := by
      rw [hget i hi, hget q hq, hx, P.step hj hi]
    unfold found posOf
    rw [e, hi1 q (by omega)]
    simp [h1, hq]
  · by_cases h0 : i = 0
    · exact Or.inl h0
    · right
      obtain ⟨a1, a2, a3⟩ := htr i hi h0
      exact ⟨⟨a1, a2⟩, a3⟩

end Search

end CFSG.KC.LocalComp.PinSnd

end
