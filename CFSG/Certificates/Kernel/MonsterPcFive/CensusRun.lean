module

public import Certificates.Data.Kernel.MonsterPcFive.Census
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.MonPcFive

theorem memK_spec {n : ℕ} : ∀ {l : List ℕ}, memK n l = true → n ∈ l
  | [], h => by simp [memK] at h
  | a :: l, h => by
    unfold memK at h
    rw [Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memK_spec h)

theorem nthN_cons_succ (a : ℕ) (l : List ℕ) (k : ℕ) : nthN (a :: l) (k + 1) = nthN l k := rfl

theorem cosRun_spec {rcs : List ℕ} : ∀ {k : ℕ} {ds : List ℕ}, cosRun rcs k ds = true →
    ∀ i < ds.length, cosOK rcs (k + i) (nthN ds i) = true
  | _, [], _, i, hi => absurd hi (by simp)
  | k, d :: ds, h, i, hi => by
    unfold cosRun at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero => simpa [nthN] using h.1
    | succ i =>
      have e : k + (i + 1) = k + 1 + i := by omega
      rw [e, nthN_cons_succ]
      exact cosRun_spec h.2 i (by simpa using hi)

theorem ptsRun_spec {rep : List ℕ} {nc : ℕ} {t : V9} {m : ℕ} : ∀ {j : ℕ} {ds : List ℕ},
    ptsRun rep nc t m j ds = true → ∀ i < ds.length, ptOK rep nc t (ptVec m (j + i)) (nthN ds i) = true
  | _, [], _, i, hi => absurd hi (by simp)
  | j, d :: ds, h, i, hi => by
    unfold ptsRun at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero => simpa [nthN] using h.1
    | succ i =>
      have e : j + (i + 1) = j + 1 + i := by omega
      rw [e, nthN_cons_succ]
      exact ptsRun_spec h.2 i (by simpa using hi)

@[expose] def RepGood (rcs rep : List ℕ) (nc ρ : ℕ) : Prop :=
  ∃ c0 c1 c2 c3 s0 s1 s2 s3 m : ℕ, ∃ ds : List ℕ,
    colOK (cosT (nthN rcs ρ)) c0 c1 c2 c3 = true ∧ piOK c0 c1 c2 c3 s0 s1 s2 s3 m = true ∧
      ds.length = ptCnt m ∧ ∀ j < ptCnt m, ptOK rep nc (cosT (nthN rcs ρ)) (ptVec m j) (nthN ds j) = true

theorem repsRun_spec {rcs rep : List ℕ} {nc : ℕ} : ∀ {r n : ℕ} {hs ps : List ℕ},
    repsRun rcs rep nc r n hs ps = true → ∀ i < n, RepGood rcs rep nc (r + i)
  | _, 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | r, n + 1, c0 :: c1 :: c2 :: c3 :: s0 :: s1 :: s2 :: s3 :: m :: hs, ps, h, i, hi => by
    unfold repsRun at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨hc, hp⟩, hl⟩, hpts⟩, hrest⟩ := h
    cases i with
    | zero =>
      refine ⟨c0, c1, c2, c3, s0, s1, s2, s3, m, ps.take (ptCnt m), hc, hp, hl, fun j hj => ?_⟩
      have := ptsRun_spec hpts j (by omega)
      simpa using this
    | succ i =>
      have e : r + (i + 1) = r + 1 + i := by omega
      rw [e]
      exact repsRun_spec hrest i (by omega)
  | _, _ + 1, [], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_, _], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_, _, _], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_, _, _, _], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_, _, _, _, _], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_, _, _, _, _, _], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_, _, _, _, _, _, _], _, h, _, _ => by simp [repsRun] at h
  | _, _ + 1, [_, _, _, _, _, _, _, _], _, h, _, _ => by simp [repsRun] at h

theorem exists_ptVec (m : ℕ) {c : ℕ} (hc : c < 625) (hJ : ∀ i < 4, inJ m i = false → d4 c i = 0) :
    ∃ j < ptCnt m, ptVec m j = c := by
  have h0 : inJ m 0 = false → c / 125 % 5 = 0 := hJ 0 (by norm_num)
  have h1 : inJ m 1 = false → c / 25 % 5 = 0 := hJ 1 (by norm_num)
  have h2 : inJ m 2 = false → c / 5 % 5 = 0 := hJ 2 (by norm_num)
  have h3 : inJ m 3 = false → c % 5 = 0 := hJ 3 (by norm_num)
  unfold ptCnt ptVec
  cases hb0 : inJ m 0 <;> cases hb1 : inJ m 1 <;> cases hb2 : inJ m 2 <;> cases hb3 : inJ m 3 <;>
    simp only [hb0, hb1, hb2, hb3, cond_true, cond_false, forall_const, Bool.true_eq_false,
      false_implies] at h0 h1 h2 h3 ⊢
  · exact ⟨0, by norm_num, by omega⟩
  · exact ⟨c % 5, by omega, by omega⟩
  · exact ⟨c / 5 % 5, by omega, by omega⟩
  · exact ⟨c % 25, by omega, by omega⟩
  · exact ⟨c / 25 % 5, by omega, by omega⟩
  · exact ⟨c / 25 % 5 * 5 + c % 5, by omega, by omega⟩
  · exact ⟨c / 5 % 25, by omega, by omega⟩
  · exact ⟨c % 125, by omega, by omega⟩
  · exact ⟨c / 125, by omega, by omega⟩
  · exact ⟨c / 125 * 5 + c % 5, by omega, by omega⟩
  · exact ⟨c / 125 * 5 + c / 5 % 5, by omega, by omega⟩
  · exact ⟨c / 125 * 25 + c % 25, by omega, by omega⟩
  · exact ⟨c / 25, by omega, by omega⟩
  · exact ⟨c / 25 * 5 + c % 5, by omega, by omega⟩
  · exact ⟨c / 5, by omega, by omega⟩
  · exact ⟨c, by omega, by omega⟩

end CFSG.KC.MonPcFive

end
