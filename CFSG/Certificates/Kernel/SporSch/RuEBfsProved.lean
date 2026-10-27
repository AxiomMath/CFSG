module

public import CFSG.Certificates.Kernel.SporSch.RuEBfsGen
import all CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
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
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KS.SporSch.EB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.KC.BfsPin

@[expose] def natB (z : Array ℕ) (ngs : Array (Array ℕ)) : Array (Array ℕ) × Array ℕ × Array ℕ :=
  Id.run do
  let mut els : Array (Array ℕ) := #[z]
  let mut par : Array ℕ := #[0]
  let mut gl : Array ℕ := #[0]
  let mut head := 0
  for _ in [0:8] do
    if head < els.size then
      let e := els[head]!
      for g in [0:2] do
        let c := ruConjA ngs[g]! e
        if !(els.any fun x => eqA 4060 x c) then
          els := els.push c
          par := par.push head
          gl := gl.push g
      head := head + 1
  return (els, par, gl)

@[expose] def natStep (ngs : Array (Array ℕ)) (g : ℕ) (e : Array ℕ) (h : ℕ)
    (s : Array (Array ℕ) × Array ℕ × Array ℕ) : Array (Array ℕ) × Array ℕ × Array ℕ :=
  if !(s.1.any fun x => eqA 4060 x (ruConjA ngs[g]! e)) then
    (s.1.push (ruConjA ngs[g]! e), s.2.1.push h, s.2.2.push g)
  else s

@[expose] def natRound (ngs : Array (Array ℕ)) (s : Array (Array ℕ) × Array ℕ × Array ℕ × ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ × ℕ :=
  if s.2.2.2 < s.1.size then
    (fun t : Array (Array ℕ) × Array ℕ × Array ℕ => (t.1, t.2.1, t.2.2, s.2.2.2 + 1))
      (natStep ngs 1 s.1[s.2.2.2]! s.2.2.2 (natStep ngs 0 s.1[s.2.2.2]! s.2.2.2 (s.1, s.2.1, s.2.2.1)))
  else s

theorem ite_yield {β : Type} (c : Prop) [Decidable c] (X Y : β) :
    (if c then (pure (ForInStep.yield X) : Id (ForInStep β)) else pure (ForInStep.yield Y)) =
      pure (ForInStep.yield (if c then X else Y)) := by
  split <;> rfl

theorem foldl_iter {β : Type} (F : β → β) : ∀ (n s : ℕ) (b : β),
    (List.range' s n).foldl (fun b _ => F b) b = F^[n] b
  | 0, _, _ => rfl
  | n + 1, s, b => by
    rw [List.range'_succ, List.foldl_cons, foldl_iter F n, Function.iterate_succ_apply]

theorem iter_congr {β : Type} {F G : β → β} (h : ∀ b, F b = G b) : ∀ (n : ℕ) (b : β),
    F^[n] b = G^[n] b
  | 0, _ => rfl
  | n + 1, b => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h, iter_congr h n]

theorem natB_eq (z : Array ℕ) (ngs : Array (Array ℕ)) :
    natB z ngs = (((natRound ngs)^[8] (#[z], #[0], #[0], 0)).1,
      ((natRound ngs)^[8] (#[z], #[0], #[0], 0)).2.1,
      ((natRound ngs)^[8] (#[z], #[0], #[0], 0)).2.2.1) := by
  unfold natB
  have h2 : List.range' 0 ((2 - 0 + 1 - 1) / 1) = [0, 1] := rfl
  have h8 : List.range' 0 ((8 - 0 + 1 - 1) / 1) = List.range' 0 8 := rfl
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ite_yield, pure_bind, h2, h8, List.foldl_cons, List.foldl_nil,
    foldl_iter]
  rw [iter_congr (G := natRound ngs) (fun b => ?_)]
  · rfl
  · unfold natRound natStep
    rfl

@[expose] def CK (x : ℕ) : Prop := canonK 4060 12 (mask 12) (4060 * 12) x = true

@[expose] noncomputable def UL (L : List ℕ) : Array (Array ℕ) := (L.map (unpack 4060 12)).toArray

theorem ck_left {P Q : ℕ} (hs : szOK 4060 12 = true)
    (h : permOK 4060 12 (mask 12) (4060 * 12) P Q = true) : CK P := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  unfold CK canonK
  simp only [bAnd_iff]
  exact ⟨hs, Nat.beq_eq.mpr h1, CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩

theorem ck_right {P Q : ℕ} (hs : szOK 4060 12 = true)
    (h : permOK 4060 12 (mask 12) (4060 * 12) P Q = true) : CK Q := by
  obtain ⟨-, h2, -⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  unfold CK canonK
  simp only [bAnd_iff]
  exact ⟨hs, Nat.beq_eq.mpr h2, CFSG.KS.Raw.Orb.allN_iff.2 fun i hi =>
    Nat.blt_eq.mpr (CFSG.KS.Prim.perm_inv_lt h i hi)⟩

theorem conj_unpack {N NI x : ℕ} (hN : CK N) (hNI : CK NI) (hx : CK x)
    (hp : permOK 4060 12 (mask 12) (4060 * 12) N NI = true) :
    ruConjA (unpack 4060 12 N) (unpack 4060 12 x) = unpack 4060 12 (conjP N NI x) ∧
      CK (conjP N NI x) := by
  have e : conjP N NI x = pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) N x) NI := rfl
  rw [e]
  refine ⟨?_, canonK_pcomp (canonK_pcomp hN hx) hNI⟩
  unfold ruConjA
  rw [(invEqK_sound (p := N) hp).1, compA_unpack hN hx, compA_unpack (canonK_pcomp hN hx) hNI]

theorem lenNL_eq : ∀ L : List ℕ, lenNL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenNL_eq L)

theorem beq_symm (a b : ℕ) : Nat.beq a b = Nat.beq b a :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, Nat.beq_eq]; exact eq_comm)

theorem any_unpack {c : ℕ} (hc : CK c) : ∀ L : List ℕ, (∀ y ∈ L, CK y) →
    (L.map (unpack 4060 12)).any (fun x => eqA 4060 x (unpack 4060 12 c)) = memNL c L
  | [], _ => rfl
  | y :: L, hL => by
    rw [List.map_cons, List.any_cons, eqA_unpack (hL y List.mem_cons_self) hc,
      any_unpack hc L fun y' h' => hL y' (List.mem_cons_of_mem y h'), beq_symm]
    change _ = bIf(Nat.beq c y, true, memNL c L)
    cases Nat.beq c y <;> rfl

@[expose] def Rel (s : Array (Array ℕ) × Array ℕ × Array ℕ × ℕ) (k : List ℕ × List ℕ × List ℕ × ℕ) :
    Prop :=
  s.1 = UL k.1 ∧ s.2.1 = k.2.1.toArray ∧ s.2.2.1 = k.2.2.1.toArray ∧ (∀ y ∈ k.1, CK y) ∧
    (s.2.2.2 = k.2.2.2 ∨ (k.1.length ≤ s.2.2.2 ∧ k.1.length ≤ k.2.2.2))

theorem gen_rel {ngs : Array (Array ℕ)} {g h : ℕ} {N NI x : ℕ} (hg : ngs[g]! = unpack 4060 12 N)
    (hN : CK N) (hNI : CK NI) (hx : CK x) (hp : permOK 4060 12 (mask 12) (4060 * 12) N NI = true)
    (A B C : List ℕ) (hA : ∀ y ∈ A, CK y) :
    natStep ngs g (unpack 4060 12 x) h (UL A, B.toArray, C.toArray) =
      (UL (ebfsGen (conjP N NI x) h g (A, B, C)).1,
        (ebfsGen (conjP N NI x) h g (A, B, C)).2.1.toArray,
        (ebfsGen (conjP N NI x) h g (A, B, C)).2.2.toArray) ∧
      ∀ y ∈ (ebfsGen (conjP N NI x) h g (A, B, C)).1, CK y := by
  obtain ⟨hc, hcan⟩ := conj_unpack hN hNI hx hp
  unfold natStep ebfsGen
  dsimp only
  rw [hg, hc]
  have hany : (UL A).any (fun y => eqA 4060 y (unpack 4060 12 (conjP N NI x))) =
      memNL (conjP N NI x) A := by
    rw [UL, ← Array.any_toList, List.toList_toArray]
    exact any_unpack hcan A hA
  rw [hany]
  cases memNL (conjP N NI x) A
  · refine ⟨?_, fun y hy => ?_⟩
    · simp [UL]
    · rcases List.mem_append.1 hy with hy | hy
      · exact hA y hy
      · rw [List.mem_singleton.1 hy]
        exact hcan
  · exact ⟨rfl, hA⟩

theorem getD_unpack {A : List ℕ} {h : ℕ} (hh : h < A.length) :
    (UL A)[h]! = unpack 4060 12 (A.getD h 0) := by
  rw [UL, getElem!_pos _ h (by simpa using hh)]
  simp [List.getElem?_eq_getElem hh]

theorem round_rel {ngs : Array (Array ℕ)} {N0 N1 N0I N1I : ℕ}
    (hg0 : ngs[0]! = unpack 4060 12 N0) (hg1 : ngs[1]! = unpack 4060 12 N1)
    (hN0 : CK N0) (hN0I : CK N0I) (hN1 : CK N1) (hN1I : CK N1I)
    (hp0 : permOK 4060 12 (mask 12) (4060 * 12) N0 N0I = true)
    (hp1 : permOK 4060 12 (mask 12) (4060 * 12) N1 N1I = true)
    {s : Array (Array ℕ) × Array ℕ × Array ℕ × ℕ} {k : List ℕ × List ℕ × List ℕ × ℕ}
    (hr : Rel s k) : Rel (natRound ngs s) (ebfsRound N0 N1 N0I N1I k) := by
  obtain ⟨a, b, c, hn⟩ := s
  obtain ⟨A, B, C, hk⟩ := k
  obtain ⟨rfl, rfl, rfl, hcan, hh⟩ := hr
  dsimp only at hh hcan
  have hsz : (UL A).size = A.length := by simp [UL]
  unfold natRound ebfsRound
  dsimp only
  rw [lenNL_eq, hsz]
  by_cases hlt : hn < A.length
  · have hkn : hn = hk := by
      rcases hh with h | h
      · exact h
      · omega
    subst hkn
    rw [ite_eq_left hlt, Nat.blt_eq.mpr hlt]
    have hx : CK (A.getD hn 0) := hcan _ (by
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt)
    rw [getD_unpack hlt]
    obtain ⟨e1, c1⟩ := gen_rel (h := hn) hg0 hN0 hN0I hx hp0 A B C hcan
    rw [e1]
    obtain ⟨e2, c2⟩ := gen_rel (h := hn) hg1 hN1 hN1I hx hp1 _ _ _ c1
    rw [e2]
    exact ⟨rfl, rfl, rfl, c2, Or.inl rfl⟩
  · rw [ite_eq_right hlt]
    have hb : Nat.blt hk A.length = false := by
      rcases hh with h | h
      · rw [← h]
        exact Bool.eq_false_iff.2 fun e => hlt (Nat.blt_eq.mp e)
      · exact Bool.eq_false_iff.2 fun e => absurd (Nat.blt_eq.mp e) (by omega)
    rw [hb]
    change Rel (UL A, B.toArray, C.toArray, hn) (A, B, C, hk + 1)
    refine ⟨rfl, rfl, rfl, hcan, Or.inr ⟨?_, ?_⟩⟩
    · change A.length ≤ hn
      omega
    · change A.length ≤ hk + 1
      rcases hh with h | h
      · omega
      · omega

theorem run_rel {ngs : Array (Array ℕ)} {z : Array ℕ} {Z N0 N1 N0I N1I : ℕ}
    (hz : z = unpack 4060 12 Z) (hZ : CK Z)
    (hg0 : ngs[0]! = unpack 4060 12 N0) (hg1 : ngs[1]! = unpack 4060 12 N1)
    (hN0 : CK N0) (hN0I : CK N0I) (hN1 : CK N1) (hN1I : CK N1I)
    (hp0 : permOK 4060 12 (mask 12) (4060 * 12) N0 N0I = true)
    (hp1 : permOK 4060 12 (mask 12) (4060 * 12) N1 N1I = true) :
    ∀ m, Rel ((natRound ngs)^[m] (#[z], #[0], #[0], 0)) (ebfsRun N0 N1 N0I N1I Z m)
  | 0 => by
    change Rel (#[z], #[0], #[0], 0) ([Z], [0], [0], 0)
    refine ⟨?_, rfl, rfl, fun y hy => ?_, Or.inl rfl⟩
    · rw [hz]
      simp [UL]
    · rw [List.mem_singleton.1 hy]
      exact hZ
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    exact round_rel hg0 hg1 hN0 hN0I hN1 hN1I hp0 hp1
      (run_rel hz hZ hg0 hg1 hN0 hN0I hN1 hN1I hp0 hp1 m)

theorem pair0 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[0]! = a := rfl

theorem pair1 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[1]! = b := rfl

theorem natB_sound {z n0 n1 : Array ℕ} {Z N0 N1 N0I N1I : ℕ} (hz : z = unpack 4060 12 Z)
    (hc : canonK 4060 12 (mask 12) (4060 * 12) Z = true)
    (h0 : n0 = unpack 4060 12 N0) (h1 : n1 = unpack 4060 12 N1)
    (hp0 : permOK 4060 12 (mask 12) (4060 * 12) N0 N0I = true)
    (hp1 : permOK 4060 12 (mask 12) (4060 * 12) N1 N1I = true) :
    natB z #[n0, n1] = (((ebfsK N0 N1 N0I N1I Z).1.map (unpack 4060 12)).toArray,
      (ebfsK N0 N1 N0I N1I Z).2.1.toArray, (ebfsK N0 N1 N0I N1I Z).2.2.toArray) := by
  have hs : szOK 4060 12 = true := rfl
  obtain ⟨e1, e2, e3, -, -⟩ := run_rel (ngs := #[n0, n1]) hz hc (by rw [pair0, h0])
    (by rw [pair1, h1]) (ck_left hs hp0) (ck_right hs hp0) (ck_left hs hp1) (ck_right hs hp1)
    hp0 hp1 8
  have hK : ebfsK N0 N1 N0I N1I Z = ((ebfsRun N0 N1 N0I N1I Z 8).1,
      (ebfsRun N0 N1 N0I N1I Z 8).2.1, (ebfsRun N0 N1 N0I N1I Z 8).2.2.1) := rfl
  rw [hK, natB_eq, e1, e2, e3]
  generalize ebfsRun N0 N1 N0I N1I Z 8 = K
  rfl

end CFSG.KS.SporSch.EB

end

public section

namespace CFSG.KS.SporSch

theorem ebfsK_sound_gen_proved (t : String) : EbfsGen t := by
  intro Z N0 N1 N0I N1I hZ hc h0 h1 hp0 hp1
  exact CFSG.KS.SporSch.EB.natB_sound hZ hc h0 h1 hp0 hp1

end CFSG.KS.SporSch

end
