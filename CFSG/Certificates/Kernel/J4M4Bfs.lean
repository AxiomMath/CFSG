module

public import Certificates.Data.CFSGNative.J4Tree.Node
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

namespace CFSG.KC.J4M4

open CFSG.J4Tree.Native CFSG.J4Tree.Native.Node

variable {α : Type} (gs : List α) (step : α → Code → Code) (x₀ : Code)

@[expose] def ReachLe : ℕ → Code → Prop
  | 0, y => y = x₀
  | n + 1, y => ReachLe n y ∨ ∃ z, ReachLe n z ∧ ∃ g ∈ gs, step g z = y

variable {gs step x₀}

variable (gs step x₀)

structure FoldInv (S₀ : Std.HashSet Code) (F : List Code) (acc : Std.HashSet Code × List Code) :
    Prop where
  sub : ∀ y ∈ S₀, y ∈ acc.1
  new : ∀ y ∈ acc.1, y ∈ S₀ ∨ y ∈ acc.2
  fr : ∀ y ∈ acc.2, y ∈ acc.1
  img : ∀ y ∈ acc.2, ∃ x ∈ F, ∃ g ∈ gs, step g x = y

theorem foldInv_insert {S₀ : Std.HashSet Code} {F : List Code} {acc : Std.HashSet Code × List Code}
    (h : FoldInv gs step S₀ F acc) {x : Code} (hx : x ∈ F) {g : α} (hg : g ∈ gs) :
    FoldInv gs step S₀ F
      (if acc.1.contains (step g x) then acc else (acc.1.insert (step g x), step g x :: acc.2)) ∧
    (∀ y ∈ acc.1, y ∈ (if acc.1.contains (step g x) then acc
      else (acc.1.insert (step g x), step g x :: acc.2)).1) ∧
    step g x ∈ (if acc.1.contains (step g x) then acc
      else (acc.1.insert (step g x), step g x :: acc.2)).1 := by
  split_ifs with hc
  · exact ⟨h, fun y hy => hy, Std.HashSet.contains_iff_mem.mp hc⟩
  · refine ⟨⟨fun y hy => Std.HashSet.mem_insert.mpr (Or.inr (h.sub y hy)), fun y hy => ?_,
      fun y hy => ?_, fun y hy => ?_⟩, fun y hy => Std.HashSet.mem_insert.mpr (Or.inr hy),
      Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))⟩
    · rcases Std.HashSet.mem_insert.mp hy with hy | hy
      · exact Or.inr (List.mem_cons.mpr (Or.inl (beq_iff_eq.mp hy).symm))
      · rcases h.new y hy with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))
      · exact Std.HashSet.mem_insert.mpr (Or.inr (h.fr y hy))
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨x, hx, g, hg, rfl⟩
      · exact h.img y hy

theorem foldInv_inner {S₀ : Std.HashSet Code} {F : List Code} {x : Code} (hx : x ∈ F) :
    ∀ (l : List α) (acc : Std.HashSet Code × List Code), (∀ g ∈ l, g ∈ gs) →
      FoldInv gs step S₀ F acc →
      let R := l.foldl (fun (acc : Std.HashSet Code × List Code) g =>
        if acc.1.contains (step g x) then acc
        else (acc.1.insert (step g x), step g x :: acc.2)) acc
      FoldInv gs step S₀ F R ∧ (∀ y ∈ acc.1, y ∈ R.1) ∧ ∀ g ∈ l, step g x ∈ R.1
  | [], acc, _, h => ⟨h, fun _ hy => hy, fun _ hg => absurd hg List.not_mem_nil⟩
  | g :: l, acc, hl, h => by
    obtain ⟨h1, h2, h3⟩ := foldInv_insert gs step h hx (hl g List.mem_cons_self)
    obtain ⟨i1, i2, i3⟩ := foldInv_inner hx l _
      (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) h1
    refine ⟨i1, fun y hy => i2 y (h2 y hy), fun g' hg' => ?_⟩
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact i2 _ h3
    · exact i3 g' hg'

theorem foldInv_outer {S₀ : Std.HashSet Code} {F : List Code} :
    ∀ (l : List Code) (acc : Std.HashSet Code × List Code), (∀ x ∈ l, x ∈ F) →
      FoldInv gs step S₀ F acc →
      let R := l.foldl (fun acc x => gs.foldl (fun (acc : Std.HashSet Code × List Code) g =>
        if acc.1.contains (step g x) then acc
        else (acc.1.insert (step g x), step g x :: acc.2)) acc) acc
      FoldInv gs step S₀ F R ∧ (∀ y ∈ acc.1, y ∈ R.1) ∧ ∀ x ∈ l, ∀ g ∈ gs, step g x ∈ R.1
  | [], acc, _, h => ⟨h, fun _ hy => hy, fun _ hx => absurd hx List.not_mem_nil⟩
  | x :: l, acc, hl, h => by
    obtain ⟨h1, h2, h3⟩ := foldInv_inner gs step (S₀ := S₀) (hl x List.mem_cons_self) gs acc
      (fun g hg => hg) h
    obtain ⟨i1, i2, i3⟩ := foldInv_outer l _
      (fun x' hx' => hl x' (List.mem_cons_of_mem _ hx')) h1
    refine ⟨i1, fun y hy => i2 y (h2 y hy), fun x' hx' g hg => ?_⟩
    rcases List.mem_cons.mp hx' with rfl | hx'
    · exact i2 _ (h3 g hg)
    · exact i3 x' hx' g hg

theorem bfsStep_spec (S : Std.HashSet Code) (F : List Code) :
    (∀ y ∈ S, y ∈ (bfsStep gs step S F).1) ∧
    (∀ x ∈ F, ∀ g ∈ gs, step g x ∈ (bfsStep gs step S F).1) ∧
    (∀ y ∈ (bfsStep gs step S F).1, y ∈ S ∨ y ∈ (bfsStep gs step S F).2) ∧
    (∀ y ∈ (bfsStep gs step S F).2, y ∈ (bfsStep gs step S F).1) ∧
    (∀ y ∈ (bfsStep gs step S F).2, ∃ x ∈ F, ∃ g ∈ gs, step g x = y) := by
  have h0 : FoldInv gs step S F (S, []) :=
    ⟨fun _ hy => hy, fun _ hy => Or.inl hy, fun _ hy => absurd hy List.not_mem_nil,
      fun _ hy => absurd hy List.not_mem_nil⟩
  obtain ⟨i1, i2, i3⟩ := foldInv_outer gs step F (S, []) (fun x hx => hx) h0
  exact ⟨i2, i3, i1.new, i1.fr, i1.img⟩

def BInv (r : ℕ) (st : Std.HashSet Code × List Code) : Prop :=
  (∀ y, ReachLe gs step x₀ r y → y ∈ st.1) ∧
    (∀ y ∈ st.1, y ∉ st.2 → ∀ g ∈ gs, step g y ∈ st.1) ∧ ∀ y ∈ st.2, y ∈ st.1

theorem bInv_step {r : ℕ} {st : Std.HashSet Code × List Code} (h : BInv gs step x₀ r st) :
    BInv gs step x₀ (r + 1) (bfsStep gs step st.1 st.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨s1, s2, s3, s4, -⟩ := bfsStep_spec gs step st.1 st.2
  refine ⟨fun y hy => ?_, fun y hy hny g hg => ?_, s4⟩
  · rcases hy with hy | ⟨z, hz, g, hg, rfl⟩
    · exact s1 y (h1 y hy)
    · by_cases hzF : z ∈ st.2
      · exact s2 z hzF g hg
      · exact s1 _ (h2 z (h1 z hz) hzF g hg)
  · rcases s3 y hy with hyS | hyF
    · by_cases hyF : y ∈ st.2
      · exact s2 y hyF g hg
      · exact s1 _ (h2 y hyS hyF g hg)
    · exact absurd hyF hny

theorem bInv_closed {r : ℕ} {st : Std.HashSet Code × List Code} (h : BInv gs step x₀ r st)
    (he : st.2 = []) : ∀ k y, ReachLe gs step x₀ (r + k) y → y ∈ st.1 := by
  intro k
  induction k with
  | zero => exact h.1
  | succ k ih =>
    intro y hy
    rcases hy with hy | ⟨z, hz, g, hg, rfl⟩
    · exact ih y hy
    · exact h.2.1 z (ih z hz) (by rw [he]; exact List.not_mem_nil) g hg

theorem bfsRun_complete : ∀ (n : ℕ) (st : Std.HashSet Code × List Code) (r : ℕ),
    BInv gs step x₀ r st → ∀ y, ReachLe gs step x₀ (r + n) y → y ∈ (bfsRun gs step n st).1
  | 0, st, r, h, y, hy => by
    rw [bfsRun]
    exact h.1 y hy
  | n + 1, st, r, h, y, hy => by
    rw [bfsRun]
    split_ifs with he
    · exact bInv_closed gs step x₀ h (List.isEmpty_iff.mp he) (n + 1) y hy
    · have e : r + (n + 1) = r + 1 + n := by omega
      rw [e] at hy
      exact bfsRun_complete n _ (r + 1) (bInv_step gs step x₀ h) y hy

theorem bfsFrom_complete {n : ℕ} {y : Code} (h : ReachLe gs step x₀ n y) :
    y ∈ bfsFrom gs step x₀ n := by
  refine bfsRun_complete gs step x₀ n _ 0 ⟨fun z hz => ?_, fun z hz hnz => ?_, fun z hz => ?_⟩ y
    (by rwa [Nat.zero_add])
  · rw [show z = x₀ from hz]
    exact Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))
  · rcases Std.HashSet.mem_insert.mp hz with hz | hz
    · exact absurd (List.mem_singleton.mpr (beq_iff_eq.mp hz).symm) hnz
    · exact absurd hz (Std.HashSet.not_mem_empty)
  · rw [List.mem_singleton.mp hz]
    exact Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))

theorem bfsRun_sound (P : Code → Prop) (hcl : ∀ y, P y → ∀ g ∈ gs, P (step g y)) :
    ∀ (n : ℕ) (st : Std.HashSet Code × List Code), (∀ y ∈ st.1, P y) → (∀ y ∈ st.2, P y) →
      ∀ y ∈ (bfsRun gs step n st).1, P y
  | 0, st, h1, _, y, hy => by
    rw [bfsRun] at hy
    exact h1 y hy
  | n + 1, st, h1, h2, y, hy => by
    rw [bfsRun] at hy
    split_ifs at hy
    · exact h1 y hy
    · obtain ⟨-, -, s3, -, s5⟩ := bfsStep_spec gs step st.1 st.2
      refine bfsRun_sound P hcl n _ (fun z hz => ?_) (fun z hz => ?_) y hy
      · rcases s3 z hz with hz | hz
        · exact h1 z hz
        · obtain ⟨x, hx, g, hg, rfl⟩ := s5 z hz
          exact hcl x (h2 x hx) g hg
      · obtain ⟨x, hx, g, hg, rfl⟩ := s5 z hz
        exact hcl x (h2 x hx) g hg

theorem bfsFrom_mem_iff {n : ℕ} (P : Code → Prop) (h0 : P x₀)
    (hcl : ∀ y, P y → ∀ g ∈ gs, P (step g y)) (hr : ∀ y, P y → ReachLe gs step x₀ n y)
    (y : Code) : y ∈ bfsFrom gs step x₀ n ↔ P y := by
  refine ⟨fun hy => bfsRun_sound gs step P hcl n _ (fun z hz => ?_) (fun z hz => ?_) y hy,
    fun hy => bfsFrom_complete gs step x₀ (hr y hy)⟩
  · rcases Std.HashSet.mem_insert.mp hz with hz | hz
    · rw [← beq_iff_eq.mp hz]
      exact h0
    · exact absurd hz (Std.HashSet.not_mem_empty)
  · rw [List.mem_singleton.mp hz]
    exact h0

theorem closedUnder_of_mem_iff {S : Std.HashSet Code} (P : Code → Prop)
    (hS : ∀ y, y ∈ S ↔ P y) (hcl : ∀ y, P y → ∀ g ∈ gs, P (step g y)) :
    closedUnder gs step S = true := by
  unfold closedUnder
  rw [List.all_eq_true]
  intro x hx
  rw [List.all_eq_true]
  intro g hg
  rw [Std.HashSet.contains_iff_mem, hS]
  exact hcl x ((hS x).mp (Std.HashSet.mem_toList.mp hx)) g hg

theorem size_of_mem_iff {S : Std.HashSet Code} {β : Type} (R : Code → β → Prop) (L : List β)
    (hS : ∀ y, y ∈ S ↔ ∃ k ∈ L, R y k) (hR1 : ∀ y y' k, R y k → R y' k → y = y')
    (hR2 : ∀ y k k', k ∈ L → k' ∈ L → R y k → R y k' → k = k') (hR3 : ∀ k ∈ L, ∃ y, R y k)
    (hL : L.Nodup) :
    S.size = L.length := by
  classical
  let g : {k // k ∈ L} → Code := fun k => Classical.choose (hR3 k.1 k.2)
  have hg : ∀ k : {k // k ∈ L}, R (g k) k.1 := fun k => Classical.choose_spec (hR3 k.1 k.2)
  have hperm : S.toList.Perm (L.attach.map g) := by
    have hnd : S.toList.Nodup :=
      Std.HashSet.distinct_toList.imp fun {a b} h hab => by simp [hab] at h
    refine (List.perm_ext_iff_of_nodup hnd ?_).mpr fun y => ?_
    · refine (List.nodup_map_iff_inj_on (List.nodup_attach.mpr hL)).mpr ?_
      intro a _ b _ e
      exact Subtype.ext (hR2 _ _ _ a.2 b.2 (hg a) (e ▸ hg b))
    · rw [Std.HashSet.mem_toList, hS, List.mem_map]
      constructor
      · rintro ⟨k, hk, hy⟩
        exact ⟨⟨k, hk⟩, List.mem_attach _ _, hR1 _ _ _ (hg ⟨k, hk⟩) hy⟩
      · rintro ⟨k, -, rfl⟩
        exact ⟨k.1, k.2, hg k⟩
  rw [← Std.HashSet.length_toList, hperm.length_eq, List.length_map, List.length_attach]

end CFSG.KC.J4M4
