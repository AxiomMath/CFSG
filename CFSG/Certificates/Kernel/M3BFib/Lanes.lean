module

public import Certificates.Data.Kernel.M3BFib.Kit
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

namespace CFSG.KC.M3BF

theorem enc_cons (d : ℕ) (ds : List ℕ) : enc (d :: ds) = d + 64 * enc ds := rfl

theorem digN_succ (n x : ℕ) : digN (n + 1) x = (x % 64) :: digN n (x / 64) := rfl

theorem digN_length : ∀ (n x : ℕ), (digN n x).length = n
  | 0, _ => rfl
  | n + 1, x => by rw [digN_succ, List.length_cons, digN_length n]

theorem digN_enc : ∀ (ds : List ℕ), (∀ d ∈ ds, d < 64) → digN ds.length (enc ds) = ds
  | [], _ => rfl
  | d :: ds, h => by
    have hd := h d List.mem_cons_self
    have ih := digN_enc ds fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.length_cons, digN_succ, enc_cons]
    have e1 : (d + 64 * enc ds) % 64 = d := by omega
    have e2 : (d + 64 * enc ds) / 64 = enc ds := by omega
    rw [e1, e2, ih]

theorem dig_enc {ds : List ℕ} (hl : ds.length = 12) (h : ∀ d ∈ ds, d < 64) : dig (enc ds) = ds := by
  unfold dig
  rw [← hl]
  exact digN_enc ds h

theorem mapMod3_eq : ∀ l : List ℕ,
    List.rec (motive := fun _ => List ℕ) [] (fun d _ ih => List.cons (Nat.mod d 3) ih) l =
      l.map (· % 3)
  | [] => rfl
  | d :: l => by
    change (d % 3) :: _ = _
    rw [mapMod3_eq l, List.map_cons]

theorem dig3_eq (x : ℕ) : dig3 x = (dig x).map (· % 3) := by
  have h := mapMod3_eq (dig x)
  unfold dig3
  exact h

theorem dig_length (x : ℕ) : (dig x).length = 12 := digN_length 12 x

theorem dig3_length (x : ℕ) : (dig3 x).length = 12 := by
  rw [dig3_eq, List.length_map, dig_length]

theorem dig3_lt (x : ℕ) : ∀ d ∈ dig3 x, d < 3 := by
  intro d hd
  rw [dig3_eq, List.mem_map] at hd
  obtain ⟨a, _, rfl⟩ := hd
  exact Nat.mod_lt _ (by norm_num)

theorem dig_enc_dig3 (x : ℕ) : dig (enc (dig3 x)) = dig3 x :=
  dig_enc (dig3_length x) fun d hd => lt_trans (dig3_lt x d hd) (by norm_num)

@[expose] def GoodRow (r : ℕ) : Prop := enc (dig3 r) = r

theorem GoodRow.dig_eq {r : ℕ} (h : GoodRow r) : dig r = dig3 r := by
  rw [← h, dig_enc_dig3, h]

theorem goodRow_red (x : ℕ) : GoodRow (red x) := by
  unfold GoodRow red
  rw [dig3_eq (enc (dig3 x)), dig_enc_dig3]
  congr 1
  conv_rhs => rw [← List.map_id (dig3 x)]
  exact List.map_congr_left fun d hd => Nat.mod_eq_of_lt (dig3_lt x d hd)

theorem dig3_red (x : ℕ) : dig3 (red x) = dig3 x := by
  rw [← (goodRow_red x).dig_eq]
  exact dig_enc_dig3 x

@[expose] def vmD : List ℕ → List (List ℕ) → List ℕ
  | a :: u, p :: P => List.zipWith (fun x y => a * x + y) p (vmD u P)
  | _, _ => List.replicate 12 0

theorem enc_zero12 : enc [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 0 := rfl

theorem enc_zipWith (a : ℕ) : ∀ p q : List ℕ, p.length = q.length →
    a * enc p + enc q = enc (List.zipWith (fun x y => a * x + y) p q)
  | [], [], _ => by simp [enc]
  | x :: p, y :: q, h => by
    rw [List.zipWith_cons_cons, enc_cons, enc_cons, enc_cons, ← enc_zipWith a p q (by simpa using h)]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem vmD_length : ∀ (u : List ℕ) (P : List (List ℕ)), (∀ p ∈ P, p.length = 12) →
    (vmD u P).length = 12
  | a :: u, p :: P, h => by
    rw [vmD, List.length_zipWith, h p List.mem_cons_self,
      vmD_length u P fun q hq => h q (List.mem_cons_of_mem _ hq), min_self]
  | [], _, _ => by simp [vmD]
  | _ :: _, [], _ => by simp [vmD]

theorem vm_cons (a p : ℕ) (u P : List ℕ) : vm (a :: u) (p :: P) = a * p + vm u P := rfl

theorem vm_eq : ∀ (u P : List ℕ), (∀ p ∈ P, GoodRow p) → vm u P = enc (vmD u (P.map dig3))
  | a :: u, p :: P, h => by
    have hp := h p List.mem_cons_self
    have hP : ∀ q ∈ P, GoodRow q := fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [vm_cons, vm_eq u P hP, List.map_cons, vmD, ← enc_zipWith, hp]
    rw [dig3_length, vmD_length]
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, _, rfl⟩ := hq
    exact dig3_length r
  | [], P, _ => by cases P <;> simp [vm, vmD, enc_zero12]
  | _ :: _, [], _ => by simp [vm, vmD, enc_zero12]

theorem getD_zipWith (f : ℕ → ℕ → ℕ) : ∀ (p q : List ℕ) (k : ℕ), k < p.length → k < q.length →
    (List.zipWith f p q).getD k 0 = f (p.getD k 0) (q.getD k 0)
  | x :: p, y :: q, 0, _, _ => rfl
  | x :: p, y :: q, k + 1, h1, h2 => by
    rw [List.zipWith_cons_cons]
    exact getD_zipWith f p q k (by simpa using h1) (by simpa using h2)
  | [], _, _, h1, _ => by simp at h1
  | _ :: _, [], _, _, h2 => by simp at h2

theorem vmD_getD : ∀ (m : ℕ) (u : List ℕ) (P : List (List ℕ)), u.length = m → P.length = m →
    (∀ p ∈ P, p.length = 12) → ∀ k < 12,
    (vmD u P).getD k 0 = ∑ j : Fin m, u.getD j 0 * (P.getD j []).getD k 0
  | 0, [], [], _, _, _, k, hk => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    change (List.replicate 12 0).getD k 0 = 0
    interval_cases k <;> rfl
  | m + 1, a :: u, p :: P, hu, hP, h, k, hk => by
    have hP' : ∀ q ∈ P, q.length = 12 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [vmD, getD_zipWith _ _ _ _ (by rw [h p List.mem_cons_self]; exact hk)
      (by rw [vmD_length u P hP']; exact hk),
      vmD_getD m u P (by simpa using hu) (by simpa using hP) hP' k hk, Fin.sum_univ_succ]
    simp

theorem dig_vm (u P : List ℕ) (hu : u.length = 12) (hu3 : ∀ a ∈ u, a < 3) (hP : P.length = 12)
    (hg : ∀ p ∈ P, GoodRow p) :
    dig (vm u P) = vmD u (P.map dig3) ∧ ∀ k < 12,
      (vmD u (P.map dig3)).getD k 0 = ∑ j : Fin 12, u.getD j 0 * (dig3 (P.getD j 0)).getD k 0 := by
  have hl : ∀ p ∈ P.map dig3, p.length = 12 := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, _, rfl⟩ := hq
    exact dig3_length r
  have hget : ∀ k < 12,
      (vmD u (P.map dig3)).getD k 0 = ∑ j : Fin 12, u.getD j 0 * (dig3 (P.getD j 0)).getD k 0 := by
    intro k hk
    rw [vmD_getD 12 u _ hu (by simpa using hP) hl k hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (j : ℕ) < (P.map dig3).length := by rw [List.length_map, hP]; exact j.isLt
    have h2 : (j : ℕ) < P.length := by rw [hP]; exact j.isLt
    rw [List.getD_eq_getElem _ _ h1, List.getElem_map, List.getD_eq_getElem _ _ h2]
  refine ⟨?_, hget⟩
  rw [vm_eq u P hg]
  refine dig_enc (vmD_length _ _ hl) fun d hd => ?_
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  have hk12 : k < 12 := by rwa [vmD_length _ _ hl] at hk
  rw [← List.getD_eq_getElem _ 0 hk, hget k hk12]
  have hb : ∀ j : Fin 12, u.getD j 0 * (dig3 (P.getD j 0)).getD k 0 ≤ 4 := by
    intro j
    have h1 : u.getD j 0 < 3 := by
      rw [List.getD_eq_getElem _ _ (by rw [hu]; exact j.isLt)]
      exact hu3 _ (List.getElem_mem _)
    have h2 : (dig3 (P.getD j 0)).getD k 0 < 3 := by
      rw [List.getD_eq_getElem _ _ (by rw [dig3_length]; exact hk12)]
      exact dig3_lt _ _ (List.getElem_mem _)
    have : u.getD j 0 ≤ 2 := by omega
    have : (dig3 (P.getD j 0)).getD k 0 ≤ 2 := by omega
    calc _ ≤ 2 * 2 := Nat.mul_le_mul ‹_› ‹_›
      _ = 4 := rfl
  calc ∑ j : Fin 12, u.getD j 0 * (dig3 (P.getD j 0)).getD k 0 ≤ ∑ _j : Fin 12, 4 :=
        Finset.sum_le_sum fun j _ => hb j
    _ < 64 := by simp

end CFSG.KC.M3BF

end
