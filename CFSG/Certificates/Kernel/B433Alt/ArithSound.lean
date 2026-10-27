module

public import Certificates.Data.Kernel.B433Alt.Arith
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
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.B4A

theorem ar_sB (v : ℕ) (k : ℕ → Bool) : sB v k = k v := by cases v <;> rfl

theorem ar_sN (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

theorem ar_andB (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem ar_orB (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem ar_notB (a : Bool) : notB a = !a := by cases a <;> rfl

theorem ar_mem_divsOf (F : List (ℕ × ℕ)) (hF : ∀ pe ∈ F, Nat.Prime pe.1) :
    ∀ d, d ∣ (F.map fun pe => pe.1 ^ pe.2).prod → d ∈ divsOf F := by
  induction F with
  | nil =>
    intro d hd
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at hd
    simp [divsOf, hd]
  | cons pe F ih =>
    intro d hd
    have hp : pe.1.Prime := hF pe List.mem_cons_self
    simp only [List.map_cons, List.prod_cons] at hd
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).1 h₁
    have h₂' := ih (fun pe' h => hF pe' (List.mem_cons_of_mem _ h)) d₂ h₂
    simp only [divsOf, List.foldr_cons] at h₂' ⊢
    rw [List.mem_flatMap]
    exact ⟨d₂, h₂', List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), Nat.mul_comm _ _⟩⟩

theorem ar_rot {m s R u : ℕ} (hs : s < m) (hu : u < m) (hR : R.testBit u = true) :
    (ssRot m s R).testBit ((u + s) % m) = true := by
  unfold ssRot ones
  change ((R <<< s ||| R >>> (m - s)) &&& ((1 <<< m) - 1)).testBit ((u + s) % m) = true
  rw [Nat.one_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hlt : (u + s) % m < m := Nat.mod_lt _ (by omega)
  by_cases h : u + s < m
  · rw [Nat.mod_eq_of_lt h]
    have e : u + s - s = u := by omega
    simp [e, hR, h]
  · have e : (u + s) % m = u + s - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have e2 : m - s + (u + s - m) = u := by omega
    rw [e2, hR]
    have hlt2 : u + s - m < m := by omega
    simp [hlt2]

theorem ar_rot_lt (m s R : ℕ) : ssRot m s R < 2 ^ m := by
  unfold ssRot ones
  change (R <<< s ||| R >>> (m - s)) &&& ((1 <<< m) - 1) < 2 ^ m
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos m)

noncomputable def arLoop (w : ℕ → ℕ) (m : ℕ) (idx : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat) (fun R => R)
    (fun j _ ih R => sN (Nat.lor R (ssRot m (Nat.mod (w j) m) R)) ih) idx

theorem ar_loop_inv (w : ℕ → ℕ) {m : ℕ} (hm : 0 < m) (idx : List ℕ) :
    ∀ (S : Finset ℕ) (R : ℕ), R < 2 ^ m → (∀ U ⊆ S, R.testBit ((∑ j ∈ U, w j) % m) = true) →
      ∀ U ⊆ S ∪ idx.toFinset, (arLoop w m idx R).testBit ((∑ j ∈ U, w j) % m) = true := by
  induction idx with
  | nil =>
    intro S R _ hR U hU
    exact hR U (by simpa using hU)
  | cons j l ih =>
    intro S R hR hbits U hU
    have e : arLoop w m (j :: l) R = arLoop w m l (Nat.lor R (ssRot m (Nat.mod (w j) m) R)) :=
      ar_sN _ _
    rw [e]
    refine ih (insert j S) _ ?_ ?_ U ?_
    · exact Nat.or_lt_two_pow hR (ar_rot_lt _ _ _)
    · intro V hV
      change (R ||| ssRot m (w j % m) R).testBit _ = true
      rw [Nat.testBit_or]
      by_cases hj : j ∈ V
      · have hV' : V.erase j ⊆ S := by
          intro x hx
          rw [Finset.mem_erase] at hx
          rcases Finset.mem_insert.mp (hV hx.2) with h | h
          · exact absurd h hx.1
          · exact h
        have hb := hbits _ hV'
        have hrot := ar_rot (Nat.mod_lt (w j) hm) (Nat.mod_lt _ hm) hb
        rw [← Finset.sum_erase_add V w hj, Nat.add_mod]
        rw [hrot, Bool.or_true]
      · have hV' : V ⊆ S := by
          intro x hx
          rcases Finset.mem_insert.mp (hV hx) with h | h
          · exact absurd (h ▸ hx) hj
          · exact h
        rw [hbits V hV', Bool.true_or]
    · intro x hx
      have := hU hx
      simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto

theorem ar_ssMod (w : ℕ → ℕ) {m : ℕ} (hm : 0 < m) (idx : List ℕ) :
    ∀ U ⊆ idx.toFinset, (ssMod w idx m).testBit ((∑ j ∈ U, w j) % m) = true := by
  intro U hU
  have h := ar_loop_inv w hm idx ∅ 1 (Nat.one_lt_two_pow (by omega)) (fun V hV => by
    rw [Finset.subset_empty.mp hV, Finset.sum_empty, Nat.zero_mod]
    rfl) U (by simpa using hU)
  exact h

noncomputable def arDiv (T m k R : ℕ) : List ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun d _ ih A' => List.rec (motive := fun _ => Bool) false
      (fun a A'' _ => andB
        (orB (notB (Nat.beq a k)) (orB (Nat.ble d (nat_lit 1)) (orB (Nat.ble T d)
          (Nat.beq (Nat.land (Nat.shiftRight R (Nat.mod (Nat.sub d (nat_lit 1)) m)) (nat_lit 1))
            (nat_lit 0)))))
        (ih A'')) A')

theorem ar_div (T m k R : ℕ) : ∀ (L A : List ℕ), arDiv T m k R L A = true →
    ∀ i < L.length, A.getD i 0 = k → L.getD i 0 ≤ 1 ∨ T ≤ L.getD i 0 ∨
      (R >>> ((L.getD i 0 - 1) % m)) &&& 1 = 0 := by
  intro L
  induction L with
  | nil => intro A _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons d L ih =>
    intro A h i hi ha
    cases A with
    | nil => exact absurd h Bool.false_ne_true
    | cons a A =>
      change andB (orB (notB (Nat.beq a k)) (orB (Nat.ble d 1) (orB (Nat.ble T d)
          (Nat.beq (Nat.land (Nat.shiftRight R (Nat.mod (Nat.sub d 1) m)) 1) 0))))
        (arDiv T m k R L A) = true at h
      rw [ar_andB, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp only [List.getD_cons_zero] at ha ⊢
        have h1 := h.1
        simp only [ar_orB, ar_notB, Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq,
          Nat.beq_eq, ha] at h1
        rcases h1 with h1 | h1 | h1 | h1
        · exact absurd (Nat.beq_refl k) (by rw [h1]; exact Bool.false_ne_true)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
      | succ i =>
        simp only [List.getD_cons_succ] at ha ⊢
        exact ih A h.2 i (by simpa using hi) ha

theorem arith_sound (w : ℕ → ℕ) (idx : List ℕ) (F : List (ℕ × ℕ)) (A Ms : List ℕ) (T : ℕ)
    (hF : ∀ pe ∈ F, Nat.Prime pe.1) (hT : (F.map fun pe => pe.1 ^ pe.2).prod = T)
    (hsum : 1 + ∑ j ∈ idx.toFinset, w j = T) (hpos : ∀ j ∈ idx, 0 < w j)
    (hm : ∀ m ∈ Ms, 0 < m) (hA : A.length = (divsOf F).length) (hAk : ∀ a ∈ A, a < Ms.length)
    (hchk : ∀ k < Ms.length, ssChk w idx F A T (Ms.getD k 0) k = true) :
    ∀ U ⊆ idx.toFinset, (1 + ∑ j ∈ U, w j) ∣ T → U = ∅ ∨ U = idx.toFinset := by
  intro U hU hdvd
  have hdm : 1 + ∑ j ∈ U, w j ∈ divsOf F := ar_mem_divsOf F hF _ (hT ▸ hdvd)
  obtain ⟨i, hi, hdi⟩ := List.getElem_of_mem hdm
  have hiA : i < A.length := hA ▸ hi
  have haM : A.getD i 0 < Ms.length := hAk _ (by
    rw [List.getD_eq_getElem _ _ hiA]
    exact List.getElem_mem hiA)
  have hm0 : 0 < Ms.getD (A.getD i 0) 0 := hm _ (by
    rw [List.getD_eq_getElem _ _ haM]
    exact List.getElem_mem haM)
  have H := hchk _ haM
  have e : ssChk w idx F A T (Ms.getD (A.getD i 0) 0) (A.getD i 0) =
      sB (ssMod w idx (Ms.getD (A.getD i 0) 0)) (fun R =>
        arDiv T (Ms.getD (A.getD i 0) 0) (A.getD i 0) R (divsOf F) A) := rfl
  rw [e, ar_sB] at H
  have hd := ar_div _ _ _ _ _ _ H i hi rfl
  rw [List.getD_eq_getElem _ _ hi, hdi] at hd
  have hbit := ar_ssMod w hm0 idx U hU
  have hsub : 1 + ∑ j ∈ U, w j - 1 = ∑ j ∈ U, w j := by omega
  rw [hsub] at hd
  have hTpos : 0 < T := by omega
  rcases hd with hd | hd | hd
  · left
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have := Finset.single_le_sum (fun x _ => Nat.zero_le (w x)) hj
    have := hpos j (List.mem_toFinset.mp (hU hj))
    omega
  · right
    have hle := Nat.le_of_dvd hTpos hdvd
    by_contra hne
    obtain ⟨j, hjI, hjU⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hU, hne⟩)
    have := Finset.sum_lt_sum_of_subset hU hjI hjU (hpos j (List.mem_toFinset.mp hjI))
      (fun _ _ _ => Nat.zero_le _)
    omega
  · exfalso
    rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hd
    simp only [decide_eq_true_eq] at hbit
    omega

end CFSG.KC.B4A

end
