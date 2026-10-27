module

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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LieType.Sp6Spin

variable {N : ℕ} [NeZero N]

private def weightSupp (a : Fin 3 → ZMod N) : Finset (Fin 3) :=
  Finset.univ.filter fun i => a i ≠ 0

@[simp]
private lemma mem_weightSupp {a : Fin 3 → ZMod N} {i : Fin 3} :
    i ∈ weightSupp a ↔ a i ≠ 0 := by
  simp [weightSupp]

private lemma weightSupp_comp_perm (a : Fin 3 → ZMod N) (e : Equiv.Perm (Fin 3)) :
    weightSupp (a ∘ e) = (weightSupp a).image e.symm := by
  ext i
  simp only [mem_weightSupp, Function.comp_apply, Finset.mem_image]
  constructor
  · intro h
    exact ⟨e i, h, e.symm_apply_apply i⟩
  · rintro ⟨j, hj, hji⟩
    rwa [← hji, e.apply_symm_apply]

private lemma m_update_eq {m : (Fin 3 → ZMod N) → ℕ}
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (a : Fin 3 → ZMod N) (i : Fin 3) {c : ZMod N} (hc : c = a i ∨ c = -a i) :
    m (Function.update a i c) = m a := by
  rcases hc with rfl | rfl
  · simp
  · exact hneg i a

private lemma m_eq_of_signs {m : (Fin 3 → ZMod N) → ℕ}
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    {a b : Fin 3 → ZMod N} (h : ∀ i, b i = a i ∨ b i = -a i) : m b = m a := by
  let a1 : Fin 3 → ZMod N := Function.update a 0 (b 0)
  let a2 : Fin 3 → ZMod N := Function.update a1 1 (b 1)
  let a3 : Fin 3 → ZMod N := Function.update a2 2 (b 2)
  have e1 : m a1 = m a := m_update_eq hneg a 0 (h 0)
  have e2 : m a2 = m a1 := m_update_eq hneg a1 1 (by simpa [a1] using h 1)
  have e3 : m a3 = m a2 := m_update_eq hneg a2 2 (by simpa [a1, a2] using h 2)
  have hb : a3 = b := by
    funext i
    fin_cases i <;> simp [a1, a2, a3]
  rw [← hb, e3, e2, e1]

private lemma m_eq_comp_perm {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (e : Equiv.Perm (Fin 3)) (a : Fin 3 → ZMod N) : m (a ∘ e) = m a := by
  induction e using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap f x y _ ih =>
      have h1 : a ∘ ⇑(f * Equiv.swap x y) = (a ∘ ⇑f) ∘ ⇑(Equiv.swap x y) := by
        funext i
        simp [Equiv.Perm.mul_def]
      rw [h1, hswap x y (a ∘ f), ih]

private def sgnVec (a : Fin 3 → ZMod N) (p : Fin 3 → Bool) : Fin 3 → ZMod N :=
  fun i => if p i then a i else -a i

private def sgnOn (a : Fin 3 → ZMod N) (s : Finset (Fin 3)) (p : s → Bool) :
    Fin 3 → ZMod N :=
  fun i => if h : i ∈ s then (if p ⟨i, h⟩ then a i else -a i) else a i

private def signBox (a : Fin 3 → ZMod N) : Finset (Fin 3 → ZMod N) :=
  Finset.univ.image (sgnVec a)

private lemma mem_signBox_iff {a b : Fin 3 → ZMod N} :
    b ∈ signBox a ↔ ∀ i, b i = a i ∨ b i = -a i := by
  constructor
  · intro hb
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hb
    intro i
    by_cases hp : p i
    · exact Or.inl (by simp [sgnVec, hp])
    · exact Or.inr (by simp [sgnVec, hp])
  · intro hb
    let p : Fin 3 → Bool := fun i => decide (b i = a i)
    have hp : sgnVec a p = b := by
      funext i
      have hi := hb i
      by_cases h : b i = a i
      · simp [sgnVec, p, h]
      · have hneg : b i = -a i := hi.resolve_left h
        have hp' : p i = false := by simp [p, h]
        simp only [sgnVec, hp', if_false]
        exact hneg.symm
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩

private lemma m_eq_of_mem_signBox {m : (Fin 3 → ZMod N) → ℕ}
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    {a b : Fin 3 → ZMod N} (hb : b ∈ signBox a) : m b = m a := by
  rw [mem_signBox_iff] at hb
  exact m_eq_of_signs hneg hb

private lemma sgnOn_mem_signBox {a : Fin 3 → ZMod N} (s : Finset (Fin 3)) (p : s → Bool) :
    sgnOn a s p ∈ signBox a := by
  rw [mem_signBox_iff]
  intro i
  by_cases hi : i ∈ s
  · rw [sgnOn, dif_pos hi]
    by_cases hp : p ⟨i, hi⟩
    · exact Or.inl (by simp [hp])
    · exact Or.inr (by simp [hp])
  · rw [sgnOn, dif_neg hi]
    exact Or.inl rfl

private lemma sgnOn_injective (hN : Odd N) {a : Fin 3 → ZMod N} {s : Finset (Fin 3)}
    (hs : ∀ i ∈ s, a i ≠ 0) : Function.Injective (sgnOn a s) := by
  intro p q hpq
  funext i
  have hi : i.1 ∈ s := i.2
  have hv := congrFun hpq i.1
  rw [sgnOn, sgnOn, dif_pos hi, dif_pos hi] at hv
  by_cases hp : p i = true <;> by_cases hq : q i = true
  · simp [hp, hq]
  · exfalso
    have hv' : a i.1 = -a i.1 := by simpa [hp, hq] using hv
    exact ZMod.ne_neg_self hN (hs i.1 hi) hv'
  · exfalso
    have hv' : -a i.1 = a i.1 := by simpa [hp, hq] using hv
    exact ZMod.ne_neg_self hN (hs i.1 hi) hv'.symm
  · simp [hp, hq]

private lemma signBox_eq_image_sgnOn {a : Fin 3 → ZMod N} (s : Finset (Fin 3))
    (hs : ∀ i, a i ≠ 0 ↔ i ∈ s) :
    signBox a = Finset.univ.image (sgnOn a s) := by
  apply Finset.Subset.antisymm
  · intro b hb
    rw [mem_signBox_iff] at hb
    let p : s → Bool := fun i => decide (b i.1 = a i.1)
    refine Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : i ∈ s
    · rw [sgnOn, dif_pos hi]
      have hbi := hb i
      by_cases h : b i = a i
      · simp [p, hi, h]
      · have hneg : b i = -a i := hbi.resolve_left h
        have hp' : p ⟨i, hi⟩ = false := by simp [p, h]
        simp only [hp', if_false]
        exact hneg.symm
    · have hai : a i = 0 := by
        by_contra h
        exact hi ((hs i).mp h)
      have hbi : b i = 0 := by
        rcases hb i with h' | h'
        · rw [h', hai]
        · rw [h', hai, neg_zero]
      simp [sgnOn, hi, hai, hbi]
  · intro b hb
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hb
    exact sgnOn_mem_signBox s p

private lemma card_signBox (hN : Odd N) {a : Fin 3 → ZMod N} (s : Finset (Fin 3))
    (hs : ∀ i, a i ≠ 0 ↔ i ∈ s) : (signBox a).card = 2 ^ s.card := by
  rw [signBox_eq_image_sgnOn s hs, Finset.card_image_of_injective]
  · simp
  · exact sgnOn_injective hN (fun i hi => (hs i).mpr hi)

private lemma card_signBox_supp (hN : Odd N) (a : Fin 3 → ZMod N) :
    (signBox a).card = 2 ^ (weightSupp a).card :=
  card_signBox hN (weightSupp a) (fun i => by simp)

private lemma card_mul_eq_sum {m : (Fin 3 → ZMod N) → ℕ} {S : Finset (Fin 3 → ZMod N)} {c : ℕ}
    (h : ∀ b ∈ S, m b = c) : ∑ b ∈ S, m b = S.card * c := by
  rw [Finset.sum_congr rfl h]
  simp [Finset.sum_const, nsmul_eq_mul]

private lemma card_mul_le_sum {m : (Fin 3 → ZMod N) → ℕ} {S : Finset (Fin 3 → ZMod N)} {c : ℕ}
    (h : ∀ b ∈ S, m b = c) : S.card * c ≤ ∑ a, m a := by
  rw [← card_mul_eq_sum h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun _ _ _ => Nat.zero_le _)

private lemma single_eq_single {i j : Fin 3} {x y : ZMod N} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (Pi.single i x : Fin 3 → ZMod N) = Pi.single j y) : i = j ∧ x = y := by
  have hij : i = j := by
    by_contra hne
    have h1 : (Pi.single i x : Fin 3 → ZMod N) i = x := by simp
    have h2 : (Pi.single j y : Fin 3 → ZMod N) i = 0 := by
      rw [Pi.single_eq_of_ne]
      exact hne
    rw [h, h2] at h1
    exact hx h1.symm
  subst hij
  exact ⟨rfl, by simpa using congrFun h i⟩

private def oneBox (x : ZMod N) : Finset (Fin 3 → ZMod N) :=
  Finset.univ.image fun p : Fin 3 × Bool =>
    if p.2 then (Pi.single p.1 x : Fin 3 → ZMod N)
    else (Pi.single p.1 (-x) : Fin 3 → ZMod N)

private lemma mem_oneBox {x : ZMod N} {a : Fin 3 → ZMod N} :
    a ∈ oneBox x ↔ ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) := by
  constructor
  · intro ha
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨p.1, ?_⟩
    by_cases hp : p.2
    · exact Or.inl (by simp [hp])
    · exact Or.inr (by simp [hp])
  · rintro ⟨i, rfl | rfl⟩
    · exact Finset.mem_image.mpr ⟨(i, true), Finset.mem_univ _, by simp⟩
    · exact Finset.mem_image.mpr ⟨(i, false), Finset.mem_univ _, by simp⟩

private lemma oneBox_injective {x : ZMod N} (hx : x ≠ 0) (hN : Odd N) :
    Function.Injective (fun p : Fin 3 × Bool =>
      if p.2 then (Pi.single p.1 x : Fin 3 → ZMod N)
      else (Pi.single p.1 (-x) : Fin 3 → ZMod N)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  change (if b then (Pi.single i x : Fin 3 → ZMod N)
      else (Pi.single i (-x) : Fin 3 → ZMod N))
    = (if c then (Pi.single j x : Fin 3 → ZMod N)
      else (Pi.single j (-x) : Fin 3 → ZMod N)) at h
  have hi : i = j := by
    by_contra hij
    have h1 : (if b then (Pi.single i x : Fin 3 → ZMod N)
        else (Pi.single i (-x) : Fin 3 → ZMod N)) i ≠ 0 := by
      by_cases hb : b <;> simp [hb, hx]
    have h2 : (if c then (Pi.single j x : Fin 3 → ZMod N)
        else (Pi.single j (-x) : Fin 3 → ZMod N)) i = 0 := by
      by_cases hc : c <;> simp [hc, Pi.single_eq_of_ne, hij]
    rw [h] at h1
    exact h1 h2
  subst hi
  have hbc : b = c := by
    by_cases hb : b <;> by_cases hc : c <;> simp [hb, hc] at h ⊢
    · exact absurd h (ZMod.ne_neg_self hN hx)
    · exact absurd h.symm (ZMod.ne_neg_self hN hx)
  subst hbc
  rfl

private lemma card_oneBox {x : ZMod N} (hx : x ≠ 0) (hN : Odd N) : (oneBox x).card = 6 := by
  rw [oneBox, Finset.card_image_of_injective]
  · simp
  · exact oneBox_injective hx hN

private lemma m_single_eq {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (i : Fin 3) (x : ZMod N) : m (Pi.single i x) = m (Pi.single 0 x) := by
  have h : (Pi.single 0 x : Fin 3 → ZMod N) ∘ Equiv.swap 0 i = Pi.single i x := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · by_cases hj0 : j = 0
      · subst hj0
        simp [Function.comp, Equiv.swap_apply_left, Pi.single_eq_of_ne (Ne.symm hji),
          Pi.single_eq_of_ne hji]
      · have hswapj : Equiv.swap 0 i j = j :=
          Equiv.swap_apply_of_ne_of_ne hj0 hji
        simp [Function.comp, hswapj, Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hj0]
  rw [← h]
  exact m_eq_comp_perm hswap (Equiv.swap 0 i) (Pi.single 0 x)

private lemma m_single_neg {m : (Fin 3 → ZMod N) → ℕ}
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (i : Fin 3) (x : ZMod N) : m (Pi.single i (-x)) = m (Pi.single i x) := by
  have h : (Pi.single i (-x) : Fin 3 → ZMod N) =
      Function.update (Pi.single i x) i (-(Pi.single i x i)) := by
    funext j
    by_cases hji : j = i <;> simp [Function.update, hji]
  rw [h, hneg]

private lemma m_eq_of_mem_oneBox {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    {x : ZMod N} {b : Fin 3 → ZMod N} (hb : b ∈ oneBox x) :
    m b = m (Pi.single 0 x) := by
  rw [mem_oneBox] at hb
  obtain ⟨i, rfl | rfl⟩ := hb
  · exact m_single_eq hswap i x
  · rw [m_single_neg hneg i x, m_single_eq hswap i x]

private lemma disjoint_oneBox {x y : ZMod N} (hx : x ≠ 0) (hy : y ≠ 0)
    (hyx : y ≠ x) (hyx' : y ≠ -x) : Disjoint (oneBox x) (oneBox y) := by
  rw [Finset.disjoint_left]
  intro b hbx hby
  rw [mem_oneBox] at hbx hby
  obtain ⟨i, rfl | rfl⟩ := hbx <;> obtain ⟨j, hj | hj⟩ := hby
  · have h := single_eq_single hx hy hj
    exact hyx h.2.symm
  · have h := single_eq_single hx (neg_ne_zero.mpr hy) hj
    exact hyx' (by rw [h.2]; simp)
  · have h := single_eq_single (neg_ne_zero.mpr hx) hy hj
    exact hyx' h.2.symm
  · have h := single_eq_single (neg_ne_zero.mpr hx) (neg_ne_zero.mpr hy) hj
    exact hyx (neg_inj.mp h.2).symm

private lemma eq_single_of_weightSupp_eq_singleton {a : Fin 3 → ZMod N} {i : Fin 3}
    (h : weightSupp a = {i}) : a = Pi.single i (a i) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp
  · have haj : a j = 0 := by
      by_contra hne
      have hj : j ∈ weightSupp a := by simpa [mem_weightSupp] using hne
      rw [h] at hj
      exact hji (by simpa using hj)
    simp [hji, haj]

private lemma weightSupp_swap {a : Fin 3 → ZMod N} {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hs : weightSupp a = {i, j}) :
    weightSupp (a ∘ Equiv.swap i k) = {j, k} := by
  rw [weightSupp_comp_perm, hs, Equiv.symm_swap, Finset.image_insert, Finset.image_singleton]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk, Finset.pair_comm]

private def twoBox (a : Fin 3 → ZMod N) (i j k : Fin 3) : Finset (Fin 3 → ZMod N) :=
  (signBox a ∪ signBox (a ∘ Equiv.swap i k)) ∪
    signBox (a ∘ Equiv.swap j k)

private lemma disjoint_twoBox {a : Fin 3 → ZMod N} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i ≠ 0) (hj : a j ≠ 0)
    (hak : a k = 0) :
    Disjoint (signBox a) (signBox (a ∘ Equiv.swap i k)) ∧
      Disjoint (signBox a ∪ signBox (a ∘ Equiv.swap i k))
        (signBox (a ∘ Equiv.swap j k)) := by
  have h12 : Disjoint (signBox a) (signBox (a ∘ Equiv.swap i k)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    have h1 : c k = 0 := by
      rw [mem_signBox_iff] at hc1
      rcases hc1 k with h | h <;> simp [hak, h]
    have h2 : c k ≠ 0 := by
      rw [mem_signBox_iff] at hc2
      rcases hc2 k with h | h
      · rw [h]
        simpa [Function.comp, Equiv.swap_apply_right] using hi
      · rw [h]
        simpa [Function.comp, Equiv.swap_apply_right] using neg_ne_zero.mpr hi
    exact h2 h1
  have h13 : Disjoint (signBox a) (signBox (a ∘ Equiv.swap j k)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc3
    have h1 : c k = 0 := by
      rw [mem_signBox_iff] at hc1
      rcases hc1 k with h | h <;> simp [hak, h]
    have h3 : c k ≠ 0 := by
      rw [mem_signBox_iff] at hc3
      rcases hc3 k with h | h
      · rw [h]
        simpa [Function.comp, Equiv.swap_apply_right] using hj
      · rw [h]
        simpa [Function.comp, Equiv.swap_apply_right] using neg_ne_zero.mpr hj
    exact h3 h1
  have h23 : Disjoint (signBox (a ∘ Equiv.swap i k))
      (signBox (a ∘ Equiv.swap j k)) := by
    rw [Finset.disjoint_left]
    intro c hc2 hc3
    have h2 : c i = 0 := by
      rw [mem_signBox_iff] at hc2
      rcases hc2 i with h | h <;> simp [hak, h]
    have h3 : c i ≠ 0 := by
      rw [mem_signBox_iff] at hc3
      rcases hc3 i with h | h
      · rw [h]
        simpa [Function.comp, Equiv.swap_apply_of_ne_of_ne hij hik] using hi
      · rw [h]
        simpa [Function.comp, Equiv.swap_apply_of_ne_of_ne hij hik]
          using neg_ne_zero.mpr hi
    exact h3 h2
  exact ⟨h12, Finset.disjoint_union_left.mpr ⟨h13, h23⟩⟩

private lemma card_twoBox (hN : Odd N) {a : Fin 3 → ZMod N} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hs : weightSupp a = {i, j}) (hi : a i ≠ 0) (hj : a j ≠ 0) (hak : a k = 0) :
    (twoBox a i j k).card = 12 := by
  have hcard1 : (signBox a).card = 4 := by
    rw [card_signBox_supp hN, hs, Finset.card_pair hij]
    norm_num
  have hsupp2 : weightSupp (a ∘ Equiv.swap i k) = {j, k} :=
    weightSupp_swap hij hik hjk hs
  have hcard2 : (signBox (a ∘ Equiv.swap i k)).card = 4 := by
    rw [card_signBox_supp hN, hsupp2, Finset.card_pair hjk]
    norm_num
  have hsupp3 : weightSupp (a ∘ Equiv.swap j k) = {i, k} := by
    rw [weightSupp_swap (Ne.symm hij) hjk hik (by rw [hs, Finset.pair_comm])]
  have hcard3 : (signBox (a ∘ Equiv.swap j k)).card = 4 := by
    rw [card_signBox_supp hN, hsupp3, Finset.card_pair hik]
    norm_num
  obtain ⟨h12, hdisj⟩ := disjoint_twoBox hij hik hjk hi hj hak
  rw [twoBox, Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint h12,
    hcard1, hcard2, hcard3]

private lemma m_eq_of_mem_twoBox {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    {a : Fin 3 → ZMod N} {i j k : Fin 3} {c : Fin 3 → ZMod N}
    (hc : c ∈ twoBox a i j k) : m c = m a := by
  rw [twoBox, Finset.mem_union, Finset.mem_union] at hc
  rcases hc with (hc | hc) | hc
  · exact m_eq_of_mem_signBox hneg hc
  · rw [m_eq_of_mem_signBox hneg hc, m_eq_comp_perm hswap (Equiv.swap i k) a]
  · rw [m_eq_of_mem_signBox hneg hc, m_eq_comp_perm hswap (Equiv.swap j k) a]

private lemma m_eq_zero_of_support_card_two {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hN : Odd N) (hsum : ∑ a, m a = 8) {a : Fin 3 → ZMod N}
    (hcard : (weightSupp a).card = 2) : m a = 0 := by
  obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hcard
  have hi : a i ≠ 0 := mem_weightSupp.mp (by rw [hs]; simp)
  have hj : a j ≠ 0 := mem_weightSupp.mp (by rw [hs]; simp)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin 3))) (t := Finset.univ) (by simp [hij])
  have hik : i ≠ k := fun h => hk (by simp [h])
  have hjk : j ≠ k := fun h => hk (by simp [h])
  have hak : a k = 0 := by
    by_contra hne
    exact hk (by rw [← hs]; simpa [mem_weightSupp] using hne)
  have hcardS : (twoBox a i j k).card = 12 :=
    card_twoBox hN hij hik hjk hs hi hj hak
  have hconst : ∀ c ∈ twoBox a i j k, m c = m a := fun _ hc => m_eq_of_mem_twoBox hswap hneg hc
  have hle := card_mul_le_sum (m := m) hconst
  rw [hcardS, hsum] at hle
  by_contra hma
  have hma1 : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr hma
  omega

private lemma m_eq_zero_of_three_split {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hN : Odd N) (hsum : ∑ a, m a = 8) {a : Fin 3 → ZMod N}
    (ha : ∀ i, a i ≠ 0) (hnot : ¬ ∃ x, ∀ i, a i = x ∨ a i = -x) : m a = 0 := by
  have hx0 : a 0 ≠ 0 := ha 0
  have hn : ¬ ∀ i, a i = a 0 ∨ a i = -a 0 := fun h => hnot ⟨a 0, h⟩
  push Not at hn
  obtain ⟨i, hi1, hi2⟩ := hn
  have hsupp : weightSupp a = Finset.univ := by
    ext x
    simp [mem_weightSupp, ha x]
  have hcard : (signBox a).card = 8 := by
    rw [card_signBox_supp hN, hsupp]
    norm_num
  have hnotmem : a ∘ Equiv.swap 0 i ∉ signBox a := by
    rw [mem_signBox_iff]
    intro h
    have h0 := h 0
    simp only [Function.comp_apply, Equiv.swap_apply_left] at h0
    exact h0.elim hi1 hi2
  have hcardS : (insert (a ∘ Equiv.swap 0 i) (signBox a)).card = 9 := by
    rw [Finset.card_insert_of_notMem hnotmem, hcard]
  have hconst : ∀ c ∈ insert (a ∘ Equiv.swap 0 i) (signBox a), m c = m a := by
    intro c hc
    rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · exact m_eq_comp_perm hswap (Equiv.swap 0 i) a
    · exact m_eq_of_mem_signBox hneg hc
  have hle := card_mul_le_sum (m := m) hconst
  rw [hcardS, hsum] at hle
  by_contra hma
  have hma1 : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr hma
  omega

private lemma add_le_sum_of_disjoint {m : (Fin 3 → ZMod N) → ℕ} {S T : Finset (Fin 3 → ZMod N)}
    (h : Disjoint S T) {p q : ℕ} (hp : p ≤ ∑ c ∈ S, m c) (hq : q ≤ ∑ c ∈ T, m c) :
    p + q ≤ ∑ c, m c := by
  have hunion : ∑ c ∈ S ∪ T, m c = ∑ c ∈ S, m c + ∑ c ∈ T, m c := Finset.sum_union h
  calc p + q ≤ ∑ c ∈ S, m c + ∑ c ∈ T, m c := Nat.add_le_add hp hq
    _ = ∑ c ∈ S ∪ T, m c := hunion.symm
    _ ≤ ∑ c, m c := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)

private lemma card_threeBox (hN : Odd N) {x : ZMod N} (hx : x ≠ 0) :
    (signBox (fun _ : Fin 3 => x)).card = 8 := by
  rw [card_signBox_supp hN]
  have hsupp : weightSupp (fun _ : Fin 3 => x) = Finset.univ := by
    ext i
    simp [mem_weightSupp, hx]
  rw [hsupp]
  norm_num

private lemma m_eq_zero_of_support_one_notMem_oneBox {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hN : Odd N) (hsum : ∑ a, m a = 8) {x : ZMod N} (hx : x ≠ 0)
    (hSsum : ∑ c ∈ oneBox x, m c = 6) {b : Fin 3 → ZMod N}
    (hcard : (weightSupp b).card = 1) (hbx : b ∉ oneBox x) : m b = 0 := by
  obtain ⟨j, hjsupp⟩ := Finset.card_eq_one.mp hcard
  have hb_single : b = Pi.single j (b j) := eq_single_of_weightSupp_eq_singleton hjsupp
  have hy : b j ≠ 0 := mem_weightSupp.mp (by rw [hjsupp]; simp)
  have hyx : b j ≠ x := by
    intro h
    exact hbx (by rw [mem_oneBox]; exact ⟨j, Or.inl (by rw [hb_single, h])⟩)
  have hyx' : b j ≠ -x := by
    intro h
    exact hbx (by rw [mem_oneBox]; exact ⟨j, Or.inr (by rw [hb_single, h])⟩)
  by_contra hmb
  have hmb1 : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr hmb
  let B := oneBox (b j)
  have hBcard : B.card = 6 := card_oneBox hy hN
  have hBdisj : Disjoint B (oneBox x) := (disjoint_oneBox hx hy hyx hyx').symm
  have hbase : m b = m (Pi.single 0 (b j)) := by
    conv_lhs => rw [hb_single]
    exact m_single_eq hswap j (b j)
  have hBconst : ∀ c ∈ B, m c = m b := by
    intro c hc
    rw [m_eq_of_mem_oneBox hswap hneg hc]
    exact hbase.symm
  have hBsum : 6 ≤ ∑ c ∈ B, m c := by
    calc 6 = B.card * 1 := by simp [hBcard]
      _ ≤ B.card * m b := Nat.mul_le_mul_left _ hmb1
      _ ≤ ∑ c ∈ B, m c := by rw [card_mul_eq_sum hBconst]
  have htotal := add_le_sum_of_disjoint (S := oneBox x) (T := B) hBdisj.symm
    (p := 6) (q := 6) (by rw [hSsum]) hBsum
  rw [hsum] at htotal
  omega

private lemma m_eq_zero_of_three_all_notMem_oneBox {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hN : Odd N) (hsum : ∑ a, m a = 8) {x : ZMod N} (hx : x ≠ 0)
    (hSsum : ∑ c ∈ oneBox x, m c = 6) {b : Fin 3 → ZMod N}
    (hcard : (weightSupp b).card = 3)
    (hall : ∃ y, ∀ i, b i = y ∨ b i = -y) (hbx : b ∉ oneBox x) : m b = 0 := by
  obtain ⟨y, hyall⟩ := hall
  have hsupp : weightSupp b = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hb0 : b 0 ≠ 0 := by
    have : (0 : Fin 3) ∈ weightSupp b := by rw [hsupp]; simp
    simpa using this
  have hy : y ≠ 0 := by
    intro hy0
    exact hb0 (by rcases hyall 0 with h | h <;> simp [hy0, h])
  let B := signBox (fun _ : Fin 3 => y)
  have hbB : b ∈ B := by
    rw [mem_signBox_iff]
    exact hyall
  have hBcard : B.card = 8 := card_threeBox hN hy
  have hBdisj : Disjoint B (oneBox x) := by
    rw [Finset.disjoint_left]
    intro c hcB hcS
    rw [mem_oneBox] at hcS
    obtain ⟨i, rfl | rfl⟩ := hcS
    · obtain ⟨j, hji⟩ := exists_ne i
      have hval := (mem_signBox_iff.mp hcB) j
      have hzero : (Pi.single i x : Fin 3 → ZMod N) j = 0 := by
        rw [Pi.single_eq_of_ne]
        exact hji
      rcases hval with h | h
      · exact hy (by rw [hzero] at h; exact h.symm)
      · exact hy (by rw [hzero] at h; exact neg_eq_zero.mp h.symm)
    · obtain ⟨j, hji⟩ := exists_ne i
      have hval := (mem_signBox_iff.mp hcB) j
      have hzero : (Pi.single i (-x) : Fin 3 → ZMod N) j = 0 := by
        rw [Pi.single_eq_of_ne]
        exact hji
      rcases hval with h | h
      · exact hy (by rw [hzero] at h; exact h.symm)
      · exact hy (by rw [hzero] at h; exact neg_eq_zero.mp h.symm)
  have hBconst : ∀ c ∈ B, m c = m b := by
    intro c hc
    exact (m_eq_of_mem_signBox hneg hc).trans (m_eq_of_mem_signBox hneg hbB).symm
  by_contra hmb
  have hmb1 : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr hmb
  have hBsum : 8 ≤ ∑ c ∈ B, m c := by
    calc 8 = B.card * 1 := by simp [hBcard]
      _ ≤ B.card * m b := Nat.mul_le_mul_left _ hmb1
      _ ≤ ∑ c ∈ B, m c := by rw [card_mul_eq_sum hBconst]
  have htotal := add_le_sum_of_disjoint (S := oneBox x) (T := B) hBdisj.symm
    (p := 6) (q := 8) (by rw [hSsum]) hBsum
  rw [hsum] at htotal
  omega

private lemma m_eq_zero_of_notMem_oneBox {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hN : Odd N) (hsum : ∑ a, m a = 8) {x : ZMod N} (hx : x ≠ 0)
    (hSsum : ∑ c ∈ oneBox x, m c = 6) {b : Fin 3 → ZMod N}
    (hb0 : b ≠ 0) (hbx : b ∉ oneBox x) : m b = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    exact hb0 (funext fun i => by simpa using h i)
  have hbpos : 0 < (weightSupp b).card :=
    Finset.card_pos.mpr ⟨i, by simpa [mem_weightSupp] using hi⟩
  have hble : (weightSupp b).card ≤ 3 := by
    simpa using Finset.card_le_univ (weightSupp b)
  have hcases : (weightSupp b).card = 1 ∨ (weightSupp b).card = 2 ∨
      (weightSupp b).card = 3 := by omega
  rcases hcases with hcard | hcard | hcard
  · exact m_eq_zero_of_support_one_notMem_oneBox hswap hneg hN hsum hx hSsum hcard hbx
  · exact m_eq_zero_of_support_card_two hswap hneg hN hsum hcard
  · by_cases hall : ∃ y, ∀ i, b i = y ∨ b i = -y
    · exact m_eq_zero_of_three_all_notMem_oneBox hswap hneg hN hsum hx hSsum hcard hall hbx
    · have hsupp : weightSupp b = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      have hbha : ∀ i, b i ≠ 0 := by
        intro i
        have : i ∈ weightSupp b := by rw [hsupp]; simp
        simpa using this
      exact m_eq_zero_of_three_split hswap hneg hN hsum hbha hall

private lemma oneBox_case {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hN : Odd N) (hsum : ∑ a, m a = 8) {a : Fin 3 → ZMod N}
    (hcard : (weightSupp a).card = 1) (hma : m a ≠ 0) :
    ∃ x : ZMod N, x ≠ 0 ∧ m 0 = 2 ∧ ∀ b, b ≠ 0 →
      m b = if ∃ i, b = Pi.single i x ∨ b = Pi.single i (-x) then 1 else 0 := by
  obtain ⟨i, hisupp⟩ := Finset.card_eq_one.mp hcard
  let x := a i
  have hx : x ≠ 0 := mem_weightSupp.mp (by rw [hisupp]; simp)
  have ha_single : a = Pi.single i x := eq_single_of_weightSupp_eq_singleton hisupp
  have hconst : ∀ c ∈ oneBox x, m c = m a := by
    intro c hc
    have hcbase := m_eq_of_mem_oneBox hswap hneg hc
    have habase : m a = m (Pi.single 0 x) := by
      conv_lhs => rw [ha_single]
      exact m_single_eq hswap i x
    rw [hcbase, ← habase]
  have hcardS : (oneBox x).card = 6 := card_oneBox hx hN
  have hle := card_mul_le_sum (m := m) hconst
  rw [hcardS, hsum] at hle
  have hma1 : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr hma
  have hma_eq : m a = 1 := by omega
  have hSsum : ∑ c ∈ oneBox x, m c = 6 := by
    rw [card_mul_eq_sum hconst, hcardS, hma_eq]
  have h0not : (0 : Fin 3 → ZMod N) ∉ oneBox x := by
    rw [mem_oneBox]
    rintro ⟨j, h | h⟩
    · have hval : x = 0 := by
        have := congrFun h j
        simpa using this.symm
      exact hx hval
    · have hval : -x = 0 := by
        have := congrFun h j
        simpa using this.symm
      exact hx (neg_eq_zero.mp hval)
  have hcomp : ∑ c ∈ (oneBox x)ᶜ, m c = 2 := by
    have h := Finset.sum_add_sum_compl (oneBox x) m
    rw [hSsum, hsum] at h
    omega
  have hm0' : ∑ c ∈ (oneBox x)ᶜ, m c = m 0 := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro b hbcomp hb0
      exact m_eq_zero_of_notMem_oneBox hswap hneg hN hsum hx hSsum hb0 (by simpa using hbcomp)
    · intro h
      exact absurd (by simpa using h) h0not
  rw [hcomp] at hm0'
  have hm0 : m 0 = 2 := hm0'.symm
  refine ⟨x, hx, hm0, ?_⟩
  intro b hb0
  by_cases hb : b ∈ oneBox x
  · have hb1 : m b = 1 := by rw [hconst b hb, hma_eq]
    have hP : ∃ i, b = Pi.single i x ∨ b = Pi.single i (-x) := mem_oneBox.mp hb
    rw [if_pos hP, hb1]
  · have hbzero : m b = 0 :=
      m_eq_zero_of_notMem_oneBox hswap hneg hN hsum hx hSsum hb0 hb
    have hP : ¬ ∃ i, b = Pi.single i x ∨ b = Pi.single i (-x) := fun h => hb (mem_oneBox.mpr h)
    rw [if_neg hP, hbzero]

private lemma threeBox_case {m : (Fin 3 → ZMod N) → ℕ}
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hN : Odd N) (hsum : ∑ a, m a = 8) {a : Fin 3 → ZMod N}
    (hcard : (weightSupp a).card = 3)
    (hall : ∃ x, ∀ i, a i = x ∨ a i = -x) (hma : m a ≠ 0) :
    ∃ x : ZMod N, x ≠ 0 ∧ ∀ b, m b = if ∀ i, b i = x ∨ b i = -x then 1 else 0 := by
  obtain ⟨x, hxall⟩ := hall
  have hsupp : weightSupp a = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have ha0 : a 0 ≠ 0 := by
    have : (0 : Fin 3) ∈ weightSupp a := by rw [hsupp]; simp
    simpa using this
  have hx : x ≠ 0 := by
    intro hx0
    exact ha0 (by rcases hxall 0 with h | h <;> simp [hx0, h])
  let S := signBox (fun _ : Fin 3 => x)
  have haS : a ∈ S := by
    change a ∈ signBox (fun _ : Fin 3 => x)
    rw [mem_signBox_iff]
    exact hxall
  have hcardS : S.card = 8 := card_threeBox hN hx
  have hconst : ∀ c ∈ S, m c = m a := by
    intro c hc
    exact (m_eq_of_mem_signBox hneg hc).trans (m_eq_of_mem_signBox hneg haS).symm
  have hle := card_mul_le_sum (m := m) hconst
  rw [hcardS, hsum] at hle
  have hma1 : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr hma
  have hma_eq : m a = 1 := by omega
  have hSsum : ∑ c ∈ S, m c = 8 := by
    rw [card_mul_eq_sum hconst, hcardS, hma_eq]
  have hcomp : ∑ c ∈ Sᶜ, m c = 0 := by
    have h := Finset.sum_add_sum_compl S m
    rw [hSsum, hsum] at h
    omega
  refine ⟨x, hx, ?_⟩
  intro b
  by_cases hb : b ∈ S
  · have hb1 : m b = 1 := by rw [hconst b hb, hma_eq]
    have hP : ∀ i, b i = x ∨ b i = -x := mem_signBox_iff.mp hb
    rw [if_pos hP, hb1]
  · have hbzero : m b = 0 := Finset.sum_eq_zero_iff.mp hcomp b (by simpa using hb)
    have hP : ¬ ∀ i, b i = x ∨ b i = -x := fun h => hb (mem_signBox_iff.mpr h)
    rw [if_neg hP, hbzero]

theorem weight_cases {N : ℕ} [NeZero N] (hN : Odd N)
    (m : (Fin 3 → ZMod N) → ℕ)
    (hswap : ∀ (i j : Fin 3) (a : Fin 3 → ZMod N), m (a ∘ Equiv.swap i j) = m a)
    (hneg : ∀ (i : Fin 3) (a : Fin 3 → ZMod N), m (Function.update a i (-a i)) = m a)
    (hsum : ∑ a, m a = 8) :
    m 0 = 8 ∨
    (∃ x : ZMod N, x ≠ 0 ∧ m 0 = 2 ∧ ∀ a, a ≠ 0 →
      m a = if ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) then 1 else 0) ∨
    (∃ x : ZMod N, x ≠ 0 ∧ ∀ a, m a = if ∀ i, a i = x ∨ a i = -x then 1 else 0) := by
  by_cases hzero : ∀ a, a ≠ 0 → m a = 0
  · left
    have hsum0 : ∑ a, m a = m 0 := by
      refine Finset.sum_eq_single 0 ?_ ?_
      · intro b _ hb
        exact hzero b hb
      · intro h
        exact absurd (Finset.mem_univ 0) h
    rw [hsum0] at hsum
    exact hsum
  · push Not at hzero
    obtain ⟨a, ha0, hma⟩ := hzero
    obtain ⟨i, hai⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (funext fun i => by simpa using h i)
    have hapos : 0 < (weightSupp a).card :=
      Finset.card_pos.mpr ⟨i, by simpa [mem_weightSupp] using hai⟩
    have halecard : (weightSupp a).card ≤ 3 := by
      simpa using Finset.card_le_univ (weightSupp a)
    have hcases : (weightSupp a).card = 1 ∨ (weightSupp a).card = 2 ∨
        (weightSupp a).card = 3 := by omega
    rcases hcases with hcard | hcard | hcard
    · exact Or.inr (Or.inl (oneBox_case hswap hneg hN hsum hcard hma))
    · exact absurd (m_eq_zero_of_support_card_two hswap hneg hN hsum hcard) hma
    · by_cases hall : ∃ x, ∀ i, a i = x ∨ a i = -x
      · exact Or.inr (Or.inr (threeBox_case hswap hneg hN hsum hcard hall hma))
      · have hsupp : weightSupp a = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          simp only [Finset.card_univ, Fintype.card_fin]
          omega
        have hbha : ∀ i, a i ≠ 0 := by
          intro i
          have : i ∈ weightSupp a := by rw [hsupp]; simp
          simpa using this
        exact absurd (m_eq_zero_of_three_split hswap hneg hN hsum hbha hall) hma

end CFSG.LieType.Sp6Spin
