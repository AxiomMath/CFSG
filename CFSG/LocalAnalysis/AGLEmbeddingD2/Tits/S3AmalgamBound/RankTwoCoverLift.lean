module

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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem exists_pElement_lift {G H : Type*} [Group G] [Group H] (f : G →* H) {p : ℕ}
    (hp : p.Prime) {x : G} {k : ℕ} (hord : orderOf (f x) = p ^ k) (hx : orderOf x ≠ 0) :
    ∃ l : G, l ∈ Subgroup.zpowers x ∧ f l = f x ∧ ∃ a : ℕ, orderOf l = p ^ a := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hx p hp.ne_one
  have hcop : Nat.Coprime (p ^ a) b :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hb)
  have hka : k ≤ a := by
    have h1 : p ^ k ∣ orderOf x := hord ▸ orderOf_map_dvd f x
    rw [hab] at h1
    have h2 : p ^ k ∣ p ^ a :=
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hb)).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
  obtain ⟨n, hn1, hn0⟩ : ∃ n : ℕ, n ≡ 1 [MOD p ^ a] ∧ n ≡ 0 [MOD b] :=
    ⟨_, (Nat.chineseRemainder hcop 1 0).2⟩
  refine ⟨x ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n, ?_, ?_⟩
  · have hfp : f x ^ (p ^ k) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    rw [map_pow, pow_eq_pow_mod n hfp]
    have h3 : n ≡ 1 [MOD p ^ k] := Nat.ModEq.of_dvd (pow_dvd_pow p hka) hn1
    have : n % p ^ k = 1 % p ^ k := h3
    rw [this, ← pow_eq_pow_mod 1 hfp, pow_one]
  · have hdvd : orderOf (x ^ n) ∣ p ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]
      have : orderOf x ∣ n * p ^ a := by
        rw [hab, mul_comm n]
        exact Nat.mul_dvd_mul_left _ (Nat.modEq_zero_iff_dvd.1 hn0)
      exact orderOf_dvd_iff_pow_eq_one.1 this
    exact ((Nat.dvd_prime_pow hp).1 hdvd).imp fun a' h => h.2

variable {G X : Type*} [Group G] [Group X]

theorem exists_threeLift [Finite G] (q : G →* X) (hq : q.ker ≤ Subgroup.center G) {a b : G}
    (ha : q a ^ 2 = 1) (hb : q b ^ 2 = 1) (hw : orderOf (q (a * b)) = 3) :
    ∃ v : G, v ∈ Subgroup.closure {a, b} ∧ q v = q (a * b) ∧ v ^ 3 = 1 ∧ b * v * b⁻¹ = v⁻¹ := by
  have hw0 : orderOf (a * b) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨v₀, hv₀mem, hv₀q, s, hs⟩ :=
    exists_pElement_lift q Nat.prime_three (x := a * b) (k := 1) (by simpa using hw) hw0
  have hwmem : a * b ∈ Subgroup.closure {a, b} :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hv₀cl : v₀ ∈ Subgroup.closure {a, b} := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv₀mem
    exact Subgroup.zpow_mem _ hwmem m
  have hbcl : b ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
  have hBB : q b * q b = 1 := by rw [← sq]; exact hb
  have hqa : (q a)⁻¹ = q a := by
    rw [inv_eq_iff_mul_eq_one, ← sq]; exact ha
  have hqb : (q b)⁻¹ = q b := by
    rw [inv_eq_iff_mul_eq_one]; exact hBB
  have e1 : q b * q (a * b) * (q b)⁻¹ = (q (a * b))⁻¹ := by
    rw [map_mul, mul_inv_rev, hqa, hqb]
    simp only [mul_assoc, hBB, mul_one]
  set z : G := v₀ * (b * v₀ * b⁻¹) with hz
  have hzq : q z = 1 := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, hv₀q, e1]
    simp
  have hzc : z ∈ Subgroup.center G := hq (MonoidHom.mem_ker.2 hzq)
  have hzcl : z ∈ Subgroup.closure {a, b} :=
    Subgroup.mul_mem _ hv₀cl (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbcl hv₀cl)
      (Subgroup.inv_mem _ hbcl))
  have hconj : b * v₀ * b⁻¹ = v₀⁻¹ * z := by rw [hz]; group
  have hv₀s : v₀ ^ (3 ^ s) = 1 := by rw [← hs]; exact pow_orderOf_eq_one _
  have hzs : z ^ (3 ^ s) = 1 := by
    have hcm : Commute v₀ (b * v₀ * b⁻¹) := by
      rw [hconj]
      exact (Commute.refl v₀).inv_right.mul_right (Subgroup.mem_center_iff.1 hzc v₀)
    rw [hz, hcm.mul_pow, hv₀s, one_mul]
    have : (b * v₀ * b⁻¹) ^ (3 ^ s) = b * v₀ ^ (3 ^ s) * b⁻¹ := by
      rw [conj_pow]
    rw [this, hv₀s]
    simp
  have hodd : Odd (3 ^ s) := Odd.pow (by decide)
  set t : ℕ := (3 ^ s - 1) / 2 with ht
  have h2t : 2 * t + 1 = 3 ^ s := by
    obtain ⟨c, hc⟩ := hodd
    rw [ht, hc]; omega
  set z₁ : G := z ^ t with hz₁
  have hz₁c : z₁ ∈ Subgroup.center G := Subgroup.pow_mem _ hzc t
  have hz₁q : q z₁ = 1 := by rw [hz₁, map_pow, hzq, one_pow]
  have hqv : q (v₀ * z₁) = q (a * b) := by rw [map_mul, hz₁q, mul_one, hv₀q]
  have hbz₁ : b * z₁ * b⁻¹ = z₁ := by
    rw [(Subgroup.mem_center_iff.1 hz₁c b), mul_assoc, mul_inv_cancel, mul_one]
  have hkey : z * z₁ * z₁ = 1 := by
    rw [hz₁, ← pow_succ', ← pow_add, show t + 1 + t = 3 ^ s by omega, hzs]
  have hzz : z * z₁ = z₁⁻¹ := eq_inv_of_mul_eq_one_left hkey
  have hc : z₁⁻¹ * v₀⁻¹ = v₀⁻¹ * z₁⁻¹ :=
    (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz₁c) v₀⁻¹).symm
  have hconjv : b * (v₀ * z₁) * b⁻¹ = (v₀ * z₁)⁻¹ := by
    have : b * (v₀ * z₁) * b⁻¹ = (b * v₀ * b⁻¹) * (b * z₁ * b⁻¹) := by group
    rw [this, hconj, hbz₁, mul_inv_rev, hc, mul_assoc, hzz]
  have hvs : (v₀ * z₁) ^ (3 ^ s) = 1 := by
    have hcm : Commute v₀ z₁ := Subgroup.mem_center_iff.1 hz₁c v₀
    rw [hcm.mul_pow, hv₀s, one_mul, hz₁, ← pow_mul, mul_comm, pow_mul, hzs, one_pow]
  have hv3 : (v₀ * z₁) ^ 3 = 1 := by
    set v := v₀ * z₁ with hv
    have hq3 : q (v ^ 3) = 1 := by
      rw [map_pow, hqv]
      exact hw ▸ pow_orderOf_eq_one _
    have hv3c : v ^ 3 ∈ Subgroup.center G := hq (MonoidHom.mem_ker.2 hq3)
    have h1 : b * v ^ 3 * b⁻¹ = (v ^ 3)⁻¹ := by
      have : b * v ^ 3 * b⁻¹ = (b * v * b⁻¹) ^ 3 := by rw [conj_pow]
      rw [this, hconjv, inv_pow]
    have h2 : b * v ^ 3 * b⁻¹ = v ^ 3 := by
      rw [(Subgroup.mem_center_iff.1 hv3c b), mul_assoc, mul_inv_cancel, mul_one]
    have h3 : v ^ 3 * v ^ 3 = 1 := by
      rw [h2] at h1
      exact mul_eq_one_iff_eq_inv.2 h1
    have h6 : orderOf v ∣ 6 := orderOf_dvd_of_pow_eq_one (by rw [show 6 = 3 + 3 by rfl, pow_add]; exact h3)
    have hs' : orderOf v ∣ 3 ^ s := orderOf_dvd_of_pow_eq_one hvs
    have hcop : Nat.Coprime (orderOf v) 2 :=
      Nat.Coprime.coprime_dvd_left hs' (Nat.Coprime.pow_left s (by norm_num))
    have h3' : orderOf v ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using h6)
    exact orderOf_dvd_iff_pow_eq_one.1 h3'
  exact ⟨v₀ * z₁, Subgroup.mul_mem _ hv₀cl (Subgroup.pow_mem _ hzcl t), hqv, hv3, hconjv⟩

theorem commute_of_inverted (q : G →* X) (hq : q.ker ≤ Subgroup.center G) {u v b : G}
    (hv : v ^ 3 = 1) (hbv : b * v * b⁻¹ = v⁻¹)
    (hcomm : q (u * v) = q (v * u)) (hb : q (b * u) = q (u * b)) : u * v = v * u := by
  set c : G := u * v * u⁻¹ * v⁻¹ with hc
  have hcq : q c = 1 := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [map_mul, map_mul] at hcomm
    rw [hcomm]; group
  have hcc : c ∈ Subgroup.center G := hq (MonoidHom.mem_ker.2 hcq)
  set z : G := u⁻¹ * (b * u * b⁻¹) with hz
  have hzq : q z = 1 := by
    have hb' : q b * q u = q u * q b := by simpa only [map_mul] using hb
    simp only [hz, map_mul, map_inv]
    rw [hb']; group
  have hzc : z ∈ Subgroup.center G := hq (MonoidHom.mem_ker.2 hzq)
  have hbu : b * u * b⁻¹ = u * z := by rw [hz]; group
  have hz1 : b * c * b⁻¹ = c := by
    rw [(Subgroup.mem_center_iff.1 hcc b), mul_assoc, mul_inv_cancel, mul_one]
  have hz2 : b * c * b⁻¹ = u * v⁻¹ * u⁻¹ * v := by
    have e : b * c * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹) * (b * u * b⁻¹)⁻¹ * (b * v * b⁻¹)⁻¹ := by
      rw [hc]; group
    rw [e, hbu, hbv]
    have hzz : u * z * v⁻¹ * (u * z)⁻¹ = u * v⁻¹ * u⁻¹ := by
      have : z * v⁻¹ = v⁻¹ * z := (Subgroup.mem_center_iff.1 hzc v⁻¹).symm
      calc u * z * v⁻¹ * (u * z)⁻¹ = u * (z * v⁻¹) * z⁻¹ * u⁻¹ := by group
        _ = u * (v⁻¹ * z) * z⁻¹ * u⁻¹ := by rw [this]
        _ = u * v⁻¹ * u⁻¹ := by group
    rw [hzz]; group
  have hcv : u * v * u⁻¹ = c * v := by rw [hc]; group
  have hcinv : c = c⁻¹ := by
    have h1 : u * v⁻¹ * u⁻¹ = v⁻¹ * c⁻¹ := by
      have : u * v⁻¹ * u⁻¹ = (u * v * u⁻¹)⁻¹ := by group
      rw [this, hcv, mul_inv_rev]
    have h2 : c = v⁻¹ * c⁻¹ * v := by
      calc c = b * c * b⁻¹ := hz1.symm
        _ = u * v⁻¹ * u⁻¹ * v := hz2
        _ = v⁻¹ * c⁻¹ * v := by rw [h1]
    have h3 : v⁻¹ * c⁻¹ * v = c⁻¹ := by
      rw [(Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hcc) v⁻¹), mul_assoc, inv_mul_cancel,
        mul_one]
    exact h2.trans h3
  have hc2 : c * c = 1 := mul_eq_one_iff_eq_inv.2 hcinv
  have hc3 : c ^ 3 = 1 := by
    have h1 : (u * v * u⁻¹) ^ 3 = 1 := by rw [conj_pow, hv]; simp
    rw [hcv] at h1
    have hcm : Commute c v := Subgroup.mem_center_iff.1 hcc v |>.symm
    rwa [hcm.mul_pow, hv, mul_one] at h1
  have hc1 : c = 1 := by
    have : c = c ^ 3 * (c * c)⁻¹ := by group
    rw [this, hc3, hc2]; simp
  exact (commutatorElement_eq_one_iff_mul_comm).1 hc1

section Pair

variable {H : Type*} [Group H] {x y : H}

theorem exists_pow_mul_pow_of_mem_closure (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    {z : H} (hz : z ∈ Subgroup.closure {x, y}) : ∃ a b : ℕ, z = x ^ a * y ^ b := by
  have hc : Commute x y := hxy
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul z₁ z₂ _ _ h1 h2 =>
    obtain ⟨a, b, rfl⟩ := h1
    obtain ⟨c, d, rfl⟩ := h2
    refine ⟨a + c, b + d, ?_⟩
    have : y ^ b * x ^ c = x ^ c * y ^ b := (hc.symm.pow_pow b c).eq
    calc x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ a * (y ^ b * x ^ c) * y ^ d := by group
      _ = x ^ a * (x ^ c * y ^ b) * y ^ d := by rw [this]
      _ = x ^ (a + c) * y ^ (b + d) := by rw [pow_add, pow_add]; group
  | inv z _ h1 =>
    obtain ⟨a, b, rfl⟩ := h1
    refine ⟨2 * a, 2 * b, ?_⟩
    have e1 : (x ^ a)⁻¹ = x ^ (2 * a) :=
      inv_eq_of_mul_eq_one_right (by
        rw [← pow_add, show a + 2 * a = 3 * a by ring, pow_mul, hx, one_pow])
    have e2 : (y ^ b)⁻¹ = y ^ (2 * b) :=
      inv_eq_of_mul_eq_one_right (by
        rw [← pow_add, show b + 2 * b = 3 * b by ring, pow_mul, hy, one_pow])
    have : x ^ (2 * a) * y ^ (2 * b) = y ^ (2 * b) * x ^ (2 * a) := (hc.pow_pow _ _).eq
    rw [mul_inv_rev, e1, e2, this]

theorem isElemAbelian_closure_pair (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    IsMulCommutative (Subgroup.closure {x, y}) ∧ ∀ z ∈ Subgroup.closure {x, y}, z ^ 3 = 1 := by
  have hc : Commute x y := hxy
  refine ⟨Subgroup.isMulCommutative_closure ?_, ?_⟩
  · intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  · intro z hz
    obtain ⟨a, b, rfl⟩ := exists_pow_mul_pow_of_mem_closure hxy hx hy hz
    rw [((hc.pow_pow a b)).mul_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul, hx,
      hy]
    simp

theorem card_closure_pair (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hinj : ∀ a b : ℕ, x ^ a * y ^ b = 1 → 3 ∣ a ∧ 3 ∣ b) :
    Nat.card (Subgroup.closure {x, y}) = 9 := by
  have hc : Commute x y := hxy
  have hxm : ∀ n : ℕ, x ^ n = x ^ (n % 3) := fun n => pow_eq_pow_mod n hx
  have hym : ∀ n : ℕ, y ^ n = y ^ (n % 3) := fun n => pow_eq_pow_mod n hy
  let f : Fin 3 × Fin 3 → Subgroup.closure {x, y} := fun p =>
    ⟨x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ), Subgroup.mul_mem _ (Subgroup.pow_mem _
      (Subgroup.subset_closure (by simp)) _) (Subgroup.pow_mem _
      (Subgroup.subset_closure (by simp)) _)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' : x ^ (a : ℕ) * y ^ (b : ℕ) = x ^ (a' : ℕ) * y ^ (b' : ℕ) := congrArg Subtype.val h
      have key : x ^ ((a : ℕ) + 2 * (a' : ℕ)) * y ^ ((b : ℕ) + 2 * (b' : ℕ)) = 1 := by
        have e : x ^ ((a : ℕ) + 2 * (a' : ℕ)) * y ^ ((b : ℕ) + 2 * (b' : ℕ)) =
            (x ^ (a : ℕ) * y ^ (b : ℕ)) * (x ^ (2 * (a' : ℕ)) * y ^ (2 * (b' : ℕ))) := by
          rw [pow_add, pow_add]
          have : y ^ (b : ℕ) * x ^ (2 * (a' : ℕ)) = x ^ (2 * (a' : ℕ)) * y ^ (b : ℕ) :=
            (hc.symm.pow_pow _ _).eq
          calc x ^ (a : ℕ) * x ^ (2 * (a' : ℕ)) * (y ^ (b : ℕ) * y ^ (2 * (b' : ℕ))) =
              x ^ (a : ℕ) * (x ^ (2 * (a' : ℕ)) * y ^ (b : ℕ)) * y ^ (2 * (b' : ℕ)) := by group
            _ = x ^ (a : ℕ) * (y ^ (b : ℕ) * x ^ (2 * (a' : ℕ))) * y ^ (2 * (b' : ℕ)) := by rw [this]
            _ = _ := by group
        rw [e, h']
        have : y ^ (b' : ℕ) * x ^ (2 * (a' : ℕ)) = x ^ (2 * (a' : ℕ)) * y ^ (b' : ℕ) :=
          (hc.symm.pow_pow _ _).eq
        calc x ^ (a' : ℕ) * y ^ (b' : ℕ) * (x ^ (2 * (a' : ℕ)) * y ^ (2 * (b' : ℕ)))
            = x ^ (a' : ℕ) * (y ^ (b' : ℕ) * x ^ (2 * (a' : ℕ))) * y ^ (2 * (b' : ℕ)) := by group
          _ = x ^ (a' : ℕ) * (x ^ (2 * (a' : ℕ)) * y ^ (b' : ℕ)) * y ^ (2 * (b' : ℕ)) := by rw [this]
          _ = x ^ (3 * (a' : ℕ)) * y ^ (3 * (b' : ℕ)) := by
            rw [show 3 * (a' : ℕ) = (a' : ℕ) + 2 * (a' : ℕ) by ring, show 3 * (b' : ℕ) = (b' : ℕ) + 2 * (b' : ℕ) by ring, pow_add, pow_add]
            group
          _ = 1 := by rw [pow_mul, pow_mul, hx, hy]; simp
      obtain ⟨h1, h2⟩ := hinj _ _ key
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · show (a : ℕ) = (a' : ℕ)
        omega
      · show (b : ℕ) = (b' : ℕ)
        omega
    · rintro ⟨z, hz⟩
      obtain ⟨a, b, rfl⟩ := exists_pow_mul_pow_of_mem_closure hxy hx hy hz
      refine ⟨(⟨a % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show x ^ (a % 3) * y ^ (b % 3) = x ^ a * y ^ b
      rw [← hxm, ← hym]
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

end Pair

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
