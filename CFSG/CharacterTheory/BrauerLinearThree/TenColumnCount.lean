module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Transfer
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators Classical

namespace CFSG.BrauerLinearThree

namespace TenColumn

variable {G : Type} [Group G] [Finite G] {W K H : Subgroup G}

@[expose] noncomputable def torusTransfer (hWK : W ≤ K) (χ : W →* ℂˣ) : K →* ℂˣ :=
  MonoidHom.transfer (χ.comp (Subgroup.subgroupOfEquivOfLe hWK).toMonoidHom)

noncomputable abbrev torusIndex (W K : Subgroup G) : ℕ := (W.subgroupOf K).index

omit [Finite G] in
theorem pow_torusIndex_mem (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k) (k : K) :
    (k : G) ^ torusIndex W K ∈ W := by
  have key : ∀ (n : ℕ) (g₀ : K), g₀⁻¹ * k ^ n * g₀ ∈ W.subgroupOf K →
      g₀⁻¹ * k ^ n * g₀ = k ^ n := by
    intro n g₀ hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hc := hcent g₀ g₀.2 _ hg
    apply Subtype.ext
    have h1 : (g₀ : G) * ((g₀⁻¹ * k ^ n * g₀ : K) : G) = ((k ^ n : K) : G) * g₀ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      group
    rw [hc] at h1
    exact mul_right_cancel h1
  have h := MonoidHom.transfer_eq_pow_aux (H := W.subgroupOf K) k key
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h
  exact h

theorem torusTransfer_apply (hWK : W ≤ K) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (χ : W →* ℂˣ) (k : K) :
    torusTransfer hWK χ k = χ ⟨(k : G) ^ torusIndex W K, pow_torusIndex_mem hcent k⟩ := by
  have key : ∀ (n : ℕ) (g₀ : K), g₀⁻¹ * k ^ n * g₀ ∈ W.subgroupOf K →
      g₀⁻¹ * k ^ n * g₀ = k ^ n := by
    intro n g₀ hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hc := hcent g₀ g₀.2 _ hg
    apply Subtype.ext
    have h1 : (g₀ : G) * ((g₀⁻¹ * k ^ n * g₀ : K) : G) = ((k ^ n : K) : G) * g₀ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      group
    rw [hc] at h1
    exact mul_right_cancel h1
  rw [torusTransfer, MonoidHom.transfer_eq_pow _ k key]
  rfl

theorem pow_mem_of_torusTransfer_ne_one (hWK : W ≤ K) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (χ : W →* ℂˣ) {k : K} (hk : torusTransfer hWK χ k ≠ 1) :
    (k : G) ^ torusIndex W K ∈ W ∧ (k : G) ^ torusIndex W K ≠ 1 := by
  refine ⟨pow_torusIndex_mem hcent k, fun h1 => hk ?_⟩
  rw [torusTransfer_apply hWK hcent]
  have : (⟨(k : G) ^ torusIndex W K, pow_torusIndex_mem hcent k⟩ : W) = 1 := Subtype.ext h1
  rw [this, map_one]

theorem torusTransfer_conj_of_mem (hWK : W ≤ K) (χ : W →* ℂˣ) (k k' : K) :
    torusTransfer hWK χ (k' * k * k'⁻¹) = torusTransfer hWK χ k := by
  rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem torusTransfer_conj_of_not_mem (hWK : W ≤ K) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (hinv : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) (χ : W →* ℂˣ) {h : G} (hH : h ∈ H)
    (hK : h ∉ K) (k : K) (hk : h * (k : G) * h⁻¹ ∈ K) :
    torusTransfer hWK χ ⟨h * (k : G) * h⁻¹, hk⟩ = (torusTransfer hWK χ k)⁻¹ := by
  rw [torusTransfer_apply hWK hcent, torusTransfer_apply hWK hcent, ← map_inv]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_inv]
  rw [conj_pow, hinv h hH hK _ (pow_torusIndex_mem hcent k)]

theorem mem_of_torusTransfer_conj_ne_one (hWK : W ≤ K)
    (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (hTI : ∀ g : G, ∀ w ∈ W, w ≠ 1 → g * w * g⁻¹ ∈ W → g ∈ H) (χ : W →* ℂˣ) {k : K}
    (hk : torusTransfer hWK χ k ≠ 1) (g : G) (hg : g⁻¹ * (k : G) * g ∈ K) : g ∈ H := by
  obtain ⟨hW, hne⟩ := pow_mem_of_torusTransfer_ne_one hWK hcent χ hk
  have hmem : g⁻¹ * (k : G) ^ torusIndex W K * g⁻¹⁻¹ ∈ W := by
    have h := pow_torusIndex_mem hcent ⟨_, hg⟩
    have e1 := conj_pow (a := g⁻¹) (b := (k : G)) (i := torusIndex W K)
    rw [inv_inv] at e1
    rw [inv_inv, ← e1]
    exact h
  have h := hTI g⁻¹ _ hW hne hmem
  simpa using H.inv_mem h

theorem mem_of_inverts (hWK : W ≤ K) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (hTI : ∀ g : G, ∀ w ∈ W, w ≠ 1 → g * w * g⁻¹ ∈ W → g ∈ H) (χ : W →* ℂˣ) {k : K}
    (hk : torusTransfer hWK χ k ≠ 1) {x : G} (hx : x * (k : G) * x⁻¹ = (k : G)⁻¹) : x ∈ H := by
  have hx' : x⁻¹⁻¹ * (k : G) * x⁻¹ ∈ K := by
    rw [inv_inv, hx]
    exact K.inv_mem k.2
  have h := mem_of_torusTransfer_conj_ne_one hWK hcent hTI χ hk x⁻¹ hx'
  simpa using H.inv_mem h

theorem torusTransfer_pow_orderOf (hWK : W ≤ K) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (χ : W →* ℂˣ) (k : K) : (torusTransfer hWK χ k) ^ orderOf χ = 1 := by
  rw [torusTransfer_apply hWK hcent, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
    MonoidHom.one_apply]

theorem torusTransfer_eq_one_of_eq_inv (hWK : W ≤ K) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (χ : W →* ℂˣ) (hχ : Odd (orderOf χ)) {k : K}
    (h1 : torusTransfer hWK χ k = (torusTransfer hWK χ k)⁻¹) : torusTransfer hWK χ k = 1 := by
  have h2 : (torusTransfer hWK χ k) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _
  have h3 := pow_gcd_eq_one.mpr ⟨h2, torusTransfer_pow_orderOf hWK hcent χ k⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hχ), pow_one] at h3

theorem torusTransfer_eq_one_of_inverts_mem (hWK : W ≤ K)
    (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k) (χ : W →* ℂˣ) (hχ : Odd (orderOf χ)) {k x : K}
    (hx : x * k * x⁻¹ = k⁻¹) : torusTransfer hWK χ k = 1 := by
  apply torusTransfer_eq_one_of_eq_inv hWK hcent χ hχ
  have h := torusTransfer_conj_of_mem hWK χ k x
  rw [hx, map_inv] at h
  exact h.symm

@[expose] noncomputable def torusTransferFun (hWK : W ≤ K) (χ : W →* ℂˣ) (g : G) : ℂ :=
  if h : g ∈ K then (torusTransfer hWK χ ⟨g, h⟩ : ℂ) else 0

theorem torusTransferFun_of_mem (hWK : W ≤ K) (χ : W →* ℂˣ) {g : G} (hg : g ∈ K) :
    torusTransferFun hWK χ g = (torusTransfer hWK χ ⟨g, hg⟩ : ℂ) := by
  rw [torusTransferFun, dite_eq_left hg]

@[expose] noncomputable def outerInvolutions [Fintype G] (K H : Subgroup G) : Finset G :=
  Finset.univ.filter (fun x : G => x ∈ H ∧ x ∉ K ∧ x * x = 1)

omit [Finite G] in
theorem mem_outerInvolutions [Fintype G] {x : G} :
    x ∈ outerInvolutions K H ↔ x ∈ H ∧ x ∉ K ∧ x * x = 1 := by
  simp [outerInvolutions]

@[expose] noncomputable def invertingInvolutions [Fintype G] (k : G) : Finset G :=
  Finset.univ.filter (fun x : G => x * x = 1 ∧ x ≠ 1 ∧ x * k * x⁻¹ = k⁻¹)

omit [Finite G] in
theorem mem_invertingInvolutions [Fintype G] {k x : G} :
    x ∈ invertingInvolutions k ↔ x * x = 1 ∧ x ≠ 1 ∧ x * k * x⁻¹ = k⁻¹ := by
  simp [invertingInvolutions]

variable (hWK : W ≤ K) (hKH : K ≤ H) (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
  (hinv : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
  (hKH2 : ∀ x ∈ H, ∀ y ∈ H, x ∉ K → y ∉ K → x * y ∈ K)
  (hTI : ∀ g : G, ∀ w ∈ W, w ≠ 1 → g * w * g⁻¹ ∈ W → g ∈ H)

include hcent hTI in
theorem invertingInvolutions_eq [Fintype G] (χ : W →* ℂˣ) (hχ : Odd (orderOf χ)) {k : K}
    (hk : torusTransfer hWK χ k ≠ 1) :
    invertingInvolutions (k : G) =
      (outerInvolutions K H).filter (fun x => x * (k : G) * x⁻¹ = (k : G)⁻¹) := by
  ext x
  rw [mem_invertingInvolutions, Finset.mem_filter, mem_outerInvolutions]
  constructor
  · rintro ⟨hx2, -, hxk⟩
    refine ⟨⟨mem_of_inverts hWK hcent hTI χ hk hxk, fun hxK => hk ?_, hx2⟩, hxk⟩
    exact torusTransfer_eq_one_of_inverts_mem hWK hcent χ hχ (k := k) (x := ⟨x, hxK⟩)
      (Subtype.ext (by simpa using hxk))
  · rintro ⟨⟨-, hxK, hx2⟩, hxk⟩
    exact ⟨hx2, fun h1 => hxK (h1 ▸ K.one_mem), hxk⟩

omit [Finite G] in
include hKH hKH2 in
theorem sum_inverted_eq [Fintype G] (f : G → ℂ) {x : G} (hx : x ∈ outerInvolutions K H) :
    ∑ k : K, (if x * (k : G) * x⁻¹ = (k : G)⁻¹ then f k else 0) =
      ∑ y ∈ outerInvolutions K H, f (x * y) := by
  obtain ⟨hxH, hxK, hx2⟩ := mem_outerInvolutions.mp hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun k _ => x * (k : G)) (fun y hy => ⟨x * y, ?_⟩) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hyH, hyK, -⟩ := mem_outerInvolutions.mp hy
    exact hKH2 x hxH y hyH hxK hyK
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [mem_outerInvolutions]
    refine ⟨H.mul_mem hxH (hKH k.2), fun h => hxK ?_, ?_⟩
    · have := K.mul_mem h (K.inv_mem k.2)
      rwa [mul_inv_cancel_right] at this
    · have h2 := hk.2
      rw [hxinv] at h2
      calc x * (k : G) * (x * k) = (x * k * x) * k := by group
        _ = 1 := by rw [h2, inv_mul_cancel]
  · intro y hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨-, -, hy2⟩ := mem_outerInvolutions.mp hy
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    change x * (x * y) * x⁻¹ = (x * y)⁻¹
    rw [hxinv, mul_inv_rev, hxinv, hyinv]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hx2, one_mul]
  · intro k _
    apply Subtype.ext
    change x * (x * (k : G)) = k
    rw [← mul_assoc, hx2, one_mul]
  · intro y _
    change x * (x * y) = y
    rw [← mul_assoc, hx2, one_mul]
  · intro k _
    rw [← mul_assoc, hx2, one_mul]

include hKH hinv in
theorem sum_torusTransferFun_mul_eq_zero [Fintype G] (χ : W →* ℂˣ) {w₀ : G} (hw₀ : w₀ ∈ W)
    (hw₀1 : torusTransfer hWK χ ⟨w₀, hWK hw₀⟩ ≠ 1) (x : G) :
    ∑ y ∈ outerInvolutions K H, torusTransferFun hWK χ (x * y) = 0 := by
  set S := ∑ y ∈ outerInvolutions K H, torusTransferFun hWK χ (x * y) with hS
  have hshift : S = S * (torusTransfer hWK χ ⟨w₀, hWK hw₀⟩ : ℂ) := by
    rw [hS, Finset.sum_mul]
    refine Finset.sum_bij' (fun y _ => y * w₀⁻¹) (fun y _ => y * w₀) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨hyH, hyK, hy2⟩ := mem_outerInvolutions.mp hy
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have hw : y * w₀⁻¹ * y⁻¹ = w₀ := by
        rw [hinv y hyH hyK _ (W.inv_mem hw₀), inv_inv]
      rw [mem_outerInvolutions]
      refine ⟨H.mul_mem hyH (hKH (hWK (W.inv_mem hw₀))), fun h => hyK ?_, ?_⟩
      · have := K.mul_mem h (hWK hw₀)
        rwa [inv_mul_cancel_right] at this
      · rw [hyinv] at hw
        calc y * w₀⁻¹ * (y * w₀⁻¹) = (y * w₀⁻¹ * y) * w₀⁻¹ := by group
          _ = 1 := by rw [hw, mul_inv_cancel]
    · intro y hy
      obtain ⟨hyH, hyK, hy2⟩ := mem_outerInvolutions.mp hy
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have hw : y * w₀ * y⁻¹ = w₀⁻¹ := hinv y hyH hyK _ hw₀
      rw [mem_outerInvolutions]
      refine ⟨H.mul_mem hyH (hKH (hWK hw₀)), fun h => hyK ?_, ?_⟩
      · have := K.mul_mem h (hWK (W.inv_mem hw₀))
        rwa [mul_inv_cancel_right] at this
      · rw [hyinv] at hw
        calc y * w₀ * (y * w₀) = (y * w₀ * y) * w₀ := by group
          _ = 1 := by rw [hw, inv_mul_cancel]
    · intro y _
      exact inv_mul_cancel_right y w₀
    · intro y _
      exact mul_inv_cancel_right y w₀
    · intro y hy
      by_cases hxy : x * y ∈ K
      · have hxyw : x * (y * w₀⁻¹) ∈ K := by
          rw [← mul_assoc]
          exact K.mul_mem hxy (hWK (W.inv_mem hw₀))
        rw [torusTransferFun_of_mem hWK χ hxy, torusTransferFun_of_mem hWK χ hxyw, ← Units.val_mul,
          ← map_mul]
        congr 2
        apply Subtype.ext
        change x * y = x * (y * w₀⁻¹) * w₀
        group
      · have hxyw : x * (y * w₀⁻¹) ∉ K := by
          intro h
          apply hxy
          have := K.mul_mem h (hWK hw₀)
          rwa [← mul_assoc, inv_mul_cancel_right] at this
        rw [torusTransferFun, dite_eq_right hxy, torusTransferFun, dite_eq_right hxyw, zero_mul]
  have h0 : S * (1 - (torusTransfer hWK χ ⟨w₀, hWK hw₀⟩ : ℂ)) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exfalso
    apply hw₀1
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.mp h).symm

include hKH hcent hinv hKH2 hTI in
theorem sum_torusTransfer_involution_count [Fintype G] (χ : W →* ℂˣ) (hχ : Odd (orderOf χ))
    {w₀ : G} (hw₀ : w₀ ∈ W) (hw₀1 : torusTransfer hWK χ ⟨w₀, hWK hw₀⟩ ≠ 1) :
    ∑ k : K, (1 - (torusTransfer hWK χ k : ℂ)) * ((invertingInvolutions (k : G)).card : ℂ) =
      ((outerInvolutions K H).card : ℂ) ^ 2 := by
  have hstep1 : ∀ k : K, (1 - (torusTransfer hWK χ k : ℂ)) *
      ((invertingInvolutions (k : G)).card : ℂ) =
      ∑ x ∈ outerInvolutions K H,
        (if x * (k : G) * x⁻¹ = (k : G)⁻¹ then 1 - (torusTransfer hWK χ k : ℂ) else 0) := by
    intro k
    by_cases hk : torusTransfer hWK χ k = 1
    · rw [hk, Units.val_one, sub_self, zero_mul]
      exact (Finset.sum_eq_zero fun x _ => by simp).symm
    · rw [invertingInvolutions_eq hWK hcent hTI χ hχ hk, ← Finset.sum_filter,
        Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl fun k _ => hstep1 k, Finset.sum_comm]
  have hstep2 : ∀ x ∈ outerInvolutions K H, ∑ k : K,
      (if x * (k : G) * x⁻¹ = (k : G)⁻¹ then 1 - (torusTransfer hWK χ k : ℂ) else 0) =
      ∑ y ∈ outerInvolutions K H, (1 - torusTransferFun hWK χ (x * y)) := by
    intro x hx
    rw [← sum_inverted_eq hKH hKH2 (fun g => 1 - torusTransferFun hWK χ g) hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [torusTransferFun_of_mem hWK χ k.2]
  have hstep3 : ∀ x ∈ outerInvolutions K H,
      ∑ y ∈ outerInvolutions K H, (1 - torusTransferFun hWK χ (x * y)) =
        ((outerInvolutions K H).card : ℂ) := by
    intro x _
    rw [Finset.sum_sub_distrib, sum_torusTransferFun_mul_eq_zero hWK hKH hinv χ hw₀ hw₀1,
      sub_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl hstep2, Finset.sum_congr rfl hstep3, Finset.sum_const, nsmul_eq_mul,
    sq]

end TenColumn

end CFSG.BrauerLinearThree
