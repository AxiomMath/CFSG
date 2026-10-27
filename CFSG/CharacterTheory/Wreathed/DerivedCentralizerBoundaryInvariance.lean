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

public section

namespace CFSG.Wreathed

variable {M : Type*} [Group M]

theorem mem_of_sq_mem_of_odd_orderOf {H : Subgroup M} {c : M} (hc : Odd (orderOf c))
    (hc2 : c ^ 2 ∈ H) : c ∈ H := by
  obtain ⟨k, hk⟩ := hc
  have h : c = (c ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h]
  exact H.pow_mem hc2 _

theorem trivialAction_subgroup (K X : Subgroup M) [K.Normal] [X.Normal] :
    ∃ T : Subgroup M, T.Normal ∧ ∀ g : M, g ∈ T ↔ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ X := by
  let π := QuotientGroup.mk' X
  have hKn : (K.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective X)
  refine ⟨(Subgroup.centralizer (K.map π : Set (M ⧸ X))).comap π,
    Subgroup.Normal.comap Subgroup.normal_centralizer π, fun g => ?_⟩
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have := h (π k) ⟨k, hk, rfl⟩
    rw [← QuotientGroup.eq_one_iff]
    change π (g * k * g⁻¹ * k⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [← this]
    group
  · rintro h _ ⟨k, hk, rfl⟩
    have := (QuotientGroup.eq_one_iff _).mpr (h k hk)
    change π (g * k * g⁻¹ * k⁻¹) = 1 at this
    simp only [map_mul, map_inv] at this
    have h2 : π k * π g = π g * π k := by
      calc π k * π g = (π g * π k * (π g)⁻¹ * (π k)⁻¹)⁻¹ * (π g * π k) := by group
        _ = π g * π k := by rw [this, inv_one, one_mul]
    exact h2

theorem characteristic_derived_centralizer_forces_boundary_invariance [Finite M]
    (C K : Subgroup M) [C.Normal] [K.Normal] (hKC : K ≤ C) (hKodd : Odd (Nat.card K))
    (w a : M) (hw : w * w = 1) (ha : Odd (orderOf a)) (hwa : w⁻¹ * a * w = a⁻¹)
    (hgen : Subgroup.closure ((C : Set M) ∪ {w, a}) = ⊤)
    (A W : Subgroup M) (hAK : A ≤ K) (hWK : W ≤ K)
    (_hAn : ∀ k ∈ K, ∀ x ∈ A, k * x * k⁻¹ ∈ A) (hWn : ∀ k ∈ K, ∀ x ∈ W, k * x * k⁻¹ ∈ W)
    [IsCyclic W] (_hWA : W ⊓ A = ⊥) (hWAc : ∀ x ∈ W, ∀ y ∈ A, x * y = y * x)
    (hBC : ∀ c ∈ C, ∀ b ∈ W ⊔ A, c * b * c⁻¹ ∈ W ⊔ A)
    (hKB : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ W ⊔ A)
    (hCKB : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ W ⊔ A)
    (hwA : ∀ x ∈ A, w * x * w⁻¹ ∈ A) (hwW : ∀ x ∈ W, w * x * w⁻¹ ∈ W)
    (hwAc : ∀ x ∈ A, w * x = x * w) (hwKB : ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ W ⊔ A)
    (hcent : ∀ k ∈ K, (∀ x ∈ ⁅K, K⁆, k * x * k⁻¹ * x⁻¹ ∈ A) ↔ k ∈ W ⊔ A) :
    let B : Subgroup M := W ⊔ A
    let X : Subgroup M := K ⊓ Subgroup.centralizer ((⁅K, K⁆ : Subgroup M) : Set M)
    X.Normal ∧ W ≤ X ∧ X ≤ B ∧ (∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ X) ∧
      (∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ X) ∧ B.Normal ∧
      (∀ g : M, ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ B) ∧ ⁅(⊤ : Subgroup M), K⁆ ≤ B := by
  intro B X
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hBK : B ≤ K := sup_le hWK hAK
  have hK'B : ⁅K, K⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact hKB x hx y hy
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have h := (IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hBcentW : B ≤ Subgroup.centralizer (W : Set M) := by
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hWcomm z hz x hx
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hWAc z hz y hy
  have hWX : W ≤ X := by
    intro x hx
    refine ⟨hWK hx, ?_⟩
    have hW : W ≤ Subgroup.centralizer (B : Set M) := Subgroup.le_centralizer_iff.mp hBcentW
    exact Subgroup.centralizer_le hK'B (hW hx)
  have hXB : X ≤ B := by
    intro k hk
    refine (hcent k hk.1).mp fun x hx => ?_
    have h := Subgroup.mem_centralizer_iff.mp hk.2 x hx
    have h1 : k * x * k⁻¹ * x⁻¹ = 1 := by
      rw [← h]
      group
    rw [h1]
    exact A.one_mem
  have hXn : X.Normal := by
    have : (⁅K, K⁆ : Subgroup M).Normal := Subgroup.commutator_normal K K
    have : (Subgroup.centralizer ((⁅K, K⁆ : Subgroup M) : Set M)).Normal :=
      Subgroup.normal_centralizer
    exact Subgroup.normal_inf_normal _ _
  have hwBW' : ∀ b ∈ Subgroup.closure ((W : Set M) ∪ A), b⁻¹ * (w * b * w⁻¹) ∈ W := by
    intro b hb'
    induction hb' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact W.mul_mem (W.inv_mem hx) (hwW x hx)
      · rw [hwAc x hx, mul_inv_cancel_right, inv_mul_cancel]
        exact W.one_mem
    | one => simp [W.one_mem]
    | mul x y _ hy ihx ihy =>
      have hyK : y ∈ K := hBK (show y ∈ W ⊔ A by rw [Subgroup.sup_eq_closure]; exact hy)
      have h : (x * y)⁻¹ * (w * (x * y) * w⁻¹) =
          (y⁻¹ * (x⁻¹ * (w * x * w⁻¹)) * y⁻¹⁻¹) * (y⁻¹ * (w * y * w⁻¹)) := by group
      rw [h]
      exact W.mul_mem (hWn y⁻¹ (K.inv_mem hyK) _ ihx) ihy
    | inv x hx ihx =>
      have hxK : x ∈ K := hBK (show x ∈ W ⊔ A by rw [Subgroup.sup_eq_closure]; exact hx)
      have h : x⁻¹⁻¹ * (w * x⁻¹ * w⁻¹) = x * (x⁻¹ * (w * x * w⁻¹))⁻¹ * x⁻¹ := by group
      rw [h]
      exact hWn x hxK _ (W.inv_mem ihx)
  have hwBW : ∀ b ∈ B, b⁻¹ * (w * b * w⁻¹) ∈ W := fun b hb =>
    hwBW' b (by rw [← Subgroup.sup_eq_closure]; exact hb)
  have hwK : ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ W := by
    intro r hr
    set c := r⁻¹ * (w * r * w⁻¹) with hc
    have hcB : c ∈ B := by
      have h1 : w * r * w⁻¹ * r⁻¹ ∈ B := hwKB r hr
      have h2 := hBC r⁻¹ (hKC (K.inv_mem hr)) _ h1
      have h3 : c = r⁻¹ * (w * r * w⁻¹ * r⁻¹) * r⁻¹⁻¹ := by rw [hc]; group
      rw [h3]
      exact h2
    have hwc : w * c * w⁻¹ = c⁻¹ := by
      have h : w * (w * r * w⁻¹) * w⁻¹ = r := by
        calc w * (w * r * w⁻¹) * w⁻¹ = (w * w) * r * (w * w)⁻¹ := by group
          _ = r := by rw [hw, one_mul, inv_one, mul_one]
      have hrc : w * r * w⁻¹ = r * c := by rw [hc]; group
      have h2 : w * (r * c) * w⁻¹ = r := by rw [← hrc]; exact h
      have h3 : w * (r * c) * w⁻¹ = (w * r * w⁻¹) * (w * c * w⁻¹) := by group
      rw [h3, hrc] at h2
      calc w * c * w⁻¹ = (r * c)⁻¹ * ((r * c) * (w * c * w⁻¹)) := by group
        _ = c⁻¹ := by rw [h2]; group
    have hc2 : c ^ 2 ∈ W := by
      have h := hwBW c hcB
      rw [hwc] at h
      have h' : c ^ 2 = (c⁻¹ * c⁻¹)⁻¹ := by group
      rw [h']
      exact W.inv_mem h
    have hcK : c ∈ K := hBK hcB
    have hcodd : Odd (orderOf c) := by
      have hdvd : orderOf c ∣ Nat.card K := by
        rw [← Subgroup.orderOf_mk c hcK]
        exact orderOf_dvd_natCard _
      exact hKodd.of_dvd_nat hdvd
    have hcW : c ∈ W := mem_of_sq_mem_of_odd_orderOf hcodd hc2
    have h : w * r * w⁻¹ * r⁻¹ = r * c * r⁻¹ := by rw [hc]; group
    rw [h]
    exact hWn r hr c hcW
  have hwKX : ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ X := fun k hk => hWX (hwK k hk)
  have haKX : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ X := by
    obtain ⟨T, hTn, hT⟩ := trivialAction_subgroup K X
    have hwT : w ∈ T := (hT w).mpr hwKX
    let ψ := QuotientGroup.mk' T
    have hψw : ψ w = 1 := (QuotientGroup.eq_one_iff w).mpr hwT
    have hψa : ψ a * ψ a = 1 := by
      have h := congrArg ψ hwa
      simp only [map_mul, map_inv, hψw, inv_one, one_mul, mul_one] at h
      calc ψ a * ψ a = (ψ a)⁻¹ * ψ a := by rw [← h]
        _ = 1 := inv_mul_cancel _
    have hψa1 : ψ a = 1 := by
      have h2 : ψ a ^ 2 = 1 := by rw [sq]; exact hψa
      have hn : ψ a ^ orderOf a = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      obtain ⟨k, hk⟩ := ha
      have : ψ a = (ψ a ^ 2) ^ (k + 1) * (ψ a ^ orderOf a)⁻¹ := by
        rw [← pow_mul, hk]
        group
      rw [this, h2, hn, one_pow, inv_one, one_mul]
    exact (hT a).mp ((QuotientGroup.eq_one_iff a).mp hψa1)
  have hwB' : ∀ b ∈ Subgroup.closure ((W : Set M) ∪ A),
      w * b * w⁻¹ ∈ Subgroup.closure ((W : Set M) ∪ A) := by
    intro b hb'
    induction hb' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Subgroup.subset_closure (Or.inl (hwW x hx))
      · exact Subgroup.subset_closure (Or.inr (hwA x hx))
    | one => simp
    | mul x y _ _ ihx ihy =>
      have h : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ihx =>
      have h : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ihx
  have hwB : ∀ b ∈ B, w * b * w⁻¹ ∈ B := fun b hb => by
    have h := hwB' b (by rw [← Subgroup.sup_eq_closure]; exact hb)
    rw [← Subgroup.sup_eq_closure] at h
    exact h
  have hBn : B.Normal := by
    have hle : Subgroup.closure ((C : Set M) ∪ {w, a}) ≤ Subgroup.normalizer (B : Set M) := by
      rw [Subgroup.closure_le]
      rintro g (hg | hg | hg)
      · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
        intro b
        constructor
        · intro hb
          exact hBC g hg b hb
        · intro hb
          have h := hBC g⁻¹ (C.inv_mem hg) _ hb
          have e : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
          rw [e] at h
          exact h
      · obtain rfl : g = w := hg
        rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
        intro b
        constructor
        · intro hb
          exact hwB b hb
        · intro hb
          have h := hwB _ hb
          have e : g * (g * b * g⁻¹) * g⁻¹ = b := by
            calc g * (g * b * g⁻¹) * g⁻¹ = (g * g) * b * (g * g)⁻¹ := by group
              _ = b := by rw [hw, one_mul, inv_one, mul_one]
          rw [e] at h
          exact h
      · obtain rfl : g = a := hg
        rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
        intro b
        constructor
        · intro hb
          have h1 := hXB (haKX b (hBK hb))
          have h : g * b * g⁻¹ = (g * b * g⁻¹ * b⁻¹) * b := by group
          rw [h]
          exact B.mul_mem h1 hb
        · intro hb
          have hbK : g * b * g⁻¹ ∈ K := hBK hb
          have hbK' : b ∈ K := by
            have h := (inferInstance : K.Normal).conj_mem _ hbK g⁻¹
            have e : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
            rw [e] at h
            exact h
          have h1 := hXB (haKX b hbK')
          have h : b = (g * b * g⁻¹ * b⁻¹)⁻¹ * (g * b * g⁻¹) := by group
          rw [h]
          exact B.mul_mem (B.inv_mem h1) hb
    rw [hgen, top_le_iff] at hle
    exact Subgroup.normalizer_eq_top_iff.mp hle
  have hall : ∀ g : M, ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ B := by
    obtain ⟨T, -, hT⟩ := trivialAction_subgroup K B
    have hle : Subgroup.closure ((C : Set M) ∪ {w, a}) ≤ T := by
      rw [Subgroup.closure_le]
      rintro g (hg | hg | hg)
      · exact (hT g).mpr (hCKB g hg)
      · obtain rfl : g = w := hg
        exact (hT g).mpr hwKB
      · obtain rfl : g = a := hg
        exact (hT g).mpr fun k hk => hXB (haKX k hk)
    rw [hgen, top_le_iff] at hle
    intro g
    exact (hT g).mp (hle ▸ Subgroup.mem_top g)
  refine ⟨hXn, hWX, hXB, hwKX, haKX, hBn, hall, ?_⟩
  rw [Subgroup.commutator_le]
  intro g _ k hk
  rw [commutatorElement_def]
  exact hall g k hk

end CFSG.Wreathed
