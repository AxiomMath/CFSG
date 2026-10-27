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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

section Algebra

variable {M : Type*} [AddCommGroup M] {p : ℕ} [Fact p.Prime]

theorem exists_smul_of_ker_eq_addHom (l₁ l₂ : M →+ ZMod p) (h1 : l₁ ≠ 0)
    (hker : ∀ x, l₁ x = 0 ↔ l₂ x = 0) : ∃ k : ZMod p, ∀ x, l₂ x = k * l₁ x := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, l₁ x₀ ≠ 0 := by
    by_contra! hcon
    exact h1 (DFunLike.ext _ _ hcon)
  refine ⟨l₂ x₀ / l₁ x₀, fun x => ?_⟩
  have hm : l₁ (x - (l₁ x / l₁ x₀).val • x₀) = 0 := by
    rw [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hx₀]
    exact sub_self _
  have h3 := (hker _).1 hm
  rw [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val] at h3
  have h4 := sub_eq_zero.1 h3
  rw [h4]
  ring

end Algebra

section Field

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime]

theorem eq_natCast_of_map_mul_eq (l : F →+ ZMod p) (hl : ∃ a, l a ≠ 0) {ρ : F} {k : ZMod p}
    (h : ∀ a, l (ρ * a) = k * l a) : ρ = (k.val : F) := by
  by_contra hne
  have hr : ρ - (k.val : F) ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨b, hb⟩ := hl
  apply hb
  have h1 : l ((ρ - (k.val : F)) * ((ρ - (k.val : F))⁻¹ * b)) = 0 := by
    have e : l ((k.val : F) * ((ρ - (k.val : F))⁻¹ * b)) =
        k * l ((ρ - (k.val : F))⁻¹ * b) := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [sub_mul, map_sub, h, e]
    exact sub_self _
  rwa [mul_inv_cancel_left₀ hr] at h1

end Field

section Params

variable {F : Type} [Field F] {ε : ℕ}

abbrev UP (F : Type) [Field F] (ε : ℕ) : Type := (Fin ε → F) × F

@[expose] def utau (d : Fin ε → F) (μ : F) : UP F ε →+ UP F ε where
  toFun x := (fun i => μ * x.1 i, μ ^ 2 * x.2 + μ * ∑ i, d i * x.1 i)
  map_zero' := Prod.ext (funext fun i => by simp) (by simp)
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) ?_
    · simp [mul_add]
    · simp [mul_add, Finset.sum_add_distrib]
      ring

@[simp] theorem utau_apply (d : Fin ε → F) (μ : F) (x : UP F ε) :
    utau d μ x = (fun i => μ * x.1 i, μ ^ 2 * x.2 + μ * ∑ i, d i * x.1 i) :=
  rfl

theorem utau_zero_prod (d : Fin ε → F) (μ : F) (a : F) :
    utau d μ (0, a) = (0, μ ^ 2 * a) := by
  exact Prod.ext (funext fun i => by simp) (by simp)

theorem utau_single (d : Fin ε → F) (μ : F) (i : Fin ε) (r : F) :
    utau d μ (Pi.single i r, 0) = (fun j => μ * (Pi.single i r : Fin ε → F) j, μ * (d i * r)) := by
  refine Prod.ext rfl ?_
  simp [Pi.single_apply]

theorem utau_comp (d : Fin ε → F) (μ : F) (x : UP F ε) :
    utau d 1 (utau (0 : Fin ε → F) μ x) = utau d μ x := by
  refine Prod.ext (funext fun i => by simp) ?_
  simp only [utau_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
    one_pow, one_mul, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)

theorem utau_surjective (d : Fin ε → F) {μ : F} (hμ : μ ≠ 0) :
    Function.Surjective (utau d μ) := by
  intro y
  refine ⟨(fun i => μ⁻¹ * y.1 i,
    (μ ^ 2)⁻¹ * (y.2 - μ * ∑ i, d i * (μ⁻¹ * y.1 i))), ?_⟩
  refine Prod.ext (funext fun i => by simp [hμ]) ?_
  simp only [utau_apply]
  field_simp
  ring

end Params

section Count

open scoped Classical

variable {F : Type} [Field F] {ε : ℕ} {p : ℕ} [Fact p.Prime]

theorem card_filter_sq_le [Fintype F] (c : F) :
    (Finset.univ.filter (fun μ : F => μ ^ 2 = c)).card ≤ 2 := by
  by_cases hne : (Finset.univ.filter (fun μ : F => μ ^ 2 = c)).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hy' : y ^ 2 = c := (Finset.mem_filter.1 hy).2
    refine (Finset.card_le_card ?_).trans (Finset.card_le_two (a := y) (b := -y))
    intro x hx
    have hx' : x ^ 2 = c := (Finset.mem_filter.1 hx).2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx'.trans hy'.symm) with h | h
    · simp [h]
    · simp [h]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

@[expose] noncomputable def kerTau (l : UP F ε →+ ZMod p) (x : (Fin ε → F) × Fˣ) :
    AddSubgroup (UP F ε) :=
  (l.comp (utau x.1 (x.2 : F))).ker

variable [Fintype F]

theorem card_fiber_le_addHom (l : UP F ε →+ ZMod p) (hl : ∃ a, l (0, a) ≠ 0)
    (x₀ : (Fin ε → F) × Fˣ) :
    (Finset.univ.filter (fun x : (Fin ε → F) × Fˣ => kerTau l x = kerTau l x₀)).card ≤
      2 * (p - 1) := by
  obtain ⟨d₀, μ₀⟩ := x₀
  set lF : F →+ ZMod p := l.comp (AddMonoidHom.inr (Fin ε → F) F) with hlF
  have hlF' : ∃ a, lF a ≠ 0 := hl
  have hμ₀ : (μ₀ : F) ≠ 0 := μ₀.ne_zero
  have hlFμ : ∀ (μ : F), μ ≠ 0 → ∃ a, lF (μ * a) ≠ 0 := by
    intro μ hμ
    obtain ⟨b, hb⟩ := hlF'
    exact ⟨μ⁻¹ * b, by rwa [mul_inv_cancel_left₀ hμ]⟩
  have hτ₀ : l.comp (utau d₀ (μ₀ : F)) ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hlFμ ((μ₀ : F) ^ 2) (pow_ne_zero 2 hμ₀)
    apply ha
    have := DFunLike.congr_fun h0 (0, a)
    rw [AddMonoidHom.comp_apply, utau_zero_prod, AddMonoidHom.zero_apply] at this
    exact this
  let R : Finset F := (Finset.Ico 1 p).biUnion
    (fun m => Finset.univ.filter (fun μ : F => μ ^ 2 = (m : F) * (μ₀ : F) ^ 2))
  have hR : R.card ≤ 2 * (p - 1) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ m ∈ Finset.Ico 1 p,
          (Finset.univ.filter (fun μ : F => μ ^ 2 = (m : F) * (μ₀ : F) ^ 2)).card
        ≤ ∑ _m ∈ Finset.Ico 1 p, 2 := Finset.sum_le_sum fun m _ => card_filter_sq_le _
      _ = 2 * (p - 1) := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_comm]
  have hprop : ∀ x : (Fin ε → F) × Fˣ, kerTau l x = kerTau l (d₀, μ₀) →
      ∃ k : ZMod p, ∀ y, l (utau x.1 (x.2 : F) y) = k * l (utau d₀ (μ₀ : F) y) := by
    intro x hx
    refine exists_smul_of_ker_eq_addHom (l.comp (utau d₀ (μ₀ : F))) (l.comp (utau x.1 (x.2 : F)))
      hτ₀ fun y => ?_
    have := SetLike.ext_iff.1 hx y
    simpa [kerTau] using this.symm
  have hmem : ∀ x : (Fin ε → F) × Fˣ, kerTau l x = kerTau l (d₀, μ₀) → (x.2 : F) ∈ R := by
    intro x hx
    obtain ⟨k, hk⟩ := hprop x hx
    have h1 : ∀ b : F, lF (((x.2 : F) ^ 2 / (μ₀ : F) ^ 2) * b) = k * lF b := by
      intro b
      have := hk (0, b / (μ₀ : F) ^ 2)
      rw [utau_zero_prod, utau_zero_prod] at this
      have e1 : (x.2 : F) ^ 2 * (b / (μ₀ : F) ^ 2) = ((x.2 : F) ^ 2 / (μ₀ : F) ^ 2) * b := by
        field_simp
      have e2 : (μ₀ : F) ^ 2 * (b / (μ₀ : F) ^ 2) = b := by field_simp
      rw [e2, e1] at this
      exact this
    have h2 := eq_natCast_of_map_mul_eq lF hlF' h1
    have hxne : (x.2 : F) ≠ 0 := x.2.ne_zero
    have h3 : (x.2 : F) ^ 2 = (k.val : F) * (μ₀ : F) ^ 2 := by
      field_simp at h2
      linear_combination h2
    have hk0 : k.val ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_mul] at h3
      exact pow_ne_zero 2 hxne h3
    refine Finset.mem_biUnion.2 ⟨k.val, ?_, ?_⟩
    · exact Finset.mem_Ico.2 ⟨Nat.pos_of_ne_zero hk0, ZMod.val_lt k⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h3⟩
  have hlF_zero : ∀ ξ : F, (∀ r : F, lF (ξ * r) = 0) → ξ = 0 := by
    intro ξ hξ
    by_contra hξ0
    obtain ⟨b, hb⟩ := hlF'
    apply hb
    have := hξ (ξ⁻¹ * b)
    rwa [mul_inv_cancel_left₀ hξ0] at this
  have hlF_def : ∀ a : F, lF a = l (0, a) := fun a => rfl
  have hinj : Set.InjOn (fun x : (Fin ε → F) × Fˣ => (x.2 : F))
      ↑(Finset.univ.filter (fun x : (Fin ε → F) × Fˣ => kerTau l x = kerTau l (d₀, μ₀))) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    obtain ⟨k₁, hk₁⟩ := hprop x hx'
    obtain ⟨k₂, hk₂⟩ := hprop y hy'
    have hxy' : (x.2 : F) = (y.2 : F) := hxy
    have hkk : k₁ = k₂ := by
      obtain ⟨a, ha⟩ := hlFμ ((μ₀ : F) ^ 2) (pow_ne_zero 2 hμ₀)
      have e1 := hk₁ (0, a)
      have e2 := hk₂ (0, a)
      rw [utau_zero_prod, utau_zero_prod, ← hlF_def, ← hlF_def] at e1 e2
      rw [hxy'] at e1
      have e3 : (k₁ - k₂) * lF ((μ₀ : F) ^ 2 * a) = 0 := by
        rw [sub_mul, ← e1, ← e2, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 e3).resolve_right ha)
    subst hkk
    have hsame : ∀ z, l (utau x.1 (x.2 : F) z) = l (utau y.1 (y.2 : F) z) := fun z => by
      rw [hk₁, hk₂]
    have key : ∀ (w : Fin ε → F) (a₁ a₂ : F), l (w, a₁) = l (w, a₂) → lF (a₁ - a₂) = 0 := by
      intro w a₁ a₂ h
      rw [hlF_def]
      have : ((0 : Fin ε → F), a₁ - a₂) = (w, a₁) - (w, a₂) := by
        refine Prod.ext (funext fun j => by simp) (by simp)
      rw [this, map_sub, h]
      exact sub_self _
    have hd : x.1 = y.1 := by
      funext i
      have hξ : (x.2 : F) * (x.1 i - y.1 i) = 0 := by
        refine hlF_zero _ fun r => ?_
        have h1 := hsame (Pi.single i r, 0)
        rw [utau_single, utau_single, ← hxy'] at h1
        have e : (x.2 : F) * (x.1 i - y.1 i) * r =
            (x.2 : F) * (x.1 i * r) - (x.2 : F) * (y.1 i * r) := by ring
        rw [e]
        exact key _ _ _ h1
      exact sub_eq_zero.1 ((mul_eq_zero.1 hξ).resolve_left x.2.ne_zero)
    exact Prod.ext hd (Units.ext hxy')
  calc (Finset.univ.filter (fun x : (Fin ε → F) × Fˣ => kerTau l x = kerTau l (d₀, μ₀))).card
      ≤ R.card := Finset.card_le_card_of_injOn (fun x : (Fin ε → F) × Fˣ => (x.2 : F))
        (fun x hx => hmem x (Finset.mem_filter.1 hx).2) hinj
    _ ≤ 2 * (p - 1) := hR

theorem card_params_le_mul_card_image (l : UP F ε →+ ZMod p) (hl : ∃ a, l (0, a) ≠ 0) :
    Nat.card F ^ ε * (Nat.card F - 1) ≤
      2 * (p - 1) * ((Finset.univ : Finset ((Fin ε → F) × Fˣ)).image (kerTau l)).card := by
  have h := Finset.card_le_mul_card_image (Finset.univ : Finset ((Fin ε → F) × Fˣ))
    (f := kerTau l) (2 * (p - 1)) (fun a ha => by
      obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 ha
      exact card_fiber_le_addHom l hl x₀)
  rwa [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_units, ← Nat.card_eq_fintype_card] at h

end Count

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
