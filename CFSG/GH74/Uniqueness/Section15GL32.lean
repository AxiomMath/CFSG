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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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

namespace CFSG.GH74.Uniqueness.Section15GL32

open Subgroup

abbrev GL32 : Type := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def unitri (a b c : ZMod 2) : Mat3 := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem unitri_mul_inv : ∀ a b c : ZMod 2, unitri a b c * unitri a (a * c + b) c = 1 := by
  decide

theorem unitri_inv_mul : ∀ a b c : ZMod 2, unitri a (a * c + b) c * unitri a b c = 1 := by
  decide

@[expose] def unitriGL (a b c : ZMod 2) : GL32 :=
  ⟨unitri a b c, unitri a (a * c + b) c, unitri_mul_inv a b c, unitri_inv_mul a b c⟩

@[expose] def aG : GL32 := unitriGL 1 0 1

@[expose] def bG : GL32 := unitriGL 0 0 1

theorem aG_pow_four : aG ^ 4 = 1 := by decide

theorem bG_mul_self : bG * bG = 1 := by decide

theorem bG_aG_bG : bG * aG * bG = aG⁻¹ := by decide

theorem bG_aG_sq : (bG * aG) * (bG * aG) = 1 := by decide

@[expose] def fD : DihedralGroup 4 → GL32
  | DihedralGroup.r i => aG ^ i.val
  | DihedralGroup.sr i => bG * aG ^ i.val

theorem fD_injective : Function.Injective fD := by decide

section Lift

variable {E : Type*} [Group E]

theorem pow_val_add {a : E} (ha : a ^ 4 = 1) (i j : ZMod 4) :
    a ^ (i + j).val = a ^ i.val * a ^ j.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ ha]

theorem pow_val_neg {a : E} (ha : a ^ 4 = 1) (i : ZMod 4) : a ^ (-i).val = (a ^ i.val)⁻¹ := by
  have h := pow_val_add ha (-i) i
  rw [neg_add_cancel, ZMod.val_zero, pow_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pow_mul_eq {a b : E} (hb : b * b = 1) (hba : b * a * b = a⁻¹) (k : ℕ) :
    a ^ k * b = b * (a ^ k)⁻¹ := by
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : b * a ^ k * b = (a ^ k)⁻¹ := by
    have := conj_pow (a := b) (b := a) (i := k)
    rw [hb'] at this
    rw [← this, hba, inv_pow]
  calc a ^ k * b = b * (b * a ^ k * b) := by
        calc a ^ k * b = (b * b) * a ^ k * b := by rw [hb, one_mul]
          _ = b * (b * a ^ k * b) := by group
    _ = b * (a ^ k)⁻¹ := by rw [h1]

@[expose] def dihedralLift (a b : E) (ha : a ^ 4 = 1) (hb : b * b = 1) (hba : b * a * b = a⁻¹) :
    DihedralGroup 4 →* E where
  toFun x := match x with
    | DihedralGroup.r i => a ^ i.val
    | DihedralGroup.sr i => b * a ^ i.val
  map_one' := by
    rw [DihedralGroup.one_def]
    simp
  map_mul' x y := by
    rcases x with i | i <;> rcases y with j | j
    · simp only [DihedralGroup.r_mul_r]
      exact pow_val_add ha i j
    · simp only [DihedralGroup.r_mul_sr]
      rw [← mul_assoc, pow_mul_eq hb hba, mul_assoc, ← pow_val_neg ha, ← pow_val_add ha,
        sub_eq_neg_add]
    · simp only [DihedralGroup.sr_mul_r]
      rw [pow_val_add ha, mul_assoc]
    · simp only [DihedralGroup.sr_mul_sr]
      rw [mul_assoc, ← mul_assoc (a ^ i.val), pow_mul_eq hb hba, mul_assoc b, ← mul_assoc b,
        hb, one_mul, ← pow_val_neg ha, ← pow_val_add ha, sub_eq_neg_add]

theorem dihedralLift_r (a b : E) (ha : a ^ 4 = 1) (hb : b * b = 1) (hba : b * a * b = a⁻¹)
    (i : ZMod 4) : dihedralLift a b ha hb hba (DihedralGroup.r i) = a ^ i.val := rfl

theorem dihedralLift_sr (a b : E) (ha : a ^ 4 = 1) (hb : b * b = 1) (hba : b * a * b = a⁻¹)
    (i : ZMod 4) : dihedralLift a b ha hb hba (DihedralGroup.sr i) = b * a ^ i.val := rfl

@[expose] def zetaHom (z : E) (hz : z * z = 1) : Multiplicative (ZMod 2) →* E where
  toFun k := z ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    have hz2 : z ^ 2 = 1 := by rw [sq]; exact hz
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hz2]

end Lift

theorem eq_one_of_pow_two_of_odd {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) (n : ℕ)
    (hn : Odd n) (hgn : g ^ n = 1) : g = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ', pow_mul, hg, one_pow, mul_one] at hgn
  exact hgn

theorem fD_one : fD 1 = 1 := by decide

theorem card_GL32 : Nat.card GL32 = 168 := by
  rw [Matrix.card_GL_field 3, Fin.prod_univ_three]
  simp [ZMod.card]

theorem exists_sq_eq_of_gl32 {E : Type} [Group E] [Finite E] (ρ : E →* GL32)
    (hρ : Function.Surjective ρ) {z : E} (hz1 : z ≠ 1) (hzρ : ρ z = 1)
    (hker : ∀ x, ρ x = 1 → x = 1 ∨ x = z)
    (hgen : ∀ T : E →* Multiplicative (ZMod 2), (∀ y : E, Odd (orderOf y) → T y = 1) →
      ∀ x, T x = 1) :
    ∃ x : E, x * x = z := by
  by_contra hno'
  have hno : ∀ x : E, x * x ≠ z := fun x hx => hno' ⟨x, hx⟩
  have hsq : ∀ x : E, ρ (x * x) = 1 → x * x = 1 := fun x hx => (hker _ hx).resolve_right (hno x)
  have hzz : z * z = 1 := hsq z (by rw [map_mul, hzρ, one_mul])
  have hzc : ∀ g : E, g * z = z * g := by
    intro g
    have h1 : ρ (g * z * g⁻¹) = 1 := by
      rw [map_mul, map_mul, hzρ, mul_one, map_inv, mul_inv_cancel]
    rcases hker _ h1 with h2 | h2
    · exfalso
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    · calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [h2]
  obtain ⟨a₁, ha₁⟩ := hρ aG
  obtain ⟨b₁, hb₁⟩ := hρ bG
  have ha4 : a₁ ^ 4 = 1 := by
    have h := hsq (a₁ ^ 2) (by rw [map_mul, map_pow, ha₁, ← pow_add]; exact aG_pow_four)
    rwa [← pow_add] at h
  have hb2 : b₁ * b₁ = 1 := hsq b₁ (by rw [map_mul, hb₁]; exact bG_mul_self)
  have hbab : b₁ * a₁ * b₁ = a₁⁻¹ := by
    have h := hsq (b₁ * a₁) (by rw [map_mul, map_mul, hb₁, ha₁]; exact bG_aG_sq)
    have h' : b₁ * a₁ * b₁ * a₁ = 1 := by simpa [mul_assoc] using h
    exact mul_eq_one_iff_eq_inv.mp h'
  let θ : DihedralGroup 4 →* E := dihedralLift a₁ b₁ ha4 hb2 hbab
  have hρθ : ∀ x, ρ (θ x) = fD x := by
    intro x
    rcases x with i | i
    · simp [θ, dihedralLift_r, fD, map_pow, ha₁]
    · simp [θ, dihedralLift_sr, fD, map_mul, map_pow, ha₁, hb₁]
  have hθinj : Function.Injective θ := by
    intro x y hxy
    apply fD_injective
    rw [← hρθ, ← hρθ, hxy]
  let ζ : Multiplicative (ZMod 2) →* E := zetaHom z hzz
  have hcomm : ∀ x y, Commute (θ x) (ζ y) := fun x y =>
    Commute.pow_right (show Commute (θ x) z from hzc (θ x)) _
  let Θ : DihedralGroup 4 × Multiplicative (ZMod 2) →* E := θ.noncommCoprod ζ hcomm
  have hΘ : ∀ p, Θ p = θ p.1 * ζ p.2 := fun p => rfl
  have hρζ : ∀ k, ρ (ζ k) = 1 := fun k => by simp [ζ, zetaHom, map_pow, hzρ]
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, k⟩ h
    have h1 : θ d * ζ k = 1 := h
    have h2 : ρ (θ d) = 1 := by
      have := congrArg ρ h1
      rwa [map_mul, hρζ, mul_one, map_one] at this
    have hd : d = 1 := by
      apply fD_injective
      rw [← hρθ, h2, fD_one]
    have hk : ζ k = 1 := by
      rw [hd, map_one, one_mul] at h1
      exact h1
    have hk0 : (Multiplicative.toAdd k).val = 0 := by
      by_contra hne
      have hlt := ZMod.val_lt (Multiplicative.toAdd k)
      have h1' : (Multiplicative.toAdd k).val = 1 := by omega
      have : z ^ (Multiplicative.toAdd k).val = 1 := hk
      rw [h1', pow_one] at this
      exact hz1 this
    have hk' : Multiplicative.toAdd k = 0 := (ZMod.val_eq_zero _).mp hk0
    rw [hd]
    refine Prod.ext rfl ?_
    exact toAdd_eq_zero.mp hk'
  let H : Subgroup E := Θ.range
  have hcardH : Nat.card H = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΘinj).toEquiv, Nat.card_prod,
      DihedralGroup.nat_card]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h2]
  have hk : Nat.card ρ.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, ρ.ker.one_mem⟩, ⟨z, hzρ⟩, ?_, ?_⟩
    · intro h
      exact hz1 (congrArg Subtype.val h).symm
    · ext ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases hker x hx with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
  have hcardE : Nat.card E = 336 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv, card_GL32,
      hk] at h1
    omega
  have hindex : H.index = 21 := by
    have h1 := Subgroup.card_mul_index H
    rw [hcardH, hcardE] at h1
    omega
  have hzH : z ∈ H := by
    refine ⟨(1, Multiplicative.ofAdd 1), ?_⟩
    rw [hΘ]
    change θ 1 * z ^ ((1 : ZMod 2).val) = z
    rw [map_one, one_mul]
    have h1 : (1 : ZMod 2).val = 1 := rfl
    rw [h1, pow_one]
  let ϕ : H →* Multiplicative (ZMod 2) :=
    (MonoidHom.snd _ _).comp (MonoidHom.ofInjective hΘinj).symm.toMonoidHom
  have hϕz : ϕ ⟨z, hzH⟩ = Multiplicative.ofAdd 1 := by
    have h1 : (MonoidHom.ofInjective hΘinj).symm ⟨z, hzH⟩ = (1, Multiplicative.ofAdd 1) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change z = Θ (1, Multiplicative.ofAdd 1)
      rw [hΘ]
      change z = θ 1 * z ^ ((1 : ZMod 2).val)
      rw [map_one, one_mul]
      have h2 : (1 : ZMod 2).val = 1 := rfl
      rw [h2, pow_one]
    change (MonoidHom.snd _ _) ((MonoidHom.ofInjective hΘinj).symm ⟨z, hzH⟩) = _
    rw [h1]
    rfl
  have hfi : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let T : E →* Multiplicative (ZMod 2) := MonoidHom.transfer ϕ
  have hexp : ∀ w : Multiplicative (ZMod 2), w ^ 2 = 1 := by decide
  have hT : ∀ y : E, Odd (orderOf y) → T y = 1 := by
    intro y hy
    refine eq_one_of_pow_two_of_odd (T y) (hexp _) (orderOf y) hy ?_
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hTz : T z = 1 := hgen T hT z
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k * g₀ = g₀ * z ^ k :=
      ((Commute.pow_right (show Commute g₀ z from hzc g₀) k).eq).symm
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by rw [mul_assoc]
      _ = z ^ k := by rw [hc]; group
  have hTz' := MonoidHom.transfer_eq_pow ϕ z hkey
  have hz2 : z ^ 2 = 1 := by rw [sq]; exact hzz
  have hz21 : z ^ H.index = z := by
    rw [hindex, show (21 : ℕ) = 2 * 10 + 1 from rfl, pow_succ, pow_mul, hz2, one_pow, one_mul]
  have hfin : ϕ ⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ = ϕ ⟨z, hzH⟩ :=
    congrArg ϕ (Subtype.ext hz21)
  have hTz'' : T z = ϕ ⟨z, hzH⟩ := hTz'.trans hfin
  have hcontra : Multiplicative.ofAdd (1 : ZMod 2) = 1 :=
    hϕz.symm.trans (hTz''.symm.trans hTz)
  exact absurd hcontra (by decide)

end CFSG.GH74.Uniqueness.Section15GL32
