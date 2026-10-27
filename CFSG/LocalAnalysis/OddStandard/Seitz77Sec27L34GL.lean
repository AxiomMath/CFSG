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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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

namespace CFSG.OddStandard.Seitz77

open Matrix Subgroup

theorem card_GL_four_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field 4, ZMod.card, Fin.prod_univ_four]
  norm_num

namespace HelperE

theorem val_mul_mulVec {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    (a b : GL n R) (v : n → R) :
    (↑(a * b) : Matrix n n R) *ᵥ v = (↑a : Matrix n n R) *ᵥ ((↑b : Matrix n n R) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem val_inv_mulVec_val_mulVec {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    (a : GL n R) (v : n → R) :
    (↑a⁻¹ : Matrix n n R) *ᵥ ((↑a : Matrix n n R) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem val_mulVec_val_inv_mulVec {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    (a : GL n R) (v : n → R) :
    (↑a : Matrix n n R) *ᵥ ((↑a⁻¹ : Matrix n n R) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

def fixCount (g : GL (Fin 4) (ZMod 2)) : ℕ :=
  Fintype.card {v : Fin 4 → ZMod 2 // (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = v}

theorem fixCount_conj (g h : GL (Fin 4) (ZMod 2)) : fixCount (h * g * h⁻¹) = fixCount g := by
  unfold fixCount
  refine Fintype.card_congr
    { toFun := fun v => ⟨(↑h⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1, ?_⟩
      invFun := fun v => ⟨(↑h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1, ?_⟩
      left_inv := fun v => Subtype.ext (val_mulVec_val_inv_mulVec h v.1)
      right_inv := fun v => Subtype.ext (val_inv_mulVec_val_mulVec h v.1) }
  · have hv := v.2
    rw [val_mul_mulVec, val_mul_mulVec] at hv
    calc (↑g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ((↑h⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1)
        = (↑h⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ((↑h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
            ((↑g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
              ((↑h⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1))) :=
          (val_inv_mulVec_val_mulVec h _).symm
      _ = (↑h⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1 := by rw [hv]
  · have hv := v.2
    rw [val_mul_mulVec, val_inv_mulVec_val_mulVec, val_mul_mulVec, hv]

def M₁ : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def M₂ : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

theorem M₁_mul_self : M₁ * M₁ = 1 := by decide

theorem M₂_mul_self : M₂ * M₂ = 1 := by decide

def g₁ : GL (Fin 4) (ZMod 2) := ⟨M₁, M₁, M₁_mul_self, M₁_mul_self⟩

def g₂ : GL (Fin 4) (ZMod 2) := ⟨M₂, M₂, M₂_mul_self, M₂_mul_self⟩

theorem fixCount_g₁ : fixCount g₁ = 8 := by decide

theorem fixCount_g₂ : fixCount g₂ = 4 := by decide

end HelperE

theorem exists_two_nonconjugate_involutions :
    ∃ g₁ g₂ : GL (Fin 4) (ZMod 2), g₁ * g₁ = 1 ∧ g₂ * g₂ = 1 ∧ g₁ ≠ 1 ∧ g₂ ≠ 1 ∧
      ∀ h : GL (Fin 4) (ZMod 2), h * g₁ * h⁻¹ ≠ g₂ := by
  refine ⟨HelperE.g₁, HelperE.g₂, Units.ext HelperE.M₁_mul_self, Units.ext HelperE.M₂_mul_self,
    ?_, ?_, fun h hh => ?_⟩
  · intro h
    have h' : HelperE.M₁ = 1 := congrArg Units.val h
    revert h'
    decide
  · intro h
    have h' : HelperE.M₂ = 1 := congrArg Units.val h
    revert h'
    decide
  · have hc := HelperE.fixCount_conj HelperE.g₁ h
    rw [hh, HelperE.fixCount_g₂, HelperE.fixCount_g₁] at hc
    exact absurd hc (by norm_num)

theorem no_gl4_quotient {G S : Type} [Group G] [Finite G] [Group S] [Finite S]
    (π : G →* S) (hπ : Function.Surjective π) (hS : IsSimpleGroup S)
    (hSord : Nat.card S = 20160)
    (hinv : ∀ x y : S, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → ∃ g : S, g * x * g⁻¹ = y)
    (hodd : Odd (Nat.card π.ker)) (ψ : G →* GL (Fin 4) (ZMod 2))
    (Xh : Subgroup G) (hXe : Even (Nat.card Xh)) (hXψ : ∀ x ∈ Xh, ψ x = 1 → x = 1) : False := by
  have hψker : ψ.ker.Normal := MonoidHom.normal_ker ψ
  have hmapN : (ψ.ker.map π).Normal := Subgroup.Normal.map hψker π hπ
  rcases hS.eq_bot_or_eq_top_of_normal (ψ.ker.map π) with hbot | htop
  · have hle : ψ.ker ≤ π.ker := by
      intro c hc
      rw [MonoidHom.mem_ker]
      have : π c ∈ ψ.ker.map π := ⟨c, hc, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card G :=
      Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card π.ker * Nat.card S = Nat.card G :=
      Subgroup.card_ker_mul_card_of_surjective hπ
    have h3 : Nat.card ψ.range ≤ 20160 := by
      rw [← card_GL_four_two]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have h4 : Nat.card ψ.ker ≤ Nat.card π.ker := Subgroup.card_le_of_le hle
    have hpos1 : 0 < Nat.card ψ.ker := Nat.card_pos
    have hpos2 : 0 < Nat.card ψ.range := Nat.card_pos
    have hpos3 : 0 < Nat.card π.ker := Nat.card_pos
    rw [hSord] at h2
    have hker : Nat.card ψ.ker = Nat.card π.ker := by
      by_contra hne
      have hlt : Nat.card ψ.ker < Nat.card π.ker := lt_of_le_of_ne h4 hne
      have : Nat.card ψ.ker * Nat.card ψ.range < Nat.card π.ker * 20160 :=
        calc Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card ψ.ker * 20160 :=
              Nat.mul_le_mul_left _ h3
          _ < Nat.card π.ker * 20160 := Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
      omega
    have hrange : Nat.card ψ.range = 20160 := by
      rw [hker] at h1
      have := h1.trans h2.symm
      exact Nat.eq_of_mul_eq_mul_left hpos3 this
    have hkereq : ψ.ker = π.ker := Subgroup.eq_of_le_of_card_ge hle hker.ge
    have hrtop : ψ.range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hrange, card_GL_four_two])
    have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.1 hrtop
    obtain ⟨g₁, g₂, hg₁, hg₂, hne₁, hne₂, hnc⟩ := exists_two_nonconjugate_involutions
    obtain ⟨k₁, hk₁⟩ := hsurj g₁
    obtain ⟨k₂, hk₂⟩ := hsurj g₂
    have hsq : ∀ (k : G) (g : GL (Fin 4) (ZMod 2)), ψ k = g → g * g = 1 → π k * π k = 1 := by
      intro k g hk hg
      have : k * k ∈ π.ker := by
        rw [← hkereq, MonoidHom.mem_ker, map_mul, hk, hg]
      rw [← map_mul]
      exact this
    have hne : ∀ (k : G) (g : GL (Fin 4) (ZMod 2)), ψ k = g → g ≠ 1 → π k ≠ 1 := by
      intro k g hk hg h
      apply hg
      rw [← hk]
      have : k ∈ ψ.ker := by rw [hkereq]; exact h
      exact this
    obtain ⟨σ, hσ⟩ := hinv (π k₁) (π k₂) (hsq k₁ g₁ hk₁ hg₁) (hsq k₂ g₂ hk₂ hg₂)
      (hne k₁ g₁ hk₁ hne₁) (hne k₂ g₂ hk₂ hne₂)
    obtain ⟨κ, hκ⟩ := hπ σ
    have hconj : (κ * k₁ * κ⁻¹)⁻¹ * k₂ ∈ ψ.ker := by
      rw [hkereq, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hκ, hσ]
      group
    rw [MonoidHom.mem_ker] at hconj
    apply hnc (ψ κ)
    simp only [map_mul, map_inv, hk₁, hk₂] at hconj
    rw [inv_mul_eq_one] at hconj
    exact hconj
  · exfalso
    have hrange : ∀ g : G, ∃ r ∈ π.ker, ψ g = ψ r := by
      intro g
      have hg : π g ∈ ψ.ker.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hcg⟩ := hg
      refine ⟨c⁻¹ * g, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
      · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hc, inv_one, one_mul]
    let f : π.ker →* ψ.range := ψ.rangeRestrict.comp π.ker.subtype
    have hfsurj : Function.Surjective f := by
      rintro ⟨x, g, rfl⟩
      obtain ⟨r, hr, hgr⟩ := hrange g
      exact ⟨⟨r, hr⟩, Subtype.ext (by simp [f, hgr])⟩
    have hdvd : Nat.card ψ.range ∣ Nat.card π.ker := Subgroup.card_dvd_of_surjective hfsurj
    let e : Xh →* ψ.range := ψ.rangeRestrict.comp Xh.subtype
    have heinj : Function.Injective e := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ψ x = 1 := by
        have := congrArg Subtype.val hx
        simpa [e] using this
      exact Subtype.ext (hXψ x x.2 h1)
    have hdvd2 : Nat.card Xh ∣ Nat.card ψ.range := Subgroup.card_dvd_of_injective e heinj
    have hoddr : Odd (Nat.card ψ.range) := Odd.of_dvd_nat hodd hdvd
    have hoddX : Odd (Nat.card Xh) := Odd.of_dvd_nat hoddr hdvd2
    exact (Nat.not_even_iff_odd.2 hoddX) hXe

end CFSG.OddStandard.Seitz77
