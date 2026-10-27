module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterGF64
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.AGLEmbedding.ChevOuter.GF64

open CFSG.Quasithin

noncomputable section

instance : Algebra (ZMod 2) GF64 := ZMod.algebra GF64 2

instance : Fintype GF64 := Fintype.ofFinite _

theorem finrank_eq : Module.finrank (ZMod 2) GF64 = 6 := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := GF64)
  rw [← Nat.card_eq_fintype_card (α := GF64), card_eq, ZMod.card] at h
  have : (2 : ℕ) ^ 6 = 2 ^ Module.finrank (ZMod 2) GF64 := by
    rw [← h]
    norm_num
  exact (Nat.pow_right_injective le_rfl this).symm

instance : Algebra.IsAlgebraic (ZMod 2) GF64 := Algebra.IsAlgebraic.of_finite _ _

@[expose] def frobQ : GF64 ≃ₐ[ZMod 2] GF64 :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) GF64

theorem frobQ_apply (x : GF64) : frobQ x = x ^ 2 := by
  show (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) GF64) x = x ^ 2
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]

theorem orderOf_frobQ : orderOf frobQ = 6 := by
  rw [frobQ, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, finrank_eq]

@[expose] def toRE : (GF64 ≃ₐ[ZMod 2] GF64) →* (GF64 ≃+* GF64) where
  toFun τ := τ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toRE_injective : Function.Injective toRE :=
  fun _ _ h => AlgEquiv.ext fun x => congrArg (fun r : GF64 ≃+* GF64 => r x) h

theorem exists_toRE_eq (σ : GF64 ≃+* GF64) : ∃ τ : GF64 ≃ₐ[ZMod 2] GF64, toRE τ = σ := by
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), rfl⟩
  have : (σ : GF64 →+* GF64).comp (algebraMap (ZMod 2) GF64) = algebraMap (ZMod 2) GF64 :=
    RingHom.ext_zmod _ _
  exact congrArg (fun r : ZMod 2 →+* GF64 => r x) this

theorem toRE_frobQ_sq : toRE (frobQ ^ 2) = sigma2Equiv := by
  refine RingEquiv.ext fun x => ?_
  show frobQ (frobQ x) = sigma2 x
  rw [frobQ_apply, frobQ_apply, ← pow_mul, sigma2_eq_pow]

theorem sigma2Equiv_cube : sigma2Equiv ^ 3 = 1 := by
  refine RingEquiv.ext fun x => ?_
  show sigma2Equiv (sigma2Equiv (sigma2Equiv x)) = x
  exact sigma2_cube x

theorem eq_sigma2_or_inv_of_orderOf_eq_three (σ : GF64 ≃+* GF64) (hσ : orderOf σ = 3) :
    σ = sigma2Equiv ∨ σ = sigma2Equiv⁻¹ := by
  obtain ⟨τ, rfl⟩ := exists_toRE_eq σ
  have hτ : orderOf τ = 3 := by
    rw [← orderOf_injective toRE toRE_injective τ]
    exact hσ
  obtain ⟨⟨n, hn⟩, hnτ⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod 2) GF64).2 τ
  rw [finrank_eq] at hn
  have e : frobQ ^ n = τ := hnτ
  have hF : orderOf (frobQ ^ n) = 3 := by
    rw [e]
    exact hτ
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hF
  rw [orderOf_pow' _ hn0, orderOf_frobQ] at hF
  have h24 : n = 2 ∨ n = 4 := by
    interval_cases n <;> simp at hF ⊢
  rcases h24 with rfl | rfl
  · left
    rw [← e, toRE_frobQ_sq]
  · right
    have : frobQ ^ 4 = (frobQ ^ 2) ^ 2 := by rw [← pow_mul]
    rw [← e, this, map_pow, toRE_frobQ_sq]
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ']
    exact sigma2Equiv_cube

end

end CFSG.AGLEmbedding.ChevOuter.GF64
