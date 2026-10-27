module

public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Tactic.Group
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.Triality

variable {K : Type*} [Field K] [Finite K]

def subHom (σ : K ≃+* K) : K →+ K where
  toFun c := σ c - c
  map_zero' := by simp
  map_add' x y := by simp; ring

theorem subHom_apply (σ : K ≃+* K) (c : K) : subHom σ c = σ c - c := by simp [subHom]

def traceHom (σ : K ≃+* K) : K →+ K where
  toFun x := x + σ x + σ (σ x)
  map_zero' := by simp
  map_add' x y := by simp; ring

theorem exists_traceHom_ne_zero (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ x : K, traceHom σ x ≠ 0 := by
  by_contra hall
  have hall' : ∀ x : K, traceHom σ x = 0 := fun x => by
    by_contra h
    exact hall ⟨x, h⟩
  have hσ2 : σ ^ 2 ≠ 1 := by
    intro h
    apply hσ1
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ3, h]; simp
  have h12 : σ ≠ σ ^ 2 := fun h =>
    hσ1 (mul_left_cancel (a := σ) (by rw [mul_one, ← pow_two]; exact h.symm))
  let g : Fin 3 → (Kˣ →* K) := fun i =>
    (((σ ^ (i : ℕ) : K ≃+* K) : K →+* K) : K →* K).comp (Units.coeHom K)
  have hgi : Function.Injective g := by
    intro i j hij
    have hfun : ∀ x : K, (σ ^ (i : ℕ)) x = (σ ^ (j : ℕ)) x := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · have := congrArg (fun m : Kˣ →* K => m (Units.mk0 x hx)) hij
        simpa [g] using this
    have hσij : σ ^ (i : ℕ) = σ ^ (j : ℕ) := RingEquiv.ext hfun
    fin_cases i <;> fin_cases j <;> simp at hσij ⊢ <;>
      first
      | exact hσ1 (by simpa using hσij.symm)
      | exact hσ1 hσij
      | exact hσ2 hσij
      | exact hσ2 hσij.symm
      | exact hσ1 (by simpa using hσij)
      | exact h12 hσij
      | exact h12 hσij.symm
  have hli := (linearIndependent_monoidHom Kˣ K).comp g hgi
  have hz := Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by
    funext u
    have := hall' (u : K)
    simp only [traceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    simpa [g, Fin.sum_univ_three, pow_succ] using this) 0
  exact one_ne_zero hz

theorem exists_sub_of_trace_eq_zero (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hK : Nat.card K = Nat.card {c : K // σ c = c} ^ 3) (a : K)
    (ha : a + σ a + σ (σ a) = 0) : ∃ c : K, a = σ c - c := by
  classical
  set q := Nat.card {c : K // σ c = c} with hq
  have hσ3c : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := congrArg (fun e : K ≃+* K => e c) hσ3
    simpa [pow_succ] using this
  have hqpos : 0 < q := by
    have : Nonempty {c : K // σ c = c} := ⟨⟨0, map_zero σ⟩⟩
    exact Nat.card_pos
  have hker : Nat.card (subHom σ).ker = q :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      simp [subHom, AddMonoidHom.mem_ker, sub_eq_zero])
  have hrange : Nat.card (subHom σ).range = q ^ 2 := by
    have h := AddSubgroup.card_ker_mul_card_range (subHom σ)
    rw [hker, hK] at h
    have : q * Nat.card (subHom σ).range = q * q ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hqpos this
  obtain ⟨x₀, hx₀⟩ := exists_traceHom_ne_zero σ hσ3 hσ1
  set t := traceHom σ x₀ with ht
  have hrangeT : q ≤ Nat.card (traceHom σ).range := by
    refine Nat.card_le_card_of_injective
      (fun c : {c : K // σ c = c} => (⟨c.1 * t, ⟨c.1 * x₀, ?_⟩⟩ : (traceHom σ).range)) ?_
    · simp only [traceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, c.2, ht]
      ring
    · intro c c' h
      have h' : c.1 * t = c'.1 * t := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel₀ hx₀ h')
  have hkerT : Nat.card (traceHom σ).ker ≤ q ^ 2 := by
    have h := AddSubgroup.card_ker_mul_card_range (traceHom σ)
    rw [hK] at h
    have : Nat.card (traceHom σ).ker * q ≤ q ^ 2 * q := by
      calc Nat.card (traceHom σ).ker * q ≤ Nat.card (traceHom σ).ker * Nat.card (traceHom σ).range :=
            Nat.mul_le_mul le_rfl hrangeT
        _ = q ^ 2 * q := by rw [h]; ring
    exact Nat.le_of_mul_le_mul_right this hqpos
  have hle : (subHom σ).range ≤ (traceHom σ).ker := by
    rintro _ ⟨c, rfl⟩
    rw [AddMonoidHom.mem_ker]
    simp only [subHom, traceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sub]
    rw [hσ3c c]
    ring
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (by rw [hrange]; exact hkerT)
  have ha' : a ∈ (traceHom σ).ker := by
    rw [AddMonoidHom.mem_ker]
    exact ha
  rw [← heq] at ha'
  obtain ⟨c, hc⟩ := ha'
  exact ⟨c, hc.symm⟩

end CFSG.HardMathSupport.Lang.Triality
