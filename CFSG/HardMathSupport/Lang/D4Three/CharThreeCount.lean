module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.CharP.Defs

public section

namespace CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] {I : Type}

@[expose] def monoTauAdd (r : I → I) (f : I → K) (σ : K ≃+* K) : (I → K) →+ (I → K) where
  toFun a j := f j * σ (a (r j))
  map_zero' := by funext j; simp
  map_add' a b := by funext j; simp [mul_add]

theorem monoTauAdd_apply (r : I → I) (f : I → K) (σ : K ≃+* K) (a : I → K) (j : I) :
    monoTauAdd r f σ a j = f j * σ (a (r j)) := rfl

@[expose] def monoN (r : I → I) (f : I → K) (σ : K ≃+* K) : (I → K) →+ (I → K) :=
  AddMonoidHom.id _ + monoTauAdd r f σ + (monoTauAdd r f σ).comp (monoTauAdd r f σ)

theorem monoN_apply (r : I → I) (f : I → K) (σ : K ≃+* K) (a : I → K) (j : I) :
    monoN r f σ a j = a j + f j * σ (a (r j)) + f j * σ (f (r j) * σ (a (r (r j)))) := rfl

theorem card_ker_mul_three_le [Finite K] [CharP K 3] [Finite I] (N : (I → K) →+ (I → K)) (j₀ : I)
    (hN : ∃ a, N a j₀ ≠ 0) :
    Nat.card {a : I → K // N a = 0} * 3 ≤ Nat.card K ^ Nat.card I := by
  classical
  let ψ : (I → K) →+ K := (Pi.evalAddMonoidHom (fun _ : I => K) j₀).comp N
  have hker : Nat.card {a : I → K // N a = 0} ≤ Nat.card ψ.ker := by
    refine Nat.card_le_card_of_injective (fun a => ⟨a.1, ?_⟩) ?_
    · change ψ a.1 = 0
      simp [ψ, a.2]
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext this
  have hmul := AddSubgroup.card_ker_mul_card_range ψ
  rw [Nat.card_fun] at hmul
  have hrange : 3 ≤ Nat.card ψ.range := by
    obtain ⟨a, ha⟩ := hN
    have hx : ψ a ≠ 0 := by simpa [ψ] using ha
    have h2 : (2 : K) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff K 3] at this
      omega
    have hxx : ψ a + ψ a ≠ 0 := by
      intro h
      apply hx
      have : (2 : K) * ψ a = 0 := by rw [two_mul]; exact h
      exact (mul_eq_zero.1 this).resolve_left h2
    have hxx' : ψ a + ψ a ≠ ψ a := by
      intro h
      apply hx
      simpa using h
    have : Finite ψ.range := inferInstance
    have hcard : ({(0 : ψ.range), ⟨ψ a, ⟨a, rfl⟩⟩, ⟨ψ a + ψ a, ⟨a + a, by simp⟩⟩} : Finset ψ.range).card
        = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h
        apply hxx'
        simpa using congrArg Subtype.val h
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hx ?_, fun h => hxx ?_⟩
        · simpa using (congrArg Subtype.val h).symm
        · simpa using (congrArg Subtype.val h).symm
    have hfin := Fintype.ofFinite ψ.range
    calc 3 = _ := hcard.symm
      _ ≤ Fintype.card ψ.range := Finset.card_le_univ _
      _ = Nat.card ψ.range := (Nat.card_eq_fintype_card).symm
  calc Nat.card {a : I → K // N a = 0} * 3 ≤ Nat.card ψ.ker * Nat.card ψ.range :=
        Nat.mul_le_mul hker hrange
    _ = Nat.card K ^ Nat.card I := hmul

theorem monoN_coord_ne_zero_of_cycle (r : I → I) (f : I → K) (σ : K ≃+* K) [DecidableEq I]
    {j₀ : I} (h1 : r j₀ ≠ j₀) (h2 : r (r j₀) ≠ j₀) :
    ∃ a, monoN r f σ a j₀ ≠ 0 := by
  refine ⟨Pi.single j₀ 1, ?_⟩
  rw [monoN_apply, Pi.single_eq_same, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  simp

theorem monoN_coord_ne_zero_of_fixed (r : I → I) (f : I → K) (σ : K ≃+* K) {j₀ : I}
    (hr : r j₀ = j₀) (hσ1 : σ ≠ 1) :
    ∃ a, monoN r f σ a j₀ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hform : ∀ x : K, x + f j₀ * σ x + f j₀ * σ (f j₀) * σ (σ x) = 0 := by
    intro x
    have := hcon (fun _ => x)
    simp only [monoN_apply, hr] at this
    simpa [mul_assoc, map_mul] using this
  have h01 : ¬ ∀ x : K, σ x = x := fun h => hσ1 (by ext x; exact h x)
  by_cases hσ2 : ∀ x : K, σ (σ x) = x
  ·
    let g : Fin 2 → (K →* K) := ![(RingHom.id K : K →* K), (σ : K →+* K).toMonoidHom]
    have hginj : Function.Injective g := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        apply h01
        intro x
        have := congrArg (fun m : K →* K => m x) hij
        simpa [g] using this.symm
      · exfalso
        apply h01
        intro x
        have := congrArg (fun m : K →* K => m x) hij
        simpa [g] using this
      · rfl
    have hli := (linearIndependent_monoidHom K K).comp g hginj
    rw [Fintype.linearIndependent_iff] at hli
    have h1 := hli ![1 + f j₀ * σ (f j₀), f j₀] (by
      funext x
      simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply]
      have := hform x
      rw [hσ2 x] at this
      simp only [g]
      simp
      linear_combination this)
    have h1a := h1 0
    have h1b := h1 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1a h1b
    rw [h1b] at h1a
    simp at h1a
  ·
    push Not at hσ2
    let g : Fin 3 → (K →* K) := ![(RingHom.id K : K →* K), (σ : K →+* K).toMonoidHom,
      ((σ * σ : K ≃+* K) : K →+* K).toMonoidHom]
    have hsq : ∀ x : K, (σ * σ) x = σ (σ x) := fun x => rfl
    have h02 : g 0 ≠ g 2 := fun h => by
      obtain ⟨x, hx⟩ := hσ2
      have := congrArg (fun m : K →* K => m x) h
      apply hx
      simpa [g, hsq] using this.symm
    have h01' : g 0 ≠ g 1 := fun h => h01 (fun x => by
      have := congrArg (fun m : K →* K => m x) h
      simpa [g] using this.symm)
    have h12 : g 1 ≠ g 2 := fun h => h01 (fun x => by
      have := congrArg (fun m : K →* K => m x) h
      have h' : σ x = σ (σ x) := by simpa [g, hsq] using this
      have := σ.injective h'
      exact this.symm)
    have hginj : Function.Injective g := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij h01'
      · exact absurd hij h02
      · exact absurd hij.symm h01'
      · rfl
      · exact absurd hij h12
      · exact absurd hij.symm h02
      · exact absurd hij.symm h12
      · rfl
    have hli := (linearIndependent_monoidHom K K).comp g hginj
    rw [Fintype.linearIndependent_iff] at hli
    have := hli ![1, f j₀, f j₀ * σ (f j₀)] (by
      funext x
      simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply]
      have := hform x
      simpa [g, hsq] using this) 0
    simp at this

end CFSG.HardMathSupport.Lang.D4Three
