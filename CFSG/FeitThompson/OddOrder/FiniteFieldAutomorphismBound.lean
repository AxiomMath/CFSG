module

public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import CFSG.FeitThompson.Foundations.PolynomialRootCountDegree
public import CFSG.FeitThompson.Foundations.FiniteFieldUnitsCyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Polynomial

variable {F : Type*} [Field F] {p d : ℕ}

theorem finrank_eq_of_card_eq_pow (hp : p.Prime) (k : Subfield F)
    (hF : Nat.card F = p ^ d) (hk : Nat.card k = p) :
    Module.finrank k F = d := by
  have hFin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hp.pos.ne')
  have h := Module.natCard_eq_pow_finrank (K := k) (V := F)
  rw [hF, hk] at h
  exact (Nat.pow_right_injective hp.two_le h).symm

theorem finite_ringEquiv_of_finite (R : Type*) [Ring R] [Finite R] : Finite (R ≃+* R) :=
  Finite.of_injective (fun σ : R ≃+* R => (σ : R → R)) fun _ _ h => RingEquiv.ext (congrFun h)

def ringEquivFixingEquivAlgEquiv (k : Subfield F) :
    {σ : F ≃+* F // ∀ x ∈ k, σ x = x} ≃ (F ≃ₐ[k] F) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.1) (fun x => σ.2 x x.2)
  invFun e := ⟨e.toRingEquiv, fun x hx => e.commutes ⟨x, hx⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_algEquiv_eq_ncard (k : Subfield F) :
    Nat.card (F ≃ₐ[k] F) = {σ : F ≃+* F | ∀ x ∈ k, σ x = x}.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (ringEquivFixingEquivAlgEquiv k)).symm

theorem ncard_setOf_ringEquiv_fixing_le (hp : p.Prime) (k : Subfield F)
    (hF : Nat.card F = p ^ d) (hk : Nat.card k = p) :
    {σ : F ≃+* F | ∀ x ∈ k, σ x = x}.ncard ≤ d := by
  have hFin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hp.pos.ne')
  have hrank : Module.finrank k F = d := finrank_eq_of_card_eq_pow hp k hF hk
  obtain ⟨t, -, htgen⟩ := exists_ne_zero_forall_exists_pow_eq F
  have hint : IsIntegral k t := IsIntegral.of_finite k t
  set f := minpoly k t
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hfd : f.natDegree ≤ d := hrank ▸ minpoly.natDegree_le t
  set g : F[X] := f.map (algebraMap k F) with hgdef
  have hg0 : g ≠ 0 := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective k F)).2 hf0
  have hgd : g.natDegree = f.natDegree := Polynomial.natDegree_map _
  have hroot : ∀ σ ∈ {σ : F ≃+* F | ∀ x ∈ k, σ x = x}, g.eval (σ t) = 0 := by
    intro σ hσ
    have hσalg : ∀ x : k, σ (algebraMap k F x) = algebraMap k F x := fun x => hσ x x.2
    let e : F ≃ₐ[k] F := AlgEquiv.ofRingEquiv hσalg
    have h2 : aeval (σ t) f = 0 := by
      have he : e t = σ t := rfl
      rw [← he, Polynomial.aeval_algHom_apply e t f, minpoly.aeval, map_zero]
    rw [hgdef, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact h2
  have hinj : Set.InjOn (fun σ : F ≃+* F => σ t) {σ : F ≃+* F | ∀ x ∈ k, σ x = x} := by
    intro σ _ τ _ h
    refine RingEquiv.ext fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · obtain ⟨n, hn⟩ := htgen x hx
      subst hn
      simp only [map_pow]
      rw [show σ t = τ t from h]
  calc {σ : F ≃+* F | ∀ x ∈ k, σ x = x}.ncard
      ≤ {a : F | g.eval a = 0}.ncard :=
        Set.ncard_le_ncard_of_injOn _ hroot hinj (finite_setOf_eval_eq_zero hg0)
    _ ≤ g.natDegree := ncard_setOf_eval_eq_zero_le_natDegree hg0
    _ = f.natDegree := hgd
    _ ≤ d := hfd

theorem natCard_algEquiv_le (hp : p.Prime) (k : Subfield F)
    (hF : Nat.card F = p ^ d) (hk : Nat.card k = p) :
    Nat.card (F ≃ₐ[k] F) ≤ d := by
  rw [natCard_algEquiv_eq_ncard]
  exact ncard_setOf_ringEquiv_fixing_le hp k hF hk

theorem card_le_of_forall_mem_fixing (hp : p.Prime) (k : Subfield F)
    (hF : Nat.card F = p ^ d) (hk : Nat.card k = p) {s : Finset (F ≃+* F)}
    (hs : ∀ σ ∈ s, ∀ x ∈ k, σ x = x) : s.card ≤ d := by
  have hFin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hp.pos.ne')
  have : Finite (F ≃+* F) := finite_ringEquiv_of_finite F
  rw [← Set.ncard_coe_finset]
  exact le_trans (Set.ncard_le_ncard (fun σ hσ => hs σ (by simpa using hσ))
    (Set.toFinite _)) (ncard_setOf_ringEquiv_fixing_le hp k hF hk)

end

end CFSG.FeitThompson
