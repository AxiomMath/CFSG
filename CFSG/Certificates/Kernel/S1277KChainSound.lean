module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.S1277Chain

variable {Γ : Type} [Group Γ] {α : Type} [MulAction Γ α]

theorem card_eq_mul_stab [Finite Γ] (A : Subgroup Γ) (x : α) (C : Finset α)
    (h1 : ∀ g ∈ A, g • x ∈ C) (h2 : ∀ c ∈ C, ∃ g ∈ A, g • x = c) :
    Nat.card A = C.card * Nat.card ↥(A ⊓ MulAction.stabilizer Γ x) := by
  classical
  have h2' : ∀ c : C, ∃ g, g ∈ A ∧ g • x = c.1 := fun c => h2 c.1 c.2
  choose t htA htx using h2'
  have hmem : ∀ g (hg : g ∈ A), (t ⟨g • x, h1 g hg⟩)⁻¹ * g ∈ A ⊓ MulAction.stabilizer Γ x := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨A.mul_mem (A.inv_mem (htA _)) hg, ?_⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, htx]
  let f : A → C × ↥(A ⊓ MulAction.stabilizer Γ x) := fun g =>
    (⟨g.1 • x, h1 g.1 g.2⟩, ⟨(t ⟨g.1 • x, h1 g.1 g.2⟩)⁻¹ * g.1, hmem g.1 g.2⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      have h1' := congrArg Prod.fst h
      have h2'' := congrArg (fun p => (p.2 : Γ)) h
      simp only [f] at h1' h2''
      rw [h1'] at h2''
      exact Subtype.ext (mul_left_cancel h2'')
    · rintro ⟨c, β⟩
      have hβA : (β : Γ) ∈ A := β.2.1
      have hβx : (β : Γ) • x = x := β.2.2
      have hg : t c * β ∈ A := A.mul_mem (htA c) hβA
      have hc : (⟨(t c * β) • x, h1 _ hg⟩ : C) = c := by
        apply Subtype.ext
        change (t c * β) • x = c.1
        rw [mul_smul, hβx, htx]
      refine ⟨⟨t c * β, hg⟩, ?_⟩
      refine Prod.ext hc (Subtype.ext ?_)
      change (t ⟨(t c * β) • x, h1 _ hg⟩)⁻¹ * (t c * β) = β
      rw [hc, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_eq_fintype_card (α := C),
    Fintype.card_coe]

theorem card_eq_mul_stab' [Finite Γ] {β : Type} (A : Subgroup Γ) (x : α) (f : α → β)
    (hf : Function.Injective f) (C : Finset β) (h1 : ∀ g ∈ A, f (g • x) ∈ C)
    (h2 : ∀ c ∈ C, ∃ g ∈ A, f (g • x) = c) :
    Nat.card A = C.card * Nat.card ↥(A ⊓ MulAction.stabilizer Γ x) := by
  classical
  have e := card_eq_mul_stab A x (C.preimage f hf.injOn) (fun g hg => by
    rw [Finset.mem_preimage]; exact h1 g hg) (fun c hc => by
      rw [Finset.mem_preimage] at hc
      obtain ⟨g, hg, hgc⟩ := h2 _ hc
      exact ⟨g, hg, hf hgc⟩)
  rw [e]
  congr 1
  refine Finset.card_bij (fun a _ => f a) (fun a ha => Finset.mem_preimage.1 ha)
    (fun a _ b _ h => hf h) (fun c hc => ?_)
  obtain ⟨g, hg, hgc⟩ := h2 c hc
  exact ⟨g • x, Finset.mem_preimage.2 (hgc ▸ hc), hgc⟩

def Chain : Subgroup Γ → List α → List (Finset α) → Prop
  | A, x :: b, C :: Cs => (∀ g ∈ A, g • x ∈ C) ∧ (∀ c ∈ C, ∃ g ∈ A, g • x = c) ∧
      Chain (A ⊓ MulAction.stabilizer Γ x) b Cs
  | _, [], [] => True
  | _, _, _ => False

theorem card_chain [Finite Γ] :
    ∀ (b : List α) (Cs : List (Finset α)) (A : Subgroup Γ), Chain A b Cs →
      (∀ g ∈ A, (∀ a ∈ b, g • a = a) → g = 1) → Nat.card A = (Cs.map Finset.card).prod
  | [], [], A, _, htriv => by
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 fun g hg => htriv g hg (by simp)
    rw [this, Subgroup.card_bot]
    rfl
  | x :: b, C :: Cs, A, ⟨h1, h2, hc⟩, htriv => by
    rw [card_eq_mul_stab A x C h1 h2, List.map_cons, List.prod_cons,
      card_chain b Cs _ hc fun g hg hb => htriv g hg.1 fun a ha => ?_]
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hg.2
    · exact hb a ha
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

end CFSG.KS.S1277Chain

end
