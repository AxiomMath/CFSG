module

public import CFSG.GH74.Generic.S45.LBridge
public import CFSG.GH74.Generic.S45.LOrd

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

@[expose] def SporRow (s : TauCeti.SporadicName) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310 K y L →
    NativeSporadic.IsSporadic (K ⧸ center K) s → False

@[expose] def SporRowCls (s : TauCeti.SporadicName) (c : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310 K y L →
    NativeSporadic.IsSporadic (K ⧸ center K) s →
    ∀ yb : MulAut (K ⧸ center K), (∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k)) →
      Nat.card ↥(autFixed yb) = c → False

theorem false_of_fixed_card {S : Type} [Group S] {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) (hc : OrdClosable (Nat.card ↥(autFixed ya))) : False := by
  refine hc q hQ.q5 hQ.mod8 ?_
  have hdvd : Nat.card ↥Lb ∣ Nat.card ↥(autFixed ya) := Subgroup.card_dvd_of_le hQ.le
  have hN : Nat.card ↥Lb = q * (q ^ 2 - 1) / 2 := by
    have := hQ.card
    omega
  rwa [← hN]

theorem sporRowCls_of_perfect_order_four (s : TauCeti.SporadicName) (c : ℕ)
    (h : ∀ (S : Type) [Group S], (S ≃* NativeSporadic.Carrier s) → ∀ α : MulAut S, α * α = 1 →
      α ≠ 1 → Nat.card ↥(autFixed α) = c →
        ∃ P : Subgroup S, P ≤ autFixed α ∧ ⁅P, P⁆ = P ∧ ∃ x ∈ P, 4 ∣ orderOf x) :
    SporRowCls s c := by
  intro K _ _ y L hyp hS yb hyb hcard
  obtain ⟨e⟩ := hS
  obtain ⟨yb', Lb, q, hyb', hQ, -⟩ := hyp.quot_data
  have hyy : yb = yb' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hyb, hyb']
  subst hyy
  obtain ⟨P, hPle, hPperf, x, hx, h4⟩ := h _ e yb hQ.sq hQ.ne hcard
  exact hyp.false_of_perfect_order_four hyb hPle hPperf hx h4

theorem sporRow_of_perfect_order_four (s : TauCeti.SporadicName)
    (h : ∀ (S : Type) [Group S], (S ≃* NativeSporadic.Carrier s) → ∀ α : MulAut S, α * α = 1 →
      α ≠ 1 → ∃ P : Subgroup S, P ≤ autFixed α ∧ ⁅P, P⁆ = P ∧ ∃ x ∈ P, 4 ∣ orderOf x) :
    SporRow s := by
  intro K _ _ y L hyp hS
  obtain ⟨e⟩ := hS
  obtain ⟨yb, Lb, q, hyb, hQ, -⟩ := hyp.quot_data
  obtain ⟨P, hPle, hPperf, x, hx, h4⟩ := h _ e yb hQ.sq hQ.ne
  exact hyp.false_of_perfect_order_four hyb hPle hPperf hx h4

end CFSG.GH74.Generic.S45
