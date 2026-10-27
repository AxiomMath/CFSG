module

public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.ComponentClassification.OutcomeLocal

theorem prime_residual_commuting_fixed_points {p : ℕ} [hp : Fact p.Prime] {V X B : Type*}
    [Group V] [Group X] [Group B] [Finite V] [Finite X] [Finite B] (hV : IsPGroup p V)
    (hX : ∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤) (hB : IsPGroup p B)
    (α : X →* MulAut V) (β : B →* MulAut V) (hcomm : ∀ x b, α x * β b = β b * α x) :
    (∀ x v, (∀ b, β b v = v) → α x v = v) ↔ ∀ x v, α x v = v := by
  refine ⟨fun hfix => ?_, fun h x v _ => h x v⟩
  have hcop : ∀ y : X, ¬ p ∣ orderOf y → α y = 1 := by
    intro y hy
    have hA : ¬ p ∣ Nat.card (Subgroup.zpowers y) := by rwa [Nat.card_zpowers]
    exact CFSG.GroupTheory.thompson_A_times_B hV hA hB (α.comp (Subgroup.zpowers y).subtype) β
      (fun a b => hcomm a b) (fun a r hr => hfix a r hr) ⟨y, Subgroup.mem_zpowers y⟩
  have hker : α.ker = ⊤ := by
    refine hX _ fun g => ?_
    induction g using QuotientGroup.induction_on with
    | H x =>
      refine ⟨(orderOf x).factorization p, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker]
      have hx : orderOf x ≠ 0 := (orderOf_pos x).ne'
      apply hcop
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) (Nat.ordProj_dvd _ _)]
      exact Nat.not_dvd_ordCompl hp.out hx
  intro x v
  rw [MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top x : x ∈ α.ker)]
  rfl

end CFSG.ComponentClassification.OutcomeLocal
