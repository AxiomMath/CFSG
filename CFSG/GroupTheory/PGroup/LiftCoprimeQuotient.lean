module

public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem exists_lift_of_isPGroup_of_not_dvd_card {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N) {X : Subgroup G}
    (hX : IsPGroup p X) {Xbar : Subgroup (G ⧸ N)}
    (hXbar : X.map (QuotientGroup.mk' N) = Xbar)
    {V : Type*} [Group V] (c₀ : V →* G ⧸ N) (hc₀ : c₀.range = Xbar) :
    ∃ a : V →* G, a.range = X ∧ ∀ v, QuotientGroup.mk' N (a v) = c₀ v := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let f : X →* G ⧸ N := π.comp X.subtype
  have hinj : Function.Injective f := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
    (p := p) (N := N) (Q := X) hN hX
  have hrange : f.range = Xbar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hXbar]
  let e : X ≃* Xbar := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let cA : V →* Xbar := c₀.codRestrict Xbar (fun v => by
    rw [← hc₀]
    exact ⟨v, rfl⟩)
  have hcA_surj : Function.Surjective cA := by
    intro x
    have hx : (x : G ⧸ N) ∈ c₀.range := by rw [hc₀]; exact x.2
    obtain ⟨v, hv⟩ := hx
    exact ⟨v, Subtype.ext hv⟩
  let aX : V →* X := e.symm.toMonoidHom.comp cA
  have haX_surj : Function.Surjective aX := fun x =>
    (e.symm.surjective.comp hcA_surj) x
  have hrangeX : aX.range = ⊤ := MonoidHom.range_eq_top.mpr haX_surj
  refine ⟨X.subtype.comp aX, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrangeX, Subgroup.map_top, Subgroup.range_subtype]
  · intro v
    show f (aX v) = c₀ v
    have h1 : f (aX v) = e (aX v) := rfl
    rw [h1]
    show e (e.symm (cA v)) = c₀ v
    rw [MulEquiv.apply_symm_apply]
    rfl

end CFSG.GroupTheory
