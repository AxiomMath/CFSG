module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonClass

public section

namespace CFSG.ClassicalInvolution.Asc77.Star3T

variable {Q : Type*} [Group Q] {Δ : Set Q}

theorem cent_eq_of_mem_cent (h : IsTT Δ) (hS : IsStar Δ) {p q : Q} (hp : p ∈ Δ) (hq : q ∈ Δ)
    (hpq : ¬ Conn Δ p q) {z : Q} (hz : z ∈ cent Δ p) : cent Δ z = cent Δ p := by
  have hpl : IsPlane Δ p q (p * q * p) := ⟨hp, hq, hpq, rfl⟩
  have hr : p * q * p ∈ Δ := h.mem_third hpl
  ext y
  constructor
  · intro hy
    have hpy : Conn Δ p y :=
      (conn_of_mem_cent hp hz).trans (conn_of_commute hz.1 hy.1 hy.2.symm)
    have hU := IsTT.cent_union_eq hS hpl
    have hyΔ : y ∈ Δ := hy.1
    rw [hU] at hyΔ
    rcases hyΔ with (h1 | h2) | h3
    · exact h1
    · exact absurd (hpy.trans (conn_of_mem_cent hq h2).symm) hpq
    · exact absurd (hpy.trans (conn_of_mem_cent hr h3).symm) (h.not_conn_third_left hpl)
  · intro hy
    exact ⟨hy.1, h.isClique_cent hS hp hq hpq hy hz⟩

variable [Finite Q]

theorem exists_mulEquiv_perm_four_of_closure (h : IsTT Δ) (hS : IsStar Δ) {Λ : Set Q}
    (hΛ : Λ ⊆ Δ) (hconj : ∀ g ∈ Subgroup.closure Λ, ∀ x ∈ Λ, g * x * g⁻¹ ∈ Λ) {d a : Q}
    (hd : d ∈ Λ) (ha : a ∈ Λ) (hc : ¬ Conn Λ d a) (hk : (cent Λ d).ncard = 2) :
    ∃ e : ↥(Subgroup.closure Λ) ≃* Equiv.Perm (Fin 4), ∀ (x : Q) (hx : x ∈ Subgroup.closure Λ),
      x ∈ Λ ↔ (e ⟨x, hx⟩).IsSwap := by
  set H : Subgroup Q := Subgroup.closure Λ with hH
  let Δ' : Set ↥H := {y | (y : Q) ∈ Λ}
  have hcomm : ∀ x y : ↥H, (x : Q) * y = y * x ↔ x * y = y * x := fun x y => by
    rw [← Subtype.coe_inj]
    rfl
  have hT' : IsTT Δ' :=
    { mul_self := fun y hy => Subtype.ext (h.mul_self _ (hΛ hy))
      ne_one := fun y hy e => h.ne_one _ (hΛ hy) (congrArg Subtype.val e)
      conj_mem := fun y hy g => hconj g.1 g.2 y hy
      closure_eq_top := Subgroup.closure_closure_coe_preimage
      comm_or_cube := fun x hx y hy => by
        rcases h.comm_or_cube _ (hΛ hx) _ (hΛ hy) with h1 | h1
        · exact Or.inl ((hcomm x y).mp h1)
        · exact Or.inr (Subtype.ext h1) }
  have hS' : IsStar Δ' := by
    intro x hx y hy hxy z hz
    have hxy' : (x : Q) * y ≠ y * x := fun e => hxy ((hcomm x y).mp e)
    rcases hS _ (hΛ hx) _ (hΛ hy) hxy' _ (hΛ hz) with h1 | h1 | h1
    · exact Or.inl ((hcomm z x).mp h1)
    · exact Or.inr (Or.inl ((hcomm z y).mp h1))
    · exact Or.inr (Or.inr ((hcomm z (x * y * x)).mp h1))
  have hdH : d ∈ H := Subgroup.subset_closure hd
  have haH : a ∈ H := Subgroup.subset_closure ha
  have hc' : ¬ Conn Δ' ⟨d, hdH⟩ ⟨a, haH⟩ := by
    intro hcon
    refine hc ?_
    exact Relation.ReflTransGen.lift (Subtype.val : ↥H → Q) (r := Adj Δ') (p := Adj Λ)
      (fun x y hxy => ⟨hxy.1, hxy.2.1, (hcomm x y).mpr hxy.2.2⟩) _ _ hcon
  have hk' : (cent Δ' ⟨d, hdH⟩).ncard = 2 := by
    have himg : (Subtype.val : ↥H → Q) '' cent Δ' ⟨d, hdH⟩ = cent Λ d := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.1, (hcomm x ⟨d, hdH⟩).mpr hx.2⟩
      · intro hy
        exact ⟨⟨y, Subgroup.subset_closure hy.1⟩, ⟨hy.1, (hcomm ⟨y, _⟩ ⟨d, hdH⟩).mp hy.2⟩, rfl⟩
    rw [← hk, ← himg]
    exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
  obtain ⟨e, he⟩ := exists_mulEquiv_perm_four hT' hS' (d := ⟨d, hdH⟩) (a := ⟨a, haH⟩) hd ha hc' hk'
  exact ⟨e, fun x hx => he ⟨x, hx⟩⟩

end CFSG.ClassicalInvolution.Asc77.Star3T
