module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Inputs
public import CFSG.HardMathSupport.RichardWeiss.Proving.PairRelations

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.CGT.PushingUpLit.CGT6

theorem zpowers_eq_of_card_three {K : Type*} [Group K] (hcard : Nat.card K = 3) {a b : K}
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htop : ∀ c : K, orderOf c = 3 → Subgroup.zpowers c = ⊤ := by
    intro c hc
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hc, hcard]
  rw [htop a ha, htop b hb]

theorem pair_type {K : Type} [Group K] (hK : IsZ3E9A4A5 K) {a b : K} (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Subgroup.zpowers a ≠ Subgroup.zpowers b)
    (hgen : Subgroup.closure ({a, b} : Set K) = ⊤) :
    (Nonempty (K ≃* Multiplicative (ZMod 3 × ZMod 3)) ∧ a * b = b * a) ∨
    (Nonempty (K ≃* alternatingGroup (Fin 4)) ∧ ((a * b) ^ 2 = 1 ↔ (a * b⁻¹) ^ 2 ≠ 1)) ∨
    (Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
      ((a * b) ^ 5 = 1 ∧ (b⁻¹ * a * b * a) ^ 2 = 1)) := by
  rcases hK with h | h | h | h
  · obtain ⟨e⟩ := h
    exfalso
    have hcard : Nat.card K = 3 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card]
    exact hab (zpowers_eq_of_card_three hcard ha hb)
  · refine Or.inl ⟨h, ?_⟩
    obtain ⟨e⟩ := h
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨⟨e⟩, transport_alt4_pair_iff e ha hb hab⟩)
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr ⟨⟨e⟩, transport_alt5_relations e ha hb hgen⟩)

end CFSG.HardMathSupport.RichardWeiss.Proving

end
