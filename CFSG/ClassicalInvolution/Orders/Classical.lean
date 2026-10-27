module

public import CFSG.ClassicalInvolution.Orders.Symplectic
public import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.ClassicalInvolution

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Timmesfeld.ClassicalOrders

theorem card_statedClassicalModel_of_ne_two {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel G t n p f) :
    (t = .PSL → Nat.card G = ordA (n - 1) (p ^ f)) ∧
    (t = .PSU → Nat.card G = ordTwistedA (n - 1) (p ^ f)) ∧
    (t = .PSp → Nat.card G = ordBC n (p ^ f)) ∧
    (t = .POmegaOdd → Nat.card G = ordBC n (p ^ f)) ∧
    (t = .POmegaPlus → Nat.card G = ordD n (p ^ f)) ∧
    (t = .POmegaMinus → Nat.card G = ordTwistedD n (p ^ f)) := by
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_⟩ <;>
    subst ht
  · obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL (by omega), hK, ordA,
      Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]
  · obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSU hp hf hK (by omega), ordTwistedA,
      Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]
  · obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact card_statedProj_statedSp_eq_ordBC hp hp2 hK (by omega)
  · obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact card_statedProj_statedOmega_quadOdd_eq_ordBC hp hp2 hK hn
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact card_statedProj_statedOmega_quadPlus_eq_ordD hp hp2 hK hn
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact card_statedProj_statedOmega_quadMinus_eq_ordTwistedD hp hp2 hK hn hirr

end CFSG.ClassicalInvolution
