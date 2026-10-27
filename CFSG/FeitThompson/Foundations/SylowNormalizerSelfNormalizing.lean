module

public import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

open Pointwise Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem coe_conj_smul_eq_map (g : G) (P : Subgroup G) :
    MulAut.conj g • P = P.map (MulAut.conj g : G →* G) :=
  toSubmonoid_inj.mp rfl

theorem natCard_subgroupOf_eq_pow_factorization [Finite G] {P N : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) (hPN : P ≤ N) :
    Nat.card (P.subgroupOf N) = p ^ (Nat.card N).factorization p := by
  have := ((Sylow.ofCard P hP).subtype (by simpa using hPN)).card_eq_multiplicity
  rwa [Sylow.coe_subtype, Sylow.coe_ofCard] at this

theorem normalizer_normalizer_of_natCard_eq_pow_factorization [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    normalizer ((normalizer (P : Set G) : Subgroup G) : Set G) = normalizer (P : Set G) := by
  set N : Subgroup G := normalizer (P : Set G)
  refine le_antisymm (fun x hx => ?_) le_normalizer
  have hPN : P ≤ N := le_normalizer
  have hxN : map (MulAut.conj x : G →* G) N = N := mem_normalizer_iff_map_conj_eq.mp hx
  set Q : Subgroup G := MulAut.conj x • P with hQ
  have hQN : Q ≤ N := by
    rw [hQ, coe_conj_smul_eq_map, ← hxN]
    exact map_mono hPN
  have hSylP : Nat.card (P.subgroupOf N) = p ^ (Nat.card N).factorization p :=
    natCard_subgroupOf_eq_pow_factorization hP hPN
  have hSylQ : Nat.card (Q.subgroupOf N) = p ^ (Nat.card N).factorization p := by
    rw [← hSylP, Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv, hQ, natCard_conj_smul]
  obtain ⟨n, hn⟩ := exists_conj_smul_eq (p := p) hSylQ hSylP
  have hnormal : (P.subgroupOf N).Normal := normal_in_normalizer
  have hAB : Q.subgroupOf N = P.subgroupOf N := by
    rw [show Q.subgroupOf N = (MulAut.conj n)⁻¹ • (P.subgroupOf N) by rw [← hn, inv_smul_smul],
      ← map_inv, hnormal.conj_smul_eq_self]
  have hQP : Q = P := by
    have := subgroupOf_inj.mp hAB
    rwa [inf_of_le_left hQN, inf_of_le_left hPN] at this
  exact mem_normalizer_iff_map_conj_eq.mpr (by rw [← coe_conj_smul_eq_map, ← hQ, hQP])

theorem mem_normalizer_normalizer_iff [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) {x : G} :
    x ∈ normalizer ((normalizer (P : Set G) : Subgroup G) : Set G) ↔
      x ∈ normalizer (P : Set G) := by
  rw [normalizer_normalizer_of_natCard_eq_pow_factorization hP]

theorem sylow_normalizer_normalizer [Finite G] (P : Sylow p G) :
    normalizer ((normalizer ((P : Subgroup G) : Set G) : Subgroup G) : Set G) =
      normalizer ((P : Subgroup G) : Set G) :=
  normalizer_normalizer_of_natCard_eq_pow_factorization P.card_eq_multiplicity

end

end CFSG.FeitThompson
