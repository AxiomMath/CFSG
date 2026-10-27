module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74

open CFSG.Open CFSG.SectionRank

theorem twoRank_eq_of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) : twoRank G = twoRank H :=
  pRank_top_eq_of_mulEquiv Nat.one_lt_two e

namespace SmallRanks

theorem isPGroup_two_of_isElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsPGroup 2 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) := by
  obtain ⟨T, hET⟩ := (isPGroup_two_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  refine ⟨g, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have h2 : (g • T : Sylow 2 G) = S := hg
  rw [← h2, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) _ (hET he)

theorem twoRank_le_of_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {r : ℕ}
    (h : ∀ E : Subgroup G, E ≤ (S : Subgroup G) → IsElemAbelian 2 E → Nat.card E ≤ 2 ^ r) :
    twoRank G ≤ r := by
  refine pRank_le Nat.one_lt_two (fun E _ hE => ?_)
  obtain ⟨g, hg⟩ := exists_conj_le_sylow S hE
  have h1 := h _ hg (isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1

theorem card_mul_relIndex_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := (H.subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact h1

theorem card_le_two_of_sq_eq_one_cyclic {G : Type*} [Group G] [Finite G] (c : G)
    (E : Subgroup G) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card ↥(E ⊓ Subgroup.zpowers c) ≤ 2 := by
  classical
  let C := Subgroup.zpowers c
  have : Fintype C := Fintype.ofFinite C
  have h := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have key : ∀ x : ↥(E ⊓ C), (⟨x.1, x.2.2⟩ : C) ^ 2 = 1 := fun x => by
    apply Subtype.ext
    simpa using hE x.1 x.2.1
  have hle : Nat.card ↥(E ⊓ C) ≤ Nat.card {a : C // a ^ 2 = 1} := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨x.1, x.2.2⟩, key x⟩ : {a : C // a ^ 2 = 1})) ?_
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun z : {a : C // a ^ 2 = 1} => (z.1 : G)) hxy
    simpa using this
  have hR : Nat.card {a : C // a ^ 2 = 1} =
      (Finset.univ.filter (fun a : C => a ^ 2 = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hle.trans (hR ▸ h)

theorem twoRank_le_two_of_orderOf {G : Type*} [Group G] [Finite G] (c : G) (m : ℕ)
    (hc : orderOf c = 2 ^ m) (hG : (Nat.card G).factorization 2 = m + 1) :
    twoRank G ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hc])
  obtain ⟨S, hCS⟩ := hC.exists_le_sylow
  have hS : Nat.card (S : Subgroup G) = 2 ^ (m + 1) := by rw [S.card_eq_multiplicity, hG]
  refine twoRank_le_of_sylow S (r := 2) (fun E hES hE => ?_)
  have hCcard : Nat.card (Subgroup.zpowers c) = 2 ^ m := by rw [Nat.card_zpowers, hc]
  have hEC := card_le_two_of_sq_eq_one_cyclic c E (fun x hx => by simpa using hE.2 x hx)
  have hEC_le : E ⊓ Subgroup.zpowers c ≤ (S : Subgroup G) := inf_le_left.trans hES
  have h1 := card_mul_relIndex_of_le hES
  have h2 := card_mul_relIndex_of_le hCS
  have h3 := card_mul_relIndex_of_le hEC_le
  have h4 := Subgroup.relIndex_inf_le (H := E) (K := Subgroup.zpowers c) (L := (S : Subgroup G))
  rw [hS] at h1 h2 h3
  rw [hCcard] at h2
  have hj : (Subgroup.zpowers c).relIndex (S : Subgroup G) = 2 := by
    have hpos : 0 < 2 ^ m := by positivity
    rw [pow_succ] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  rw [hj] at h4
  have hipos : 0 < E.relIndex (S : Subgroup G) := by
    rcases Nat.eq_zero_or_pos (E.relIndex (S : Subgroup G)) with h0 | h0
    · rw [h0, mul_zero] at h1
      exact absurd h1.symm (by positivity)
    · exact h0
  have h5 : 2 ^ (m + 1) ≤ 2 * (2 * E.relIndex (S : Subgroup G)) := by
    calc 2 ^ (m + 1) = Nat.card ↥(E ⊓ Subgroup.zpowers c) *
          (E ⊓ Subgroup.zpowers c).relIndex (S : Subgroup G) := h3.symm
      _ ≤ 2 * (E.relIndex (S : Subgroup G) * 2) := Nat.mul_le_mul hEC h4
      _ = 2 * (2 * E.relIndex (S : Subgroup G)) := by ring
  rw [← h1] at h5
  have h6 : Nat.card E * E.relIndex (S : Subgroup G) ≤ 4 * E.relIndex (S : Subgroup G) := by
    linarith
  have := Nat.le_of_mul_le_mul_right h6 hipos
  simpa using this

theorem factorization_two_pow_mul_odd {k n : ℕ} (hn : Odd n) :
    (2 ^ k * n).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) hn.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hn.not_two_dvd_nat, add_zero]

end SmallRanks

end CFSG.GH74
