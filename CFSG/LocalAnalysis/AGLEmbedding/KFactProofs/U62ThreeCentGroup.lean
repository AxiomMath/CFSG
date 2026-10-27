module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding.U62ThreeCent

@[expose] def HasLarge {G : Type*} [Group G] (x : G) : Prop :=
  (∃ E : Subgroup G, E ≤ Subgroup.centralizer {x} ∧ IsMulCommutative E ∧ (∀ y ∈ E, y ^ 3 = 1) ∧
    Nat.card E = 3 ^ 4) ∧
  ∃ Y : Subgroup G, Y ≤ Subgroup.centralizer {x} ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ^ 5

theorem HasLarge.map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {x : G} (hx : HasLarge x) :
    HasLarge (e x) := by
  obtain ⟨⟨E, hEC, hEc, hE3, hEcard⟩, Y, hYC, -, hYcard⟩ := hx
  have hcent : ∀ T : Subgroup G, T ≤ Subgroup.centralizer {x} →
      T.map e.toMonoidHom ≤ Subgroup.centralizer {e x} := by
    rintro T hT _ ⟨t, ht, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hT ht)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e t * e x = e x * e t
    rw [← map_mul, ← map_mul, h1]
  refine ⟨⟨E.map e.toMonoidHom, hcent E hEC, ?_, ?_, ?_⟩, Y.map e.toMonoidHom, hcent Y hYC, ?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨_, a', ha', rfl⟩ := a
    obtain ⟨_, b', hb', rfl⟩ := b
    apply Subtype.ext
    change e a' * e b' = e b' * e a'
    have h := hEc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
    rw [← map_mul, ← map_mul]
    exact congrArg e (congrArg Subtype.val h)
  · rintro _ ⟨a, ha, rfl⟩
    change e a ^ 3 = 1
    rw [← map_pow, hE3 a ha, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hEcard]
  · refine IsPGroup.of_card (n := 5) ?_
    rw [Subgroup.card_map_of_injective e.injective, hYcard]
  · rw [Subgroup.card_map_of_injective e.injective, hYcard]

theorem hasLarge_of_normalizer {G : Type*} [Group G] [Finite G] {x : G} {E : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer {x}) (hEc : IsMulCommutative E) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hEcard : Nat.card E = 3 ^ 4) {y : G} (hyC : y ∈ Subgroup.centralizer {x})
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) (hyE : y ∉ E) (hy3 : y ^ 3 ∈ E) :
    HasLarge x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨E, hEC, hEc, hE3, hEcard⟩, ?_⟩
  set N : Subgroup G := Subgroup.centralizer {x} ⊓ Subgroup.normalizer (E : Set G) with hN
  have hEN : E ≤ N := fun e he => ⟨hEC he, Subgroup.le_normalizer he⟩
  have hnorm : (E.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEN]
    intro e n he hn
    exact (Subgroup.mem_normalizer_iff.1 hn.2 e).1 he
  set y' : N := ⟨y, hyC, hyN⟩ with hy'
  have hpow : (QuotientGroup.mk y' : N ⧸ E.subgroupOf N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hy3
  have hne : (QuotientGroup.mk y' : N ⧸ E.subgroupOf N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hyE
  have hord : orderOf (QuotientGroup.mk y' : N ⧸ E.subgroupOf N) = 3 := orderOf_eq_prime hpow hne
  have hdvd : 3 ∣ Nat.card (N ⧸ E.subgroupOf N) := hord ▸ orderOf_dvd_natCard _
  have hcard := Subgroup.card_mul_index (E.subgroupOf N)
  rw [Subgroup.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv,
    hEcard] at hcard
  obtain ⟨m, hm⟩ := hdvd
  have h5 : 3 ^ 5 ∣ Nat.card N := ⟨m, by rw [← hcard, hm]; ring⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := N) 3 h5
  refine ⟨K.map N.subtype, (Subgroup.map_subtype_le K).trans inf_le_left, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 5) ?_
    rw [Subgroup.card_map_of_injective N.subtype_injective, hK]
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hK]

end CFSG.AGLEmbedding.U62ThreeCent
