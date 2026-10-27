module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G]

@[expose] def qdMk (C : Subgroup G) : normalizer (C : Set G) →* egQD C :=
  QuotientGroup.mk' (C.subgroupOf (normalizer (C : Set G)))

@[expose] def liftSub (C : Subgroup G) (S₀ : Subgroup (egQD C)) : Subgroup G :=
  (S₀.comap (qdMk C)).map (normalizer (C : Set G)).subtype

theorem mem_liftSub {C : Subgroup G} {S₀ : Subgroup (egQD C)} {x : G} :
    x ∈ liftSub C S₀ ↔ ∃ hx : x ∈ normalizer (C : Set G), qdMk C ⟨x, hx⟩ ∈ S₀ := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem qdMk_eq_one {C : Subgroup G} {x : G} (hx : x ∈ normalizer (C : Set G)) :
    qdMk C ⟨x, hx⟩ = 1 ↔ x ∈ C := by
  show QuotientGroup.mk (⟨x, hx⟩ : normalizer (C : Set G)) = 1 ↔ x ∈ C
  rw [QuotientGroup.eq_one_iff]
  exact mem_subgroupOf

theorem le_liftSub {C : Subgroup G} {S₀ : Subgroup (egQD C)} : C ≤ liftSub C S₀ := fun x hx =>
  mem_liftSub.2 ⟨le_normalizer hx, by rw [(qdMk_eq_one (le_normalizer hx)).2 hx]; exact S₀.one_mem⟩

theorem liftSub_le_normalizer {C : Subgroup G} {S₀ : Subgroup (egQD C)} :
    liftSub C S₀ ≤ normalizer (C : Set G) := fun _ hx => (mem_liftSub.1 hx).1

theorem liftSub_isPGroup {C : Subgroup G} (hC2 : ∀ c ∈ C, c * c = 1)
    {S₀ : Subgroup (egQD C)} (hS : IsPGroup 2 S₀) : IsPGroup 2 (liftSub C S₀) := by
  intro x
  obtain ⟨hx, hxS⟩ := mem_liftSub.1 x.2
  obtain ⟨m, hm⟩ := hS ⟨_, hxS⟩
  refine ⟨m + 1, ?_⟩
  have h1 : qdMk C ⟨(x : G) ^ 2 ^ m, pow_mem hx _⟩ = 1 := by
    have : qdMk C ⟨(x : G) ^ 2 ^ m, pow_mem hx _⟩ = (qdMk C ⟨x, hx⟩) ^ 2 ^ m :=
      (map_pow (qdMk C) (⟨x, hx⟩ : normalizer (C : Set G)) (2 ^ m)).symm
    rw [this]
    exact congrArg Subtype.val hm
  have h2 : (x : G) ^ 2 ^ m ∈ C := (qdMk_eq_one _).1 h1
  apply Subtype.ext
  show (x : G) ^ 2 ^ (m + 1) = 1
  rw [pow_succ, pow_mul, sq]
  exact hC2 _ h2

theorem liftSub_maximal [Finite G] {C : Subgroup G} {S₀ : Subgroup (egQD C)} (hS : IsPGroup 2 S₀)
    (hodd : ¬ 2 ∣ S₀.index) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ normalizer (C : Set G)) (hRQ : liftSub C S₀ ≤ Q) : Q ≤ liftSub C S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Qb : Subgroup (egQD C) := (Q.subgroupOf (normalizer (C : Set G))).map (qdMk C)
  have hQb : IsPGroup 2 Qb := by
    rintro ⟨y, n, hn, rfl⟩
    obtain ⟨m, hm⟩ := hQ ⟨(n : G), hn⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    show (qdMk C n) ^ 2 ^ m = 1
    rw [← map_pow]
    have h1 : (n : G) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have : n ^ 2 ^ m = 1 := Subtype.ext h1
    rw [this, map_one]
  have hSQb : S₀ ≤ Qb := by
    intro s hs
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective s
    have hnR : (n : G) ∈ liftSub C S₀ := mem_liftSub.2 ⟨n.2, hs⟩
    exact ⟨n, hRQ hnR, rfl⟩
  let P : Sylow 2 (egQD C) := hS.toSylow hodd
  obtain ⟨Q', hQ'⟩ := hQb.exists_le_sylow
  have hPQ : (P : Subgroup (egQD C)) ≤ Q' := hSQb.trans hQ'
  have hcard : Nat.card Q' = Nat.card P := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have heq : (P : Subgroup (egQD C)) = Q' :=
    Subgroup.eq_of_le_of_card_ge hPQ (le_of_eq hcard)
  have hQbS : Qb ≤ S₀ := fun y hy => by
    have hy' : y ∈ (Q' : Subgroup (egQD C)) := hQ' hy
    rw [← heq] at hy'
    exact hy'
  intro x hx
  have hxN : x ∈ normalizer (C : Set G) := hQN hx
  refine mem_liftSub.2 ⟨hxN, hQbS ⟨⟨x, hxN⟩, hx, rfl⟩⟩

theorem card_range_eq_relIndex [Finite G] {C D : Subgroup G} (hD : D ≤ normalizer (C : Set G)) :
    Nat.card ((qdMk C).comp ((D.subgroupOf (normalizer (C : Set G))).subtype)).range =
      C.relIndex D := by
  let f := (qdMk C).comp ((D.subgroupOf (normalizer (C : Set G))).subtype)
  have h1 := Subgroup.card_ker_mul_card_range f
  have hDn : Nat.card (D.subgroupOf (normalizer (C : Set G))) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  have hker : Nat.card f.ker = Nat.card (C ⊓ D : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun d => ⟨((d.1 : normalizer (C : Set G)) : G),
          (qdMk_eq_one (d.1 : normalizer (C : Set G)).2).1 d.2, mem_subgroupOf.1 d.1.2⟩
        invFun := fun x => ⟨⟨⟨(x : G), hD x.2.2⟩, mem_subgroupOf.2 x.2.2⟩,
          (qdMk_eq_one (hD x.2.2)).2 x.2.1⟩
        left_inv := fun d => rfl
        right_inv := fun x => rfl }
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := D)
  rw [hDn, hker] at h1
  have hpos : 0 < Nat.card (C ⊓ D : Subgroup G) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (by rw [← h2, mul_comm]))

end CFSG.EvenSporadicStandard.M24Std
