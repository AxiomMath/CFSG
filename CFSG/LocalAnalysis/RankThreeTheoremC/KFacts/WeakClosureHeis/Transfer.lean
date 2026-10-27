module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueSylow
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open
open scoped commutatorElement

section TransferHelpers

private theorem isMulCommutative_map_of_hom {A B : Type*} [Group A] [Group B] (f : A →* B)
    {S : Subgroup A} (hS : IsMulCommutative S) : IsMulCommutative (S.map f) := by
  rw [isMulCommutative_iff] at hS ⊢
  intro a b
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
  apply Subtype.ext
  show (a : B) * b = b * a
  rw [← hxa, ← hyb, ← map_mul, ← map_mul]
  have := congrArg (fun z : S => f z) (hS ⟨x, hx⟩ ⟨y, hy⟩)
  simpa using this

private theorem isElemAbelian_map_of_hom {p : ℕ} {A B : Type*} [Group A] [Group B] (f : A →* B)
    {E : Subgroup A} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  exact CFSG.Open.IsElemAbelian.map hE f

private theorem card_map_of_injOn {A B : Type*} [Group A] [Group B] (f : A →* B) (S : Subgroup A)
    (hf : Set.InjOn f (S : Set A)) : Nat.card (S.map f) = Nat.card S :=
  Nat.card_image_of_injOn hf

private theorem isElemAbelian_of_map_of_injOn {p : ℕ} {A B : Type*} [Group A] [Group B]
    (f : A →* B) {S E : Subgroup A} (hES : E ≤ S) (hf : Set.InjOn f (S : Set A))
    (h : IsElemAbelian p (E.map f)) : IsElemAbelian p E := by
  refine ⟨?_, ?_⟩
  · have hc := h.1
    rw [isMulCommutative_iff] at hc ⊢
    intro a b
    have h1 := hc ⟨f a, Subgroup.mem_map_of_mem f a.2⟩ ⟨f b, Subgroup.mem_map_of_mem f b.2⟩
    have h2 : f ((a : A) * b) = f ((b : A) * a) := by
      simpa [map_mul] using congrArg Subtype.val h1
    exact Subtype.ext (hf (S.mul_mem (hES a.2) (hES b.2)) (S.mul_mem (hES b.2) (hES a.2)) h2)
  · intro x hx
    have h1 : f (x ^ p) = f 1 := by
      rw [map_pow, map_one]
      exact h.2 _ (Subgroup.mem_map_of_mem f hx)
    exact hf (S.pow_mem (hES hx) p) S.one_mem h1

private theorem pRank_map_of_injOn {p : ℕ} {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (S : Subgroup A) (hf : Set.InjOn f (S : Set A)) :
    CFSG.Open.pRank p (S.map f) = CFSG.Open.pRank p S := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hES, hE, hcard⟩
    have hmap : (E.comap f ⊓ S).map f = E := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hx1, -⟩, rfl⟩
        exact hx1
      · intro y hy
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 (hES hy)
        exact ⟨s, ⟨hy, hs⟩, rfl⟩
    have hinj : Set.InjOn f ((E.comap f ⊓ S : Subgroup A) : Set A) :=
      hf.mono (by exact_mod_cast (inf_le_right : E.comap f ⊓ S ≤ S))
    refine ⟨E.comap f ⊓ S, inf_le_right, ?_, ?_⟩
    · exact isElemAbelian_of_map_of_injOn f (S := S) inf_le_right hf (by rw [hmap]; exact hE)
    · rw [← card_map_of_injOn f _ hinj, hmap]
      exact hcard
  · rintro ⟨E, hES, hE, hcard⟩
    refine ⟨E.map f, Subgroup.map_mono hES, isElemAbelian_map_of_hom f hE, ?_⟩
    rw [card_map_of_injOn f E (hf.mono (by exact_mod_cast hES))]
    exact hcard

private theorem pRank_mono_of_le {p : ℕ} (hp : 1 < p) {K : Type*} [Group K] [Finite K]
    {H H' : Subgroup K} (h : H ≤ H') : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p H' := by
  unfold CFSG.Open.pRank
  apply csSup_le_csSup
  · refine ⟨Nat.card K, ?_⟩
    rintro k' ⟨E', -, -, hk'⟩
    have h1 : p ^ k' ≤ Nat.card K := hk' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self hp).le.trans h1
  · exact ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by
      rw [(Subgroup.mem_bot).1 hx, one_pow]⟩, by simp⟩
  · rintro k ⟨E, hEH, hE, hk⟩
    exact ⟨E, hEH.trans h, hE, hk⟩

private theorem violation_map_iff_of_injOn {p : ℕ} {A B : Type} [Group A] [Finite A] [Group B]
    [Finite B] (f : A →* B) (U : Subgroup A) (hf : Set.InjOn f (U : Set A)) :
    (4 ≤ CFSG.Open.pRank p (U.map f) ∨ ¬ IsCyclic ↥⁅U.map f, U.map f⁆ ∨
      ((∀ u ∈ U.map f, u ^ p = 1) ∧ p ^ 5 ≤ Nat.card (U.map f))) ↔
    (4 ≤ CFSG.Open.pRank p U ∨ ¬ IsCyclic ↥⁅U, U⁆ ∨
      ((∀ u ∈ U, u ^ p = 1) ∧ p ^ 5 ≤ Nat.card U)) := by
  have hC : ⁅U.map f, U.map f⁆ = (⁅U, U⁆).map f := (Subgroup.map_commutator U U f).symm
  have hCU : ⁅U, U⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha)) (U.inv_mem hb)
  have hcyc : IsCyclic ↥((⁅U, U⁆).map f) ↔ IsCyclic ↥⁅U, U⁆ := by
    constructor
    · intro hc
      refine isCyclic_of_injective (f.subgroupMap ⁅U, U⁆) ?_
      intro x y hxy
      exact Subtype.ext (hf (hCU x.2) (hCU y.2) (congrArg Subtype.val hxy))
    · intro hc
      exact isCyclic_of_surjective (f.subgroupMap ⁅U, U⁆) (f.subgroupMap_surjective _)
  have hexp : (∀ u ∈ U.map f, u ^ p = 1) ↔ (∀ u ∈ U, u ^ p = 1) := by
    constructor
    · intro h u hu
      have h1 : f (u ^ p) = f 1 := by
        rw [map_pow, map_one]
        exact h _ (Subgroup.mem_map_of_mem f hu)
      exact hf (U.pow_mem hu p) U.one_mem h1
    · rintro h _ ⟨u, hu, rfl⟩
      rw [← map_pow, h u hu, map_one]
  rw [pRank_map_of_injOn f U hf, hC, card_map_of_injOn f U hf, hexp]
  simp only [hcyc]

private theorem injOn_of_isPGroup_of_not_dvd_ker {G K : Type} [Group G] [Finite G] [Group K]
    {p : ℕ} (hp : p.Prime) (π : G →* K) (hker : ¬ p ∣ Nat.card π.ker) {U : Subgroup G}
    (hU : IsPGroup p U) : Set.InjOn π (U : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hU
  have hcop : Nat.Coprime (Nat.card U) (Nat.card π.ker) := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hker)
  have hdis : Disjoint U π.ker := Subgroup.disjoint_of_coprime_natCard hcop
  intro a ha b hb hab
  have h1 : a⁻¹ * b = 1 := by
    refine Subgroup.disjoint_def.1 hdis (U.mul_mem (U.inv_mem ha) hb) ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  exact inv_mul_eq_one.1 h1

end TransferHelpers

namespace SylowDichotomyAt

theorem of_normal_coprime_index {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hN : ¬ p ∣ N.index) (h : SylowDichotomyAt G p) :
    SylowDichotomyAt N p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : (Nat.card G).factorization p = (Nat.card N).factorization p := by
    rw [← Subgroup.card_mul_index N,
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp [Nat.factorization_eq_zero_of_not_dvd hN]
  have hF : ∀ U : Subgroup G, IsPGroup p U → U ≤ N := by
    intro U hU u hu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have hk' : u ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (QuotientGroup.mk (s := N) u) ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    have h2 : orderOf (QuotientGroup.mk (s := N) u) ∣ N.index := by
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) N.index :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
    have h3 : orderOf (QuotientGroup.mk (s := N) u) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff] at h3
    exact (QuotientGroup.eq_one_iff u).1 h3
  rcases h with h | h | h | ⟨U, hU, hv⟩
  · exact of_factorization_le (by rw [← hcard]; exact h)
  ·
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p G))
    have hQN : (Q : Subgroup G) ≤ N := hF _ Q.isPGroup'
    have hmapQ : ((Q : Subgroup G).subgroupOf N).map N.subtype = (Q : Subgroup G) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hQN]
    refine of_abelian_full hp (A := (Q : Subgroup G).subgroupOf N) ?_ ?_
    · rw [← isMulCommutative_map_iff_of_injective N.subtype N.subtype_injective, hmapQ]
      exact h Q
    · rw [← Subgroup.card_map_of_injective N.subtype_injective, hmapQ, Q.card_eq_multiplicity,
        hcard]
  ·
    apply of_pRank_le
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup N) = CFSG.Open.pRank p (N : Subgroup G) := by
      rw [← pRank_map_of_injOn N.subtype (⊤ : Subgroup N) N.subtype_injective.injOn]
      congr 1
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1]
    exact (pRank_mono_of_le hp.one_lt le_top).trans h
  ·
    have hUN : U ≤ N := hF U hU
    have hmap : (U.comap N.subtype).map N.subtype = U :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hUN)
    refine of_violation (U := U.comap N.subtype) hU.comap_subtype ?_
    rw [← violation_map_iff_of_injOn N.subtype (U.comap N.subtype) N.subtype_injective.injOn,
      hmap]
    exact hv

theorem of_surjective_coprime_ker {G K : Type} [Group G] [Finite G] [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (π : G →* K) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    (h : SylowDichotomyAt G p) : SylowDichotomyAt K p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : (Nat.card K).factorization p = (Nat.card G).factorization p := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hπ,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  have hinj : ∀ U : Subgroup G, IsPGroup p U → Set.InjOn π (U : Set G) := fun U hU =>
    injOn_of_isPGroup_of_not_dvd_ker hp π hker hU
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p G))
  have hQcard : Nat.card ((Q : Subgroup G).map π) = p ^ (Nat.card K).factorization p := by
    rw [card_map_of_injOn π _ (hinj _ Q.isPGroup'), Q.card_eq_multiplicity, hcard]
  rcases h with h | h | h | ⟨U, hU, hv⟩
  · exact of_factorization_le (by rw [hcard]; exact h)
  · exact of_abelian_full hp (A := (Q : Subgroup G).map π) (isMulCommutative_map_of_hom π (h Q))
      hQcard
  · apply of_pRank_le
    let T : Sylow p K := Sylow.ofCard _ hQcard
    have hT : (T : Subgroup K) = (Q : Subgroup G).map π := Sylow.coe_ofCard _ _
    rw [pRank_top_eq_of_sylow T, hT, pRank_map_of_injOn π _ (hinj _ Q.isPGroup'),
      ← pRank_top_eq_of_sylow Q]
    exact h
  · exact of_violation (hU.map π) ((violation_map_iff_of_injOn π U (hinj U hU)).2 hv)

end SylowDichotomyAt

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
