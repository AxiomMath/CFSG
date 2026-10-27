module

public import CFSG.Open.LocalVocabulary

import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.PreuniquenessRankFour.PrimeCore
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Lift

public section

namespace CFSG.GroupTheory.CoprimeTransport

open CFSG.Open

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {p s : ℕ}

theorem orderOf_mk_eq_prime [Finite G] [Fact p.Prime] (hN : ¬ p ∣ Nat.card N) {x : G}
    (hx : orderOf x = p) : orderOf (QuotientGroup.mk' N x) = p := by
  have hp : p.Prime := Fact.out
  refine orderOf_eq_prime (by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]) fun h1 => ?_
  have hyO : x ∈ Subgroup.zpowers x ⊓ N :=
    ⟨Subgroup.mem_zpowers x, by rwa [← QuotientGroup.ker_mk' N]⟩
  rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hN
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])), Subgroup.mem_bot] at hyO
  rw [hyO, orderOf_one] at hx
  exact hp.one_lt.ne hx

theorem exists_mem_orderOf_eq_prime_mk_eq [Finite G] [Fact p.Prime] (hN : ¬ p ∣ Nat.card N)
    {C : Subgroup G} {y : G ⧸ N} (hyC : y ∈ C.map (QuotientGroup.mk' N)) (hy : orderOf y = p) :
    ∃ x ∈ C, orderOf x = p ∧ QuotientGroup.mk' N x = y := by
  obtain ⟨c, hcC, rfl⟩ := Subgroup.mem_map.1 hyC
  obtain ⟨m, hm1, hm2⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.exists_pow_lift_orderOf hN c hy
  exact ⟨c ^ m, C.pow_mem hcC m, hm2, hm1⟩

theorem exists_orderOf_eq_prime_mk_eq [Finite G] [Fact p.Prime] (hN : ¬ p ∣ Nat.card N)
    {y : G ⧸ N} (hy : orderOf y = p) :
    ∃ x : G, orderOf x = p ∧ QuotientGroup.mk' N x = y := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective N y
  obtain ⟨x, -, hx⟩ := exists_mem_orderOf_eq_prime_mk_eq hN (C := ⊤)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_top x₀)) hy
  exact ⟨x, hx⟩

theorem card_eq_card_map_mk_mul_card_inf [Finite G] (C : Subgroup G) :
    Nat.card C = Nat.card (C.map (QuotientGroup.mk' N)) * Nat.card ↥(C ⊓ N) := by
  set g : C →* G ⧸ N := (QuotientGroup.mk' N).comp C.subtype with hg
  have hrange : g.range = C.map (QuotientGroup.mk' N) := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : g.ker = (C ⊓ N).subgroupOf C := by
    ext x
    simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have h := Subgroup.card_ker_mul_card_range g
  rw [hker, hrange] at h
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, mul_comm] at h
  exact h.symm

theorem card_map_mk_eq_of_isPGroup [Finite G] [Fact p.Prime] (hN : ¬ p ∣ Nat.card N)
    {E : Subgroup G} (hE : IsPGroup p E) :
    Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E := by
  have h := card_eq_card_map_mk_mul_card_inf (N := N) E
  rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hN hE, Subgroup.card_bot,
    mul_one] at h
  exact h.symm

theorem dvd_card_map_mk_iff [Finite G] [Fact p.Prime] (hN : ¬ p ∣ Nat.card N) (C : Subgroup G) :
    p ∣ Nat.card (C.map (QuotientGroup.mk' N)) ↔ p ∣ Nat.card C := by
  have h := card_eq_card_map_mk_mul_card_inf (N := N) C
  have hcop : ¬ p ∣ Nat.card ↥(C ⊓ N) := fun hd =>
    hN (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  rw [h]
  constructor
  · exact fun hd => Dvd.dvd.mul_right hd _
  · intro hd
    rcases (Nat.Prime.dvd_mul Fact.out).1 hd with h1 | h1
    · exact h1
    · exact absurd h1 hcop

theorem centralizer_image_mk_eq [Finite G] [Fact s.Prime] (hs : ¬ s ∣ Nat.card N)
    {E : Subgroup G} (hE : IsPGroup s E) {S : Set G} (hSE : S ⊆ E) :
    Subgroup.centralizer (QuotientGroup.mk' N '' S) =
      (Subgroup.centralizer S).map (QuotientGroup.mk' N) := by
  have hQ : IsPGroup s (Subgroup.closure S) := hE.to_le ((Subgroup.closure_le E).2 hSE)
  have h := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := s) hs hQ
  rwa [MonoidHom.map_closure, Subgroup.centralizer_closure, Subgroup.centralizer_closure] at h

theorem pRank_centralizer_image_mk_eq [Finite G] [Fact s.Prime] [Fact p.Prime]
    (hs : ¬ s ∣ Nat.card N) (hp : ¬ p ∣ Nat.card N) {E : Subgroup G} (hE : IsPGroup s E)
    {S : Set G} (hSE : S ⊆ E) :
    CFSG.Open.pRank p (Subgroup.centralizer (QuotientGroup.mk' N '' S)) =
      CFSG.Open.pRank p (Subgroup.centralizer S) := by
  rw [centralizer_image_mk_eq hs hE hSE]
  exact CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal p Fact.out N hp _

theorem pRank_centralizer_map_mk_eq [Finite G] [Fact s.Prime] [Fact p.Prime]
    (hs : ¬ s ∣ Nat.card N) (hp : ¬ p ∣ Nat.card N) {E : Subgroup G} (hE : IsPGroup s E) :
    CFSG.Open.pRank p (Subgroup.centralizer ((E.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
      Set (G ⧸ N))) = CFSG.Open.pRank p (Subgroup.centralizer (E : Set G)) := by
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := s) hs hE]
  exact CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal p Fact.out N hp _

theorem dvd_card_centralizer_map_mk_iff [Finite G] [Fact s.Prime] [Fact p.Prime]
    (hs : ¬ s ∣ Nat.card N) (hp : ¬ p ∣ Nat.card N) {E : Subgroup G} (hE : IsPGroup s E) :
    p ∣ Nat.card (Subgroup.centralizer ((E.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
      Set (G ⧸ N))) ↔ p ∣ Nat.card (Subgroup.centralizer (E : Set G)) := by
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := s) hs hE]
  exact dvd_card_map_mk_iff hp _

theorem exists_mem_centralizer_orderOf_eq_prime_mk_eq [Finite G] [Fact s.Prime] [Fact p.Prime]
    (hs : ¬ s ∣ Nat.card N) (hp : ¬ p ∣ Nat.card N) {E : Subgroup G} (hE : IsPGroup s E)
    {y : G ⧸ N}
    (hyC : y ∈ Subgroup.centralizer ((E.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
      Set (G ⧸ N))) (hy : orderOf y = p) :
    ∃ x ∈ Subgroup.centralizer (E : Set G), orderOf x = p ∧ QuotientGroup.mk' N x = y := by
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := s) hs hE] at hyC
  exact exists_mem_orderOf_eq_prime_mk_eq hp hyC hy

theorem le_pRank_centralizer_of_quotient [Finite G] [Fact p.Prime] (hN : ¬ p ∣ Nat.card N)
    {k : ℕ} (h : ∀ y : G ⧸ N, orderOf y = p → k ≤ CFSG.Open.pRank p (Subgroup.centralizer {y})) :
    ∀ x : G, orderOf x = p → k ≤ CFSG.Open.pRank p (Subgroup.centralizer {x}) := by
  intro x hx
  have hπx : orderOf (QuotientGroup.mk' N x) = p := orderOf_mk_eq_prime hN hx
  have hE : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have h1 := h _ hπx
  have e : (QuotientGroup.mk' N '' {x} : Set (G ⧸ N)) = {QuotientGroup.mk' N x} :=
    Set.image_singleton
  rw [← e, pRank_centralizer_image_mk_eq (s := p) hN hN hE
    (by simpa using Subgroup.mem_zpowers x)] at h1
  exact h1

section Equiv

variable {G' : Type*} [Group G']

theorem centralizer_image_mulEquiv (e : G ≃* G') (S : Set G) :
    Subgroup.centralizer (e '' S) = (Subgroup.centralizer S).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have h2 := congrArg e.symm (h (e s) ⟨s, hs, rfl⟩)
    simpa [map_mul] using h2
  · rintro h _ ⟨s, hs, rfl⟩
    have h2 := congrArg e (h s hs)
    simpa [map_mul] using h2

theorem centralizer_map_mulEquiv (e : G ≃* G') (E : Subgroup G) :
    Subgroup.centralizer ((E.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (E : Set G)).map e.toMonoidHom :=
  centralizer_image_mulEquiv e _

theorem pRank_centralizer_image_mulEquiv [Finite G] [Finite G'] [Fact p.Prime] (e : G ≃* G')
    (S : Set G) :
    CFSG.Open.pRank p (Subgroup.centralizer (e '' S)) =
      CFSG.Open.pRank p (Subgroup.centralizer S) := by
  rw [centralizer_image_mulEquiv]
  exact CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p Fact.out e.toMonoidHom
    e.injective _

theorem pRank_centralizer_map_mulEquiv [Finite G] [Finite G'] [Fact p.Prime] (e : G ≃* G')
    (E : Subgroup G) :
    CFSG.Open.pRank p (Subgroup.centralizer ((E.map e.toMonoidHom : Subgroup G') : Set G')) =
      CFSG.Open.pRank p (Subgroup.centralizer (E : Set G)) := by
  rw [centralizer_map_mulEquiv]
  exact CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p Fact.out e.toMonoidHom
    e.injective _

theorem card_centralizer_map_mulEquiv (e : G ≃* G') (E : Subgroup G) :
    Nat.card (Subgroup.centralizer ((E.map e.toMonoidHom : Subgroup G') : Set G')) =
      Nat.card (Subgroup.centralizer (E : Set G)) := by
  rw [centralizer_map_mulEquiv]
  exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective

theorem exists_mem_centralizer_orderOf_eq_map_mulEquiv_iff (e : G ≃* G') (E : Subgroup G)
    (n : ℕ) :
    (∃ y ∈ Subgroup.centralizer ((E.map e.toMonoidHom : Subgroup G') : Set G'),
        orderOf y = n) ↔ ∃ x ∈ Subgroup.centralizer (E : Set G), orderOf x = n := by
  rw [centralizer_map_mulEquiv e E]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, hx, by simpa using hy⟩
  · rintro ⟨x, hx, hn⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, by simpa using hn⟩

theorem le_pRank_centralizer_of_mulEquiv [Finite G] [Finite G'] [Fact p.Prime] (e : G ≃* G')
    {k : ℕ} (h : ∀ y : G', orderOf y = p → k ≤ CFSG.Open.pRank p (Subgroup.centralizer {y})) :
    ∀ x : G, orderOf x = p → k ≤ CFSG.Open.pRank p (Subgroup.centralizer {x}) := by
  intro x hx
  have h1 := h (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)
  have e1 : (e '' {x} : Set G') = {e x} := Set.image_singleton
  rwa [← e1, pRank_centralizer_image_mulEquiv e] at h1

theorem le_pRank_centralizer_of_quotientEquiv [Finite G] [Finite G'] [Fact p.Prime]
    (hN : ¬ p ∣ Nat.card N) (e : G ⧸ N ≃* G') {k : ℕ}
    (h : ∀ y : G', orderOf y = p → k ≤ CFSG.Open.pRank p (Subgroup.centralizer {y})) :
    ∀ x : G, orderOf x = p → k ≤ CFSG.Open.pRank p (Subgroup.centralizer {x}) :=
  le_pRank_centralizer_of_quotient hN (le_pRank_centralizer_of_mulEquiv e h)

theorem pRank_centralizer_image_quotientEquiv [Finite G] [Finite G'] [Fact s.Prime]
    [Fact p.Prime] (hs : ¬ s ∣ Nat.card N) (hp : ¬ p ∣ Nat.card N) (e : G ⧸ N ≃* G')
    {E : Subgroup G} (hE : IsPGroup s E) {S : Set G} (hSE : S ⊆ E) :
    CFSG.Open.pRank p (Subgroup.centralizer (e '' (QuotientGroup.mk' N '' S))) =
      CFSG.Open.pRank p (Subgroup.centralizer S) := by
  rw [pRank_centralizer_image_mulEquiv e, pRank_centralizer_image_mk_eq hs hp hE hSE]

theorem dvd_card_centralizer_map_quotientEquiv_iff [Finite G] [Fact s.Prime] [Fact p.Prime]
    (hs : ¬ s ∣ Nat.card N) (hp : ¬ p ∣ Nat.card N) (e : G ⧸ N ≃* G') {E : Subgroup G}
    (hE : IsPGroup s E) :
    p ∣ Nat.card (Subgroup.centralizer
      (((E.map (QuotientGroup.mk' N)).map e.toMonoidHom : Subgroup G') : Set G')) ↔
      p ∣ Nat.card (Subgroup.centralizer (E : Set G)) := by
  rw [card_centralizer_map_mulEquiv e (E.map (QuotientGroup.mk' N))]
  exact dvd_card_centralizer_map_mk_iff hs hp hE

theorem exists_mem_centralizer_orderOf_eq_prime_map_quotientEquiv [Finite G] [Fact s.Prime]
    [Fact p.Prime] (hs : ¬ s ∣ Nat.card N) (hp : ¬ p ∣ Nat.card N) (e : G ⧸ N ≃* G')
    {E : Subgroup G} (hE : IsPGroup s E) {y : G'}
    (hyC : y ∈ Subgroup.centralizer
      (((E.map (QuotientGroup.mk' N)).map e.toMonoidHom : Subgroup G') : Set G'))
    (hy : orderOf y = p) :
    ∃ x ∈ Subgroup.centralizer (E : Set G), orderOf x = p ∧ e (QuotientGroup.mk' N x) = y := by
  rw [centralizer_map_mulEquiv e _] at hyC
  obtain ⟨yb, hyb, rfl⟩ := hyC
  obtain ⟨x, hx, hxo, rfl⟩ := exists_mem_centralizer_orderOf_eq_prime_mk_eq hs hp hE hyb
    (by simpa using hy)
  exact ⟨x, hx, hxo, rfl⟩

end Equiv

end CFSG.GroupTheory.CoprimeTransport
