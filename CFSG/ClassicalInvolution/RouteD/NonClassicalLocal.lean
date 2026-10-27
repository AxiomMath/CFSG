module

public import CFSG.ClassicalInvolution.RouteD.GapsR2
public import CFSG.ClassicalInvolution.RouteD.TypeELocal
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Standard

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_lieSystemData {Ω : Set (Subgroup G)} (hIH : LocalLieSystems p f Ω) {x : G}
    (hx : ¬ ({x} : Set G) ⊆ Subgroup.center G) :
    Nonempty (LieSystemData p f (locQuot Ω x) (locFamily Ω x)) :=
  hIH {x} hx

theorem mem_centralizingMembers_pair {Ω : Set (Subgroup G)} {L : Subgroup G} {x z : G} :
    L ∈ centralizingMembers Ω {x, z} ↔
      L ∈ centralizingMembers Ω {x} ∧ L ≤ Subgroup.centralizer ({z} : Set G) := by
  have key : ∀ l : G, l ∈ Subgroup.centralizer ({x, z} : Set G) ↔
      l ∈ Subgroup.centralizer ({x} : Set G) ∧ l ∈ Subgroup.centralizer ({z} : Set G) := by
    intro l
    simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨hL, h⟩
    exact ⟨⟨hL, fun l hl => ((key l).mp (h hl)).1⟩, fun l hl => ((key l).mp (h hl)).2⟩
  · rintro ⟨⟨hL, h1⟩, h2⟩
    exact ⟨hL, fun l hl => (key l).mpr ⟨h1 hl, h2 hl⟩⟩

theorem centralizingMembers_pair_eq_inter {Ω : Set (Subgroup G)} (x z : G) :
    centralizingMembers Ω {x, z} =
      centralizingMembers Ω {x} ∩ centralizingMembers Ω {z} := by
  ext L
  rw [mem_centralizingMembers_pair]
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨hx, hx.1, hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, hz.2⟩

theorem le_centralizer_of_commutes {K N : Subgroup G} (h : Commutes N K) {z : G} (hz : z ∈ K) :
    N ≤ Subgroup.centralizer ({z} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h n hn z hz

section Components

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

@[expose] def NCEdge (Ω : Set (Subgroup G)) (x : G) (A B : Subgroup G) : Prop :=
  A ∈ centralizingMembers Ω {x} ∧ B ∈ centralizingMembers Ω {x} ∧ ¬ Commutes A B

@[expose] def Linked (Ω : Set (Subgroup G)) (x : G) : Subgroup G → Subgroup G → Prop :=
  Relation.ReflTransGen (NCEdge Ω x)

omit [Finite G] in
theorem NCEdge.symm {A B : Subgroup G} (h : NCEdge Ω x A B) : NCEdge Ω x B A :=
  ⟨h.2.1, h.1, fun hc => h.2.2 (Gaps.commutes_symm hc)⟩

omit [Finite G] in
theorem Linked.single {A B : Subgroup G} (h : NCEdge Ω x A B) : Linked Ω x A B :=
  Relation.ReflTransGen.single h

omit [Finite G] in
theorem Linked.trans {A B C : Subgroup G} (h₁ : Linked Ω x A B) (h₂ : Linked Ω x B C) :
    Linked Ω x A C :=
  Relation.ReflTransGen.trans h₁ h₂

omit [Finite G] in
theorem Linked.symm {A B : Subgroup G} (h : Linked Ω x A B) : Linked Ω x B A := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (NCEdge.symm hbc) ih

theorem eq_of_not_commutes (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {A B : Subgroup G} {i j : Fin D.card}
    (hA : A ∈ compMembers Ω x D i) (hB : B ∈ compMembers Ω x D j) (hnc : ¬ Commutes A B) :
    i = j := by
  by_contra hij
  exact hnc (commutes_of_ne_comp hΩ hP1 D hij hA hB)

theorem Linked.le_range (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {A B : Subgroup G} (h : Linked Ω x A B)
    {i : Fin D.card} (hA : locImg Ω x A ≤ (D.hom i).range) :
    locImg Ω x B ≤ (D.hom i).range := by
  induction h with
  | refl => exact hA
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, hnc⟩ := hbc
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨c, hc, rfl⟩)
    have := eq_of_not_commutes hΩ hP1 D (A := b) (B := c) ⟨hb, ih⟩ ⟨hc, hj⟩ hnc
    exact this ▸ hj

theorem card_eq_one_of_linked (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {K : Subgroup G} (hK : K ∈ centralizingMembers Ω {x}) {z : G} (hz : z ∈ K)
    (hlink : ∀ R ∈ centralizingMembers Ω {x, z}, Linked Ω x K R) : D.card = 1 := by
  obtain ⟨i₀, hi₀⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K, hK, rfl⟩)
  have hall : ∀ j : Fin D.card, j = i₀ := by
    intro j
    by_contra hj
    obtain ⟨R, -, hmem⟩ := D.meets j
    obtain ⟨N, hN, hNR⟩ := mem_locFamily_iff.mp hmem
    have hNj : locImg Ω x N ≤ (D.hom j).range := hNR ▸ Subgroup.map_le_range _ _
    have hcomm : Commutes N K := commutes_of_ne_comp hΩ hP1 D hj ⟨hN, hNj⟩ ⟨hK, hi₀⟩
    have hvis : N ∈ centralizingMembers Ω {x, z} :=
      mem_centralizingMembers_pair.mpr ⟨hN, le_centralizer_of_commutes hcomm hz⟩
    have hNi : locImg Ω x N ≤ (D.hom i₀).range := (hlink N hvis).le_range hΩ hP1 D hi₀
    exact hj (eq_of_locImg_le_range hΩ hex D hN hNj hNi)
  have hsub : Subsingleton (Fin D.card) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  have h1 : D.card ≤ 1 := Fin.subsingleton_iff_le_one.mp hsub
  have h2 : 0 < D.card := i₀.pos
  omega

omit [Finite G] in
theorem localShapeT_zero_of_card_eq_one {Ω : Set (Subgroup G)} {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (h : D.card = 1) (i₁ : Fin D.card) :
    LocalShapeT p f 0 (D.tag i₁) (D.rank i₁) Ω x :=
  ⟨D, by omega, i₁, rfl, rfl, fun i hi => absurd (Fin.ext (by have := i.2; have := i₁.2; omega)) hi⟩

theorem exists_corr_of_mem (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {K : Subgroup G}
    (hK : K ∈ centralizingMembers Ω {x}) : ∃ (i : Fin D.card) (R : Subgroup
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K), Corr Ω x D i K R := by
  obtain ⟨i, hi⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K, hK, rfl⟩)
  obtain ⟨R, hR⟩ := exists_corr_left hΩ hex D (i := i) ⟨hK, hi⟩
  exact ⟨i, R, hR⟩

omit [Finite G] in
theorem exists_model_elt {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card}
    {K : Subgroup G} {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hK : Corr Ω x D i K R) {z : G} (hz : z ∈ K) :
    ∃ k ∈ R, D.hom i k = locMk Ω x ⟨z, le_centralizingLayer hK.1 hz⟩ := by
  have hKY : z ∈ locLayer Ω x := le_centralizingLayer hK.1 hz
  have hmem : locMk Ω x ⟨z, hKY⟩ ∈ locImg Ω x K := ⟨_, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have e := hK.2.2
  rw [e] at hmem
  obtain ⟨k, hkR, hk⟩ := hmem
  exact ⟨k, hkR, hk⟩

theorem visible_iff_corr (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card}
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K N : Subgroup G} {R R' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hK : Corr Ω x D i K R) (hN : Corr Ω x D i N R') {z : G} (hz : z ∈ K) {k : (modelUniv
      (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hk : D.hom i k = locMk Ω x ⟨z, le_centralizingLayer hK.1 hz⟩) :
    N ∈ centralizingMembers Ω {x, z} ↔ R' ≤ Subgroup.centralizer ({k} : Set _) := by
  rw [mem_centralizingMembers_pair]
  exact ⟨fun h => (corr_le_centralizer_iff hΩ hP1 hperf hN _ k hk).mp h.2,
    fun h => ⟨hN.1, (corr_le_centralizer_iff hΩ hP1 hperf hN _ k hk).mpr h⟩⟩

theorem oddCoverSL3 (hq : 5 ≤ p ^ f) : OddCoverSL3 (GaloisField p f) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  exact CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0}
    (GaloisField.card p f hf) hq

theorem linearBlockStandardPair_of_corr (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card} {N N' : Subgroup G}
    {R R' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (h : Corr Ω x D i N R) (h' : Corr Ω x D i N' R')
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField p f) W R R') :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField p f) W' N N' := by
  obtain ⟨W, hW⟩ := hpair
  have h1 := linearBlockStandardPair_map_central hW (D.hom i) (D.ker_le_center i)
  rw [← h.2.2, ← h'.2.2] at h1
  exact linearBlockStandardPair_of_locImg (by omega) (oddCoverSL3 hq) hΩ hP1 h.1 h'.1 h1

end Components

end CFSG.ClassicalInvolution.RouteD.NonClassical
