module

public import CFSG.ClassicalInvolution.Q3.TL3C3

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Graph

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {A : Subgroup G → Subgroup G → Prop}

@[expose] def IsMaxOrb (A : Subgroup G → Subgroup G → Prop) (K : Subgroup G)
    (P : Set (Subgroup G)) : Prop :=
  (∃ J, A K J ∧ orbOf A K J = P) ∧ ∀ J, A K J → (orbOf A K J).ncard ≤ P.ncard

@[expose] def maxOrbs (A : Subgroup G → Subgroup G → Prop) (K : Subgroup G) :
    Set (Set (Subgroup G)) :=
  {P | IsMaxOrb A K P}

structure GraphFam (Ω : Set (Subgroup G)) (A : Subgroup G → Subgroup G → Prop) : Prop where
  graph : OrbitGraph A
  mem : ∀ {K J : Subgroup G}, A K J → K ∈ Ω
  conjMem : ∀ K ∈ Ω, ∀ g : G, conjSub g K ∈ Ω
  trans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g ∈ ⨆ L ∈ Ω, L, conjSub g K = J
  conn : ∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen A K J

variable {Ω : Set (Subgroup G)} (hF : GraphFam Ω A)
include hF

omit hF in
theorem exists_isMaxOrb {K J : Subgroup G} (hKJ : A K J) : ∃ P, IsMaxOrb A K P := by
  set T : Set (Set (Subgroup G)) := {P | ∃ J, A K J ∧ orbOf A K J = P} with hT
  have hne : T.Nonempty := ⟨_, J, hKJ, rfl⟩
  obtain ⟨P, ⟨J', hKJ', rfl⟩, hmax⟩ := Set.exists_max_image T Set.ncard (Set.toFinite T) hne
  exact ⟨_, ⟨J', hKJ', rfl⟩, fun J'' hJ'' => hmax _ ⟨J'', hJ'', rfl⟩⟩

omit [Finite G] in
theorem isMaxOrb_conj {K : Subgroup G} {P : Set (Subgroup G)} (hP : IsMaxOrb A K P) (g : G) :
    IsMaxOrb A (conjSub g K) (conjSub g '' P) := by
  obtain ⟨⟨J, hKJ, rfl⟩, hmax⟩ := hP
  refine ⟨⟨conjSub g J, hF.graph.conj g hKJ, orbOf_conj hF.graph K J g⟩, fun J' hJ' => ?_⟩
  have h1 : A K (conjSub g⁻¹ J') := by
    have := hF.graph.conj g⁻¹ hJ'
    rwa [conjSub_inv_conjSub] at this
  have h2 := hmax _ h1
  have h3 := ncard_orbOf_conj hF.graph K (conjSub g⁻¹ J') g
  rw [conjSub_conjSub_inv] at h3
  rw [h3, Set.ncard_image_of_injective _ (conjSub_injective g)]
  exact h2

omit [Finite G] in
theorem ncard_eq_of_isMaxOrb {x v : Subgroup G} (hx : x ∈ Ω) (hv : v ∈ Ω)
    {P Q : Set (Subgroup G)} (hP : IsMaxOrb A x P) (hQ : IsMaxOrb A v Q) : P.ncard = Q.ncard := by
  obtain ⟨g, -, rfl⟩ := hF.trans x hx v hv
  have hP' := isMaxOrb_conj hF hP g
  rw [← Set.ncard_image_of_injective P (conjSub_injective g)]
  obtain ⟨⟨J, hJ, rfl⟩, hmaxQ⟩ := hQ
  obtain ⟨⟨J', hJ', hJ'eq⟩, hmaxP⟩ := hP'
  apply le_antisymm
  · rw [← hJ'eq]
    exact hmaxQ J' hJ'
  · exact hmaxP J hJ

theorem ncard_orbOf_le_of_isMaxOrb {x v : Subgroup G} (hx : x ∈ Ω) {P : Set (Subgroup G)}
    (hP : IsMaxOrb A x P) {J' : Subgroup G} (hvJ' : A v J') : (orbOf A v J').ncard ≤ P.ncard := by
  obtain ⟨Q, hQ⟩ := exists_isMaxOrb hvJ'
  rw [ncard_eq_of_isMaxOrb hF hx (hF.mem hvJ') hP hQ]
  exact hQ.2 J' hvJ'

theorem isMaxOrb_of_adj_all {x v : Subgroup G} (hx : x ∈ Ω) {P : Set (Subgroup G)}
    (hP : IsMaxOrb A x P) (hv : ∀ M ∈ P, A v M) :
    IsMaxOrb A v P ∧ ∀ J ∈ P, orbOf A v J = P := by
  obtain ⟨⟨J, hxJ, rfl⟩, hmax⟩ := hP
  have hP' : IsMaxOrb A x (orbOf A x J) := ⟨⟨J, hxJ, rfl⟩, hmax⟩
  have hJM : ∀ M ∈ orbOf A x J, orbOf A v M = orbOf A x J := by
    intro M hM
    have h1 : orbOf A v J = orbOf A x J := orbOf_eq_of_adj_all hF.graph hxJ hv
      (fun J' hJ' => ncard_orbOf_le_of_isMaxOrb hF hx hP' hJ')
    rw [← h1, orbOf_eq_of_mem (h1 ▸ hM)]
  refine ⟨⟨⟨J, hv J (mem_orbOf_self x J), hJM J (mem_orbOf_self x J)⟩, fun J' hJ' =>
    ncard_orbOf_le_of_isMaxOrb hF hx hP' hJ'⟩, hJM⟩

omit [Finite G] in
theorem adj_of_mem_isMaxOrb {K : Subgroup G} {P : Set (Subgroup G)} (hP : IsMaxOrb A K P)
    {M : Subgroup G} (hM : M ∈ P) : A K M := by
  obtain ⟨⟨J, hKJ, rfl⟩, -⟩ := hP
  exact adj_of_mem_orbOf hF.graph hKJ hM

omit [Finite G] in
theorem not_mem_of_isMaxOrb {K : Subgroup G} {P : Set (Subgroup G)} (hP : IsMaxOrb A K P) :
    K ∉ P := fun h => hF.graph.irrefl K (adj_of_mem_isMaxOrb hF hP h)

omit [Finite G] hF in
theorem orbOf_eq_of_mem_isMaxOrb {K : Subgroup G} {P : Set (Subgroup G)} (hP : IsMaxOrb A K P)
    {J : Subgroup G} (hJ : J ∈ P) : orbOf A K J = P := by
  obtain ⟨⟨J₀, -, rfl⟩, -⟩ := hP
  exact orbOf_eq_of_mem hJ

omit [Finite G] in
theorem maxOrbs_conj (K : Subgroup G) (g : G) :
    maxOrbs A (conjSub g K) = (fun P => conjSub g '' P) '' maxOrbs A K := by
  ext P
  constructor
  · intro hP
    refine ⟨conjSub g⁻¹ '' P, ?_, ?_⟩
    · have := isMaxOrb_conj hF hP g⁻¹
      rwa [conjSub_inv_conjSub] at this
    · show conjSub g '' (conjSub g⁻¹ '' P) = P
      rw [Set.image_image]
      simp [conjSub_conjSub_inv]
  · rintro ⟨P', hP', rfl⟩
    exact isMaxOrb_conj hF hP' g

omit [Finite G] in
theorem ncard_maxOrbs_eq {x v : Subgroup G} (hx : x ∈ Ω) (hv : v ∈ Ω) :
    (maxOrbs A v).ncard = (maxOrbs A x).ncard := by
  obtain ⟨g, -, rfl⟩ := hF.trans x hx v hv
  rw [maxOrbs_conj hF]
  refine Set.ncard_image_of_injective _ ?_
  intro P P' h
  exact (Set.image_injective.mpr (conjSub_injective g)) h

theorem maxOrbs_eq_of_nonmax {K J : Subgroup G} (hKJ : A K J)
    (hnm : orbOf A K J ∉ maxOrbs A K) : maxOrbs A J = maxOrbs A K := by
  have hK : K ∈ Ω := hF.mem hKJ
  have hJ : J ∈ Ω := hF.mem (hF.graph.symm hKJ)
  have hsub : maxOrbs A K ⊆ maxOrbs A J := by
    intro P hP
    have hadj : ∀ M ∈ P, A J M := by
      intro M hM
      have hKM : A K M := adj_of_mem_isMaxOrb hF hP hM
      refine hF.graph.sep hKJ hKM fun hMJ => hnm ?_
      rw [← orbOf_eq_of_mem hMJ, orbOf_eq_of_mem_isMaxOrb hP hM]
      exact hP
    exact (isMaxOrb_of_adj_all hF hK hP hadj).1
  exact (Set.eq_of_subset_of_ncard_le hsub (ncard_maxOrbs_eq hF hK hJ).le
    (Set.toFinite _)).symm

theorem mem_maxOrbs_of_ne {K J : Subgroup G} (hKJ : A K J) {P' : Set (Subgroup G)}
    (hP' : P' ∈ maxOrbs A K) (hne : P' ≠ orbOf A K J) :
    P' ∈ maxOrbs A J := by
  have hK : K ∈ Ω := hF.mem hKJ
  have hadj : ∀ M ∈ P', A J M := by
    intro M hM
    have hKM : A K M := adj_of_mem_isMaxOrb hF hP' hM
    refine hF.graph.sep hKJ hKM fun hMJ => hne ?_
    rw [← orbOf_eq_of_mem_isMaxOrb hP' hM, orbOf_eq_of_mem hMJ]
  exact (isMaxOrb_of_adj_all hF hK hP' hadj).1

omit [Finite G] in
theorem orbOf_not_mem_maxOrbs (K J : Subgroup G) :
    orbOf A J K ∉ maxOrbs A K := fun h =>
  not_mem_of_isMaxOrb hF h (mem_orbOf_self J K)

theorem orbOf_mem_maxOrbs {K J : Subgroup G} (hKJ : A K J) (hP : orbOf A K J ∈ maxOrbs A K) :
    orbOf A J K ∈ maxOrbs A J := by
  by_contra hnm
  have h1 := maxOrbs_eq_of_nonmax hF (hF.graph.symm hKJ) hnm
  rw [h1] at hP
  exact not_mem_of_isMaxOrb hF hP (mem_orbOf_self K J)

theorem maxOrbs_eq_insert {K J : Subgroup G} (hKJ : A K J) (hP : orbOf A K J ∈ maxOrbs A K) :
    maxOrbs A J = insert (orbOf A J K) (maxOrbs A K \ {orbOf A K J}) := by
  have hK : K ∈ Ω := hF.mem hKJ
  have hJ : J ∈ Ω := hF.mem (hF.graph.symm hKJ)
  have hsub : insert (orbOf A J K) (maxOrbs A K \ {orbOf A K J}) ⊆ maxOrbs A J := by
    refine Set.insert_subset (orbOf_mem_maxOrbs hF hKJ hP) fun P' hP' => ?_
    exact mem_maxOrbs_of_ne hF hKJ hP'.1 hP'.2
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  have hnot : orbOf A J K ∉ maxOrbs A K \ {orbOf A K J} := fun h =>
    orbOf_not_mem_maxOrbs hF K J h.1
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_sdiff_singleton_add_one hP,
    ncard_maxOrbs_eq hF hK hJ]

end CFSG.ClassicalInvolution.Q3.TC.Graph
