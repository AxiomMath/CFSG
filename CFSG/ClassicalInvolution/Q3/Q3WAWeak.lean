module

public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups

structure LocCtx3 {G : Type} [Group G] (K : Subgroup G) (z : G) : Prop where
  hΩ : InClass3 (conjClass3 K)
  hconn : RouteD.DeltaConnected (conjClass3 K)
  hex : ExactMembers3 (conjClass3 K)
  hP1 : LocalOddCentral (conjClass3 K) {z}
  hO3 : LocalOddThreeFree3 (conjClass3 K) z
  hz : IsClassicalMember3 K z

section Plain

variable {G : Type} [Group G]

theorem ne_bot_of_mem3 {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) : ∀ L ∈ Ω, L ≠ ⊥ := by
  intro L hL hbot
  obtain ⟨w, hw⟩ := hΩ.classical L hL
  have := hw.mem
  rw [hbot, Subgroup.mem_bot] at this
  have h2 := hw.orderOf_eq_two
  rw [this, orderOf_one] at h2
  omega

theorem single_class3 (K : Subgroup G) : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
  rintro L ⟨g, rfl⟩
  exact ⟨g, rfl⟩

theorem commutes_reflTransGen_of_connected3 {K : Subgroup G}
    (hconn : RouteD.DeltaConnected (conjClass3 K)) :
    ∀ X ∈ conjClass3 K, ∀ Y ∈ conjClass3 K, Relation.ReflTransGen
      (fun A B : Subgroup G => A ∈ conjClass3 K ∧ B ∈ conjClass3 K ∧ Commutes A B) X Y := by
  intro X hX Y hY
  have hreach := hconn.preconnected ⟨X, hX⟩ ⟨Y, hY⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ v : conjClass3 K, Relation.ReflTransGen
      (CFSG.ClassicalInvolution.Models.commGraph (conjClass3 K)).Adj ⟨X, hX⟩ v →
      Relation.ReflTransGen
        (fun A B : Subgroup G => A ∈ conjClass3 K ∧ B ∈ conjClass3 K ∧ Commutes A B) X
        (v : Subgroup G) := by
    intro v hv
    induction hv with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      exact ih.tail ⟨b.2, c.2, (CFSG.ClassicalInvolution.Models.commGraph_adj.mp hbc).2⟩
  exact key ⟨Y, hY⟩ hreach

end Plain

section Weak



variable {G : Type} [Group G] [Finite G] {ι : Type}

theorem quasi_or_a1_3 {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData3 ι X Φ)
    (i : ι) : CFSG.Open.IsQuasisimple (D.kind i).G ∨ IsA1Comp3 D i := by
  by_cases h : IsA1Comp3 D i
  · exact Or.inr h
  · exact Or.inl (isQuasisimple_of_not_a1 D h)

theorem exists_maximal_block3 (hMFZ : RouteD.Gaps.FundNoncentral 3) {K : Subgroup G} {z : G}
    (hc : LocCtx3 K z)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    (hmulti : ∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j) :
    ∃ (A₀ : Subgroup G) (i₀ i' : ι) (a₂ : Subgroup G),
      A₀ ∈ centralizingMembers (conjClass3 K) {z} ∧
      (∀ A ∈ centralizingMembers (conjClass3 K) {z},
        (ncBlock (conjClass3 K) z A).ncard ≤ (ncBlock (conjClass3 K) z A₀).ncard) ∧
      ncBlock (conjClass3 K) z A₀ = compMembers3 (conjClass3 K) z D i₀ ∧
      ¬ IsA1Comp3 D i₀ ∧ ¬ IsA1Comp3 D i' ∧ i' ≠ i₀ ∧
      a₂ ∈ compMembers3 (conjClass3 K) z D i' ∧
      K ∉ compMembers3 (conjClass3 K) z D i₀ ∧
      (∀ B ∈ compMembers3 (conjClass3 K) z D i₀, Commutes K B ∧ Commutes a₂ B) ∧
      Commutes K a₂ := by
  have hΩ := hc.hΩ
  have hex := hc.hex
  have hP1 := hc.hP1
  have hO3 := hc.hO3
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hK, isSubnormal_le hc.hz.subnormal⟩
  obtain ⟨A₀, hA₀, hmax⟩ : ∃ A₀ ∈ centralizingMembers (conjClass3 K) {z},
      ∀ A ∈ centralizingMembers (conjClass3 K) {z},
        (ncBlock (conjClass3 K) z A).ncard ≤ (ncBlock (conjClass3 K) z A₀).ncard :=
    Set.exists_max_image _ (fun A => (ncBlock (conjClass3 K) z A).ncard) (Set.toFinite _)
      ⟨K, hKz⟩
  obtain ⟨i₀, hi₀, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hA₀
  have hblock : ∀ i : ι, ∀ N ∈ compMembers3 (conjClass3 K) z D i,
      ncBlock (conjClass3 K) z N = compMembers3 (conjClass3 K) z D i := by
    intro i N hN
    ext B
    exact linked_iff_mem_compMembers3 hΩ hex hP1 hO3 (quasi_or_a1_3 D i) hN
  have hsize : ∀ i : ι, ¬ IsA1Comp3 D i →
      1 < (compMembers3 (conjClass3 K) z D i).ncard := by
    intro i hi
    obtain ⟨N, N', hN, hN', hne⟩ := exists_ne_of_not_isA1Comp3 hΩ hex hP1 hO3 hi
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨N, hN, N', hN', hne⟩
  have hle : ∀ i : ι, ∀ N ∈ compMembers3 (conjClass3 K) z D i,
      (compMembers3 (conjClass3 K) z D i).ncard ≤
        (compMembers3 (conjClass3 K) z D i₀).ncard := by
    intro i N hN
    have := hmax N hN.1
    rwa [hblock i N hN, hblock i₀ A₀ hi₀] at this
  obtain ⟨i, j, hij, hi, hj⟩ := hmulti
  obtain ⟨Ni, hNi⟩ := exists_mem_compMembers3 (D := D) (x := z) (Ω := conjClass3 K) i
  have hi₀na : ¬ IsA1Comp3 D i₀ := by
    intro hA1
    have h1 := hsize i hi
    have h2 := hle i Ni hNi
    have h3 : (compMembers3 (conjClass3 K) z D i₀).ncard ≤ 1 :=
      (Set.ncard_le_one_iff (Set.toFinite _)).mpr fun {a b} ha hb =>
        eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA1 ha hb
    omega
  obtain ⟨i', hi'na, hi'ne⟩ : ∃ i' : ι, ¬ IsA1Comp3 D i' ∧ i' ≠ i₀ := by
    by_cases hii : i = i₀
    · exact ⟨j, hj, fun e => hij (hii.trans e.symm)⟩
    · exact ⟨i, hi, hii⟩
  obtain ⟨iK, hKA1, hKimg⟩ := locImg_eq_range_of_involution3 (D := D) hMFZ hKz hc.hz
  have hKmem : K ∈ compMembers3 (conjClass3 K) z D iK := ⟨hKz, hKimg.le⟩
  have hiKi₀ : iK ≠ i₀ := fun e => hi₀na (e ▸ hKA1)
  have hiKi' : iK ≠ i' := fun e => hi'na (e ▸ hKA1)
  obtain ⟨a₂, ha₂⟩ := exists_mem_compMembers3 (D := D) (x := z) (Ω := conjClass3 K) i'
  refine ⟨A₀, i₀, i', a₂, hA₀, hmax, hblock i₀ A₀ hi₀, hi₀na, hi'na, hi'ne, ha₂, ?_,
    fun B hB => ⟨commutes_of_ne_comp3 hΩ hex hP1 hO3 D hiKi₀ hKmem hB,
      commutes_of_ne_comp3 hΩ hex hP1 hO3 D hi'ne ha₂ hB⟩,
    commutes_of_ne_comp3 hΩ hex hP1 hO3 D hiKi' hKmem ha₂⟩
  intro hKi₀
  exact hiKi₀ (eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hKz hKmem.2 hKi₀.2)

theorem exists_weak_star_nbr3 (hMFZ : RouteD.Gaps.FundNoncentral 3) [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hc : LocCtx3 K z)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    (hmulti : ∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j) :
    ∃ (i₁ i₂ : ι) (a₁ a₂ c' q : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp3 D i₁ ∧
      ¬ IsA1Comp3 D i₂ ∧ a₁ ∈ compMembers3 (conjClass3 K) z D i₁ ∧
      c' ∈ compMembers3 (conjClass3 K) z D i₁ ∧
      a₂ ∈ compMembers3 (conjClass3 K) z D i₂ ∧ q ∈ conjClass3 K ∧ Commutes K a₁ ∧
      Commutes K a₂ ∧ Commutes a₁ a₂ ∧ Commutes K c' ∧ Commutes c' a₂ ∧ Commutes q c' ∧
      ¬ Commutes q K ∧ ¬ Commutes q a₁ ∧ ¬ Commutes q a₂ := by
  have hΩ := hc.hΩ
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hconn := commutes_reflTransGen_of_connected3 hc.hconn
  obtain ⟨A₀, i₀, i', a₂, hA₀, hmax, hblock, hi₀na, hi'na, hi'ne, ha₂, hKV, hKc, hKa₂⟩ :=
    exists_maximal_block3 hMFZ hc D hmulti
  have hne := ne_bot_of_mem3 hΩ
  obtain ⟨q, hqΩ, hqV, ⟨a₁, ha₁V, hqa₁⟩, ⟨c', hcV, hqc⟩, hqK, hqcl⟩ :=
    exists_not_commuting_nbr_of_max hnab hΩ.conjInvariant hΩ.generated hne hK
      hc.hz.mem (single_class3 K) hconn hA₀ hmax (hblock ▸ hKV)
      (fun B hB => (hKc B (hblock ▸ hB)).1)
  rw [hblock] at ha₁V hcV hqcl
  exact ⟨i₀, i', a₁, a₂, c', q, fun e => hi'ne e.symm, hi₀na, hi'na, ha₁V, hcV, ha₂, hqΩ,
    (hKc a₁ ha₁V).1, hKa₂, Gaps.commutes_symm (hKc a₁ ha₁V).2, (hKc c' hcV).1,
    Gaps.commutes_symm (hKc c' hcV).2, hqc, hqK, hqa₁, hqcl a₂ ha₂.1.1 fun B hB => (hKc B hB).2⟩

theorem exists_weak_star_common_nbr3 (hMFZ : RouteD.Gaps.FundNoncentral 3) [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hc : LocCtx3 K z)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    (hmulti : ∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j)
    (hconnV : ∀ i : ι, ¬ IsA1Comp3 D i → ∀ A ∈ compMembers3 (conjClass3 K) z D i,
      ∀ B ∈ compMembers3 (conjClass3 K) z D i, Relation.ReflTransGen
        (fun X Y : Subgroup G => X ∈ compMembers3 (conjClass3 K) z D i ∧
          Y ∈ compMembers3 (conjClass3 K) z D i ∧ Commutes X Y) A B) :
    ∃ (i₁ i₂ : ι) (a₁ a₂ c' q : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp3 D i₁ ∧
      ¬ IsA1Comp3 D i₂ ∧ a₁ ∈ compMembers3 (conjClass3 K) z D i₁ ∧
      c' ∈ compMembers3 (conjClass3 K) z D i₁ ∧
      a₂ ∈ compMembers3 (conjClass3 K) z D i₂ ∧ q ∈ conjClass3 K ∧ Commutes K a₁ ∧
      Commutes K a₂ ∧ Commutes a₁ a₂ ∧ Commutes K c' ∧ Commutes c' a₂ ∧ Commutes c' a₁ ∧
      Commutes q c' ∧ ¬ Commutes q K ∧ ¬ Commutes q a₁ ∧ ¬ Commutes q a₂ := by
  have hΩ := hc.hΩ
  have hex := hc.hex
  have hP1 := hc.hP1
  have hO3 := hc.hO3
  obtain ⟨i₁, i₂, a₁, a₂, c', q, hne, hn₁, hn₂, ha₁, hc', ha₂, hq, hKa₁, hKa₂, ha₁a₂, hKc, hca₂,
    hqc, hqK, hqa₁, hqa₂⟩ := exists_weak_star_nbr3 hMFZ hnab hc D hmulti
  obtain ⟨c'', hc'', a', ha', hca', hqc', hqa'⟩ := RouteD.exists_commuting_pair_of_chain
    (hconnV i₁ hn₁) hc' hqc ha₁ hqa₁
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hK, isSubnormal_le hc.hz.subnormal⟩
  have hcomm : ∀ {B : Subgroup G}, B ∈ compMembers3 (conjClass3 K) z D i₁ →
      Commutes K B ∧ Commutes B a₂ := by
    intro B hB
    obtain ⟨iK, hKA1, hKimg⟩ := locImg_eq_range_of_involution3 (D := D) hMFZ hKz hc.hz
    have hKmem : K ∈ compMembers3 (conjClass3 K) z D iK := ⟨hKz, hKimg.le⟩
    have hiK : iK ≠ i₁ := fun e => hn₁ (e ▸ hKA1)
    exact ⟨commutes_of_ne_comp3 hΩ hex hP1 hO3 D hiK hKmem hB,
      commutes_of_ne_comp3 hΩ hex hP1 hO3 D hne hB ha₂⟩
  exact ⟨i₁, i₂, a', a₂, c'', q, hne, hn₁, hn₂, ha', hc'', ha₂, hq, (hcomm ha').1, hKa₂,
    (hcomm ha').2, (hcomm hc'').1, (hcomm hc'').2, hca', hqc', hqK, hqa', hqa₂⟩

end Weak

end CFSG.ClassicalInvolution.Q3.Q3W
