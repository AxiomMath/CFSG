module

public import CFSG.ClassicalInvolution.Balance.PassTwo
public import CFSG.ClassicalInvolution.Generic.InductionLocal

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

@[expose] def InCommonComponent (x : G) (K L : Subgroup G) : Prop :=
  ∃ Q : Subgroup (OddQuot x), CFSG.IsComponent Q ∧ modOdd x K ≤ Q ∧ modOdd x L ≤ Q

@[expose] def FrameMeetsAt (Ω : Set (Subgroup G)) (E : Subgroup G) (S : Set (Subgroup G))
    (x : G) : Prop :=
  ∀ K ∈ centMembers Ω x, ∃ L₀ ∈ S, x ∈ axisSub E L₀ ∧ InCommonComponent x K L₀

@[expose] def FrameMeetsComponents (Ω : Set (Subgroup G)) (E : Subgroup G) (S : Set (Subgroup G))
    (x : G) : Prop :=
  ∀ Q : Subgroup (OddQuot x), CFSG.IsComponent Q → Q ≤ memberJoin Ω x →
    ∃ L₀ ∈ S, x ∈ axisSub E L₀ ∧ modOdd x L₀ ≤ Q

theorem frameMeetsAt_of_frameMeetsComponents (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {S : Set (Subgroup G)} {x : G} (hxne : ¬ ({x} : Set G) ⊆ Subgroup.center G)
    (h : FrameMeetsComponents Ω E S x) : FrameMeetsAt Ω E S x := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH hxne
  have := memberJoin_normal (a := x) hΩ.conjInvariant
  intro K hK
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨K, hK, rfl⟩ : modOdd x K ∈ memberImages Ω x)
  obtain ⟨L₀, hL₀S, hxax, hL₀i⟩ := h (D.Q i) ((CFSG.isComponent_iff_open _).mpr (D.isComponentOf i))
    (D.le_join i)
  exact ⟨L₀, hL₀S, hxax, D.Q i, (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i), hi, hL₀i⟩

theorem frameMeetsAt_of_covers (hp2 : p ≠ 2) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {S : Set (Subgroup G)} (hSΩ : S ⊆ Ω)
    {x : G} (hxE : x ∈ E) (hxne : ¬ ({x} : Set G) ⊆ Subgroup.center G)
    (hcov : ∀ L ∈ centMembers Ω x, ∃ K ∈ S, K ≤ Subgroup.centralizer ({x} : Set G) ∧
      ∃ a ∈ L, ∃ b ∈ K, a * b * a⁻¹ * b⁻¹ ∉ oddCoreIn (centLayer Ω x)) :
    FrameMeetsAt Ω E S x := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH hxne
  have := memberJoin_normal (a := x) hΩ.conjInvariant
  intro L hL
  obtain ⟨K, hKS, hKC, a, ha, b, hb, hnot⟩ := hcov L hL
  refine ⟨K, hKS, mem_axisSub_iff.mpr ⟨hxE, fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk))⟩, ?_⟩
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨L, hL, rfl⟩ : modOdd x L ∈ memberImages Ω x)
  obtain ⟨j, hj⟩ := D.exists_le _
    (⟨K, ⟨hSΩ hKS, hKC⟩, rfl⟩ : modOdd x K ∈ memberImages Ω x)
  have hij : i = j := by
    by_contra hne
    refine hnot ?_
    have haY : a ∈ centLayer Ω x := le_centLayer hL ha
    have hbY : b ∈ centLayer Ω x := le_centLayer ⟨hSΩ hKS, hKC⟩ hb
    have hcomm : layerToOddQuot Ω x ⟨a, haY⟩ * layerToOddQuot Ω x ⟨b, hbY⟩ =
        layerToOddQuot Ω x ⟨b, hbY⟩ * layerToOddQuot Ω x ⟨a, haY⟩ :=
      D.commute i j hne _ (hi ⟨⟨a, hL.2 ha⟩, ha, rfl⟩) _ (hj ⟨⟨b, hKC hb⟩, hb, rfl⟩)
    have hker : (⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹ : ↥(centLayer Ω x)) ∈
        (layerToOddQuot Ω x).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    rw [ker_layerToOddQuot hΩ.conjInvariant] at hker
    exact ⟨_, hker, rfl⟩
  subst hij
  exact ⟨D.Q i, (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i), hi, hj⟩

omit [Finite G] in
theorem commutator_subgroupOf_eq_top {C K : Subgroup G} (hKC : K ≤ C) (hK : Group.IsPerfect ↥K) :
    commutator ↥(K.subgroupOf C) = ⊤ := by
  have : Group.IsPerfect ↥(K.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKC).symm.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem member_commutes_oddCore [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakPreFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 E, deltaCore Φ = ⊥) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1)
    {K : Subgroup G} (hK : K ∈ centMembers Ω x) {L₀ : Subgroup G} (hL₀S : L₀ ∈ S)
    (hxax : x ∈ axisSub E L₀) (hcc : InCommonComponent x K L₀) :
    ∀ d ∈ componentClassificationOddCore ↥(centLayer Ω x), ∀ k ∈ K, (d : G) * k = k * d := by
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hxne : ¬ ({x} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hx1
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH hxne
  have := memberJoin_normal (a := x) hΩ.conjInvariant
  obtain ⟨-, hxc⟩ := mem_axisSub_iff.mp hxax
  have hL₀Ω : L₀ ∈ Ω := Fr.subset hL₀S
  have hL₀C : L₀ ≤ C := fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hxc l hl)
  have hKmem : modOdd x K ∈ memberImages Ω x := ⟨K, hK, rfl⟩
  have hL₀mem : modOdd x L₀ ∈ memberImages Ω x := ⟨L₀, ⟨hL₀Ω, hL₀C⟩, rfl⟩
  obtain ⟨i, hi⟩ := D.exists_le _ hKmem
  obtain ⟨Q, hQcomp, hKQ, hL₀Q⟩ := hcc
  obtain ⟨z₁, hz₁⟩ := hΩ.classical K hK.1
  obtain ⟨hKbperf, hKbne⟩ := modOdd_perfect_ne_bot hz₁ hK.2
  have hQeq : Q = D.Q i := eq_of_isComponentOf_of_perfect_le
    ((CFSG.isComponent_iff_open Q).mp hQcomp) (D.isComponentOf i) hKbperf hKbne hKQ hi
  have hj : modOdd x L₀ ≤ D.Q i := hQeq ▸ hL₀Q
  obtain ⟨lift, hlift, hliftmap⟩ := TwoComponents.exists_lift (D.Q i) (D.isComponentOf i)
  obtain ⟨z₀, hz₀E, hz₀⟩ := Fr.exists_weakMember hL₀S
  have hKperf := hz₁.perfect
  have hL₀perf := hz₀.perfect
  have hKle : K.subgroupOf C ≤ lift :=
    le_of_perfect_of_map_le hlift (commutator_subgroupOf_eq_top hK.2 hKperf)
      (by rw [hliftmap]; exact hi)
  have hL₀le : L₀.subgroupOf C ≤ lift :=
    le_of_perfect_of_map_le hlift (commutator_subgroupOf_eq_top hL₀C hL₀perf)
      (by rw [hliftmap]; exact hj)
  set P : Subgroup G := lift.map C.subtype with hP
  have hPC : P ≤ C := Subgroup.map_subtype_le lift
  have hPsub : P.subgroupOf C = lift := subgroupOf_map_subtype_self C lift
  have hL₀P : L₀ ≤ P := fun l hl =>
    ⟨⟨l, hL₀C hl⟩, hL₀le (Subgroup.mem_subgroupOf.mpr hl), rfl⟩
  have hx2 : x * x = 1 := Fr.elem x hxE
  have htL : ∀ l ∈ L₀, x * l = l * x := fun l hl => (hxc l hl).symm
  have hPq : CFSG.Open.IsQuasisimple ↥P :=
    isQuasisimple_of_weakFrame Fr h16 hΔ hL₀S hz₀ hxax hPC (by rw [hPsub]; exact hlift) hL₀P
      fun f₀ hf₀ hf₀1 M hM => by
        obtain ⟨hf₀E, hf₀c⟩ := mem_axisSub_iff.mp hf₀
        exact hB_of_localLieSystems_of_centralizes hp2 h0 hA1 hΩ hIH hL₀Ω hx2 hx1 htL
          (not_subset_center_of_ne_one hnab hf₀1)
          (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hf₀c l hl))
          (Fr.comm hxE hf₀E) M hM
  have hq : CFSG.Open.IsQuasisimple ↥lift :=
    Components.quasisimple_of_equiv (lift.equivMapOfInjective C.subtype C.subtype_injective) hPq
  have hcomp : IsComponentOf lift ⊤ := ⟨le_top, hlift.1, hq⟩
  have hsolv : Group.IsSolvable ↥(componentClassificationOddCore ↥C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (OddCore.odd_card _)
  have hOsub : IsSubnormal (componentClassificationOddCore ↥C) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hcommlift := LocalComponents.commutes_with_solvable_subnormal lift _ hcomp hOsub
  intro d hd k hk
  have hdO : Subgroup.inclusion (centLayer_le_centralizer Ω x) d ∈
      componentClassificationOddCore ↥C := map_inclusion_oddCore_le hΩ.conjInvariant ⟨d, hd, rfl⟩
  have hk' : (⟨k, hK.2 hk⟩ : ↥C) ∈ lift := hKle (Subgroup.mem_subgroupOf.mpr hk)
  have hmem := Subgroup.commutator_mem_commutator hk' hdO
  rw [hcommlift, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact (congrArg Subtype.val hmem).symm

theorem localOddCentral_of_localLieSystems [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hmeet : FrameMeetsAt Ω E S x) : LocalOddCentral Ω {x} := by
  have hΔ := deltaCore_eq_bot_of_localLieSystems hnab hp2 h0 hA1 hΩ hIH Fr h16 hGen hlay
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro y
  by_cases hne : (centMembers Ω x).Nonempty
  · have hgen := (inClass_local hΩ {x} hne).generated
    have hle : (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) ≤
        Subgroup.centralizer ({d} : Set ↥(centralizingLayer Ω {x})) := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨K, hK, hKY, rfl⟩ := hL
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨L₀, hL₀S, hxax, hcc⟩ := hmeet K hK
      exact Subtype.ext (member_commutes_oddCore hnab hp2 h0 hA1 hΩ hIH Fr.toWeakPreFrame h16 hΔ
        hxE hx1 hK hL₀S hxax hcc d hd k (Subgroup.mem_subgroupOf.mp hk)).symm
    have hy : y ∈ (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) :=
      hgen ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  · have hY : centLayer Ω x = ⊥ := by
      refine le_bot_iff.mp (centLayer_le fun L hL => ?_)
      exact absurd ⟨L, hL⟩ hne
    have htriv : ∀ z : ↥(centLayer Ω x), z = 1 := fun z =>
      Subtype.ext (by
        have := z.2
        simpa only [hY, Subgroup.mem_bot, Subgroup.coe_one] using this)
    rw [htriv y, htriv d]

theorem localOddCentral_of_central_involution [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) {K : Subgroup G} (hK : K ∈ S) {z : G}
    (hz : IsCentralInvolution K z) (hmeet : FrameMeetsAt Ω E S z) : LocalOddCentral Ω {z} :=
  localOddCentral_of_localLieSystems hnab hp2 h0 hA1 hΩ hIH Fr h16 hGen hlay
    (Fr.toWeakPreFrame.mem_of_central hK hz) hz.ne_one hmeet

@[expose] def Stage2 (Ω : Set (Subgroup G)) (X₂ : Set G) : Prop :=
  ExactMembers Ω ∧ ∀ x ∈ X₂, LocalOddCentral Ω {x}

theorem stage2_of_localLieSystems [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} :=
  ⟨exactMembers_of_localLieSystems hnab hp2 hf h9 h0 hA1 hΩ hsingle hIH Fr h16 hGen hlay,
    fun _ ⟨hxE, hx1, hmeet⟩ =>
      localOddCentral_of_localLieSystems hnab hp2 h0 hA1 hΩ hIH Fr h16 hGen hlay hxE hx1 hmeet⟩

end CFSG.ClassicalInvolution.Balance
