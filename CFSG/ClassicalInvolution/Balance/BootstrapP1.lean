module

public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem member_commutes_oddCore_of_deltaCore_eq_bot [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8)
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 A, deltaCore Φ = ⊥) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    {K : Subgroup G} (hK : K ∈ centMembers Ω x) {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) (hcc : InCommonComponent x K L₀) :
    ∀ d ∈ componentClassificationOddCore ↥(centLayer Ω x), ∀ k ∈ K, (d : G) * k = k * d := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hxne : ¬ ({x} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hx1
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 h0 hA1 hΩ hIH hxne
  have := memberJoin_normal (a := x) hΩ.conjInvariant
  have htL : ∀ l ∈ L₀, x * l = l * x := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hL₀A hl) x hxA
  have hL₀C : L₀ ≤ C := fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (htL l hl).symm
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
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hA.2 x hxA
  have hW : WeakMember (GaloisField p f) L₀ z₀ :=
    ⟨hz₀.orderOf_eq_two, hz₀.mem, hz₀.perfect, hz₀.subnormal, hz₀.nonempty_equiv⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hmem := IsInvolutionMember.of_weakMember hW h4
  have hc := hz₀.isCentralInvolution
  have hL₀ne : L₀ ≠ ⊥ := by
    intro hbot
    have := hc.mem
    rw [hbot, Subgroup.mem_bot] at this
    exact hc.ne_one this
  have hAC : A ≤ C := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm (⟨e, he⟩ : A) ⟨x, hxA⟩))
  have hsubL : IsSubnormal L₀ (C ⊓ Subgroup.centralizer (A : Set G)) := by
    have h := isSubnormal_inf hz₀.subnormal (C ⊓ Subgroup.centralizer (A : Set G))
    rwa [inf_eq_left.mpr (le_inf hL₀C hL₀A),
      inf_eq_right.mpr (inf_le_right.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz₀A)))] at h
  have hPq : CFSG.Open.IsQuasisimple ↥P :=
    isQuasisimple_of_isTwoComponent_of_layer_of_centralizes hPC (by rw [hPsub]; exact hlift) hAC
      hA hcard hL₀P hL₀A hmem.perfect hL₀ne hΔ hsubL hmem.quasisimple
      fun f₀ hf₀ hf₀1 M hM =>
        hB_of_localLieSystems_of_centralizes hp2 h0 hA1 hΩ hIH hL₀Ω hx2 hx1 htL
          (not_subset_center_of_ne_one hnab hf₀1)
          (hL₀A.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf₀)))
          (congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hxA⟩ : A) ⟨f₀, hf₀⟩)) M hM
  have hq' : CFSG.Open.IsQuasisimple ↥lift :=
    Components.quasisimple_of_equiv (lift.equivMapOfInjective C.subtype C.subtype_injective) hPq
  have hcomp : IsComponentOf lift ⊤ := ⟨le_top, hlift.1, hq'⟩
  have hsolv : Group.IsSolvable ↥(componentClassificationOddCore ↥C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (OddCore.odd_card _)
  have hOsub : IsSubnormal (componentClassificationOddCore ↥C) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hcommlift := LocalComponents.commutes_with_solvable_subnormal lift _ hcomp hOsub
  intro d hd k hk
  have hdO : Subgroup.inclusion (centLayer_le_centralizer Ω x) d ∈
      componentClassificationOddCore ↥C := map_inclusion_oddCore_le hΩ.conjInvariant ⟨d, hd, rfl⟩
  have hk' : (⟨k, hK.2 hk⟩ : ↥C) ∈ lift := hKle (Subgroup.mem_subgroupOf.mpr hk)
  have hmem' := Subgroup.commutator_mem_commutator hk' hdO
  rw [hcommlift, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem'
  exact (congrArg Subtype.val hmem').symm

theorem localOddCentral_of_deltaCore_eq_bot [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8)
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 A, deltaCore Φ = ⊥) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hmeet : ∀ K ∈ centMembers Ω x, ∃ L₀ ∈ Ω, ∃ z₀ ∈ A, IsClassicalMember p f L₀ z₀ ∧
      L₀ ≤ Subgroup.centralizer (A : Set G) ∧ InCommonComponent x K L₀) :
    LocalOddCentral Ω {x} := by
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
      obtain ⟨L₀, hL₀Ω, z₀, hz₀A, hz₀, hL₀A, hcc⟩ := hmeet K hK
      exact Subtype.ext (member_commutes_oddCore_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH
        hA hcard hΔ hxA hx1 hK hL₀Ω hz₀ hz₀A hL₀A hcc d hd k (Subgroup.mem_subgroupOf.mp hk)).symm
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

end CFSG.ClassicalInvolution.Balance.Bootstrap
