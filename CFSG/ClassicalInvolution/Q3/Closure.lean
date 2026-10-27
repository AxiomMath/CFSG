module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.LieDecomposition
public import CFSG.ClassicalInvolution.Balance.BootstrapClosure
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Defs

variable {G : Type} [Group G]

structure FrameSideTwo3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Prop where
  elem : IsElemAbelian 2 A
  card : 8 ≤ Nat.card A
  subset : S ⊆ Ω
  nonempty : S.Nonempty
  involution : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z
  generation : ∀ a ∈ A, IsFrameInvolution3 S a → CentralizerGenerationModOTwo Ω A a
  link : ∀ a ∈ A, IsFrameInvolution3 S a → InvolutionLink3 Ω A S a

@[expose] def omegaStarTwo3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ h ∈ rankTwoSpan A, ∃ K ∈ S, ∃ z ∈ A,
    IsClassicalMember3 K z ∧ IsClassicalMember3 L (h * z * h⁻¹)}

end Defs

section Closure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

theorem le_rankTwoSpan_of_mem_omegaStarTwo3 (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    {L : Subgroup G} (hLs : L ∈ omegaStarTwo3 Ω A S) : L ≤ rankTwoSpan A := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} :=
    ⟨hconj _ _ hLΩ, isSubnormal_le hLa'.subnormal⟩
  have hY : conjSub h⁻¹ L ≤ rankTwoSpan A :=
    (le_centralizingLayer hmem).trans (centralizingLayer_le_rankTwoSpan hconj hF.elem hF.card haA
      (hF.generation a haA ⟨K, hK, hKa⟩))
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStarTwo3_of_commutes (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    {L L' : Subgroup G} (hLs : L ∈ omegaStarTwo3 Ω A S) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStarTwo3 Ω A S := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
  have hc' : Commutes (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := hc.conjSub h₀⁻¹
  set M := conjSub h₀⁻¹ L' with hM
  have hMΩ : M ∈ Ω := hconj _ _ hL'
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc' a hLa'.mem x hx).symm
  have hMmem : M ∈ centralizingMembers Ω {a} := ⟨hMΩ, hMa⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.classical M hMΩ
  obtain ⟨K', hK'S, z', hz'A, hK'z', h₁, hh₁Y, hz₀h₁⟩ :=
    hF.link a haA ⟨K, hKS, hKa⟩ M hMmem z₀ hz₀
  have hYH := centralizingLayer_le_rankTwoSpan hconj hF.elem hF.card haA
    (hF.generation a haA ⟨K, hKS, hKa⟩)
  have hz₀' : IsClassicalMember3 M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember3 L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ (hYH hh₁Y), K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem mem_omegaStarTwo3_of_omegaConnected (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) : L ∈ omegaStarTwo3 Ω A S := by
  obtain ⟨K₀, hK₀⟩ := hF.nonempty
  obtain ⟨z, hzA, hz⟩ := hF.involution K₀ hK₀
  have hK₀s : K₀ ∈ omegaStarTwo3 Ω A S :=
    ⟨hF.subset hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStarTwo3 Ω A S := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarTwo3_of_commutes hΩ hF ih hbc.1 hbc.2
  exact key L (hconn K₀ (hF.subset hK₀) L hLΩ)

theorem rankTwoSpan_eq_top3 (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    (hconn : OmegaConnected Ω) : rankTwoSpan A = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_rankTwoSpan_of_mem_omegaStarTwo3 hΩ hF
    (mem_omegaStarTwo3_of_omegaConnected hΩ hF hconn hLΩ)

end Closure

section Family

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure MemberFamily3 (Ω : Set (Subgroup G)) (A : Subgroup G) (𝒦 : Set (Subgroup G)) :
    Prop where
  elem : IsElemAbelian 2 A
  card : Nat.card A = 8
  subset : 𝒦 ⊆ Ω
  nonempty : 𝒦.Nonempty
  involution : ∀ K ∈ 𝒦, ∃ z ∈ A, IsClassicalMember3 K z ∧ K ≤ Subgroup.centralizer (A : Set G)
  generate : A = Subgroup.closure {z | ∃ K ∈ 𝒦, IsClassicalMember3 K z}

theorem generation_of_memberFamily3 {A : Subgroup G} {𝒦 : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hM : MemberFamily3 Ω A 𝒦) (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution3 𝒦 a → CentralizerGenerationModOTwo Ω A a)
    (hlink : ∀ a ∈ A, IsFrameInvolution3 𝒦 a → InvolutionLink3 Ω A 𝒦 a) :
    (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤ :=
  rankTwoSpan_eq_top3 hΩ
    { elem := hM.elem
      card := hM.card.ge
      subset := hM.subset
      nonempty := hM.nonempty
      involution := fun K hK => by
        obtain ⟨z, hzA, hz, -⟩ := hM.involution K hK
        exact ⟨z, hzA, hz⟩
      generation := hgenModO
      link := hlink } hconn

theorem generation_of_exactTriple3 (hΩ : InClass3 Ω) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω)
    (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution3 ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hlink : ∀ a ∈ T.group, IsFrameInvolution3 ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink3 Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a) :
    (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤ := by
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₂A : z₂ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₃A : z₃ ∈ T.group := Subgroup.subset_closure (by simp)
  exact rankTwoSpan_eq_top3 hΩ
    { elem := T.isElemAbelian
      card := (T.card_eq_eight hind).ge
      subset := by
        intro K hK
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
        rcases hK with rfl | rfl | rfl <;> assumption
      nonempty := ⟨K₁, by simp⟩
      involution := by
        intro K hK
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
        rcases hK with rfl | rfl | rfl
        exacts [⟨z₁, hz₁A, hz₁⟩, ⟨z₂, hz₂A, hz₂⟩, ⟨z₃, hz₃A, hz₃⟩]
      generation := hgenModO
      link := hlink } hconn

end Family

section Link

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

omit [Finite G] in
theorem range_inf_range_le_center3 {ι X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) {i j : ι} (h : i ≠ j) :
    (D.hom i).range ⊓ (D.hom j).range ≤ Subgroup.center X := by
  rintro x ⟨hxi, hxj⟩
  have key : ∀ k, (D.hom k).range ≤ Subgroup.centralizer ({x} : Set X) := by
    intro k y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨u, rfl⟩ := hy
    by_cases hki : k = i
    · subst hki
      obtain ⟨v, hv⟩ := hxj
      rw [← hv]
      exact D.commute k j h u v
    · obtain ⟨v, hv⟩ := hxi
      rw [← hv]
      exact D.commute k i hki u v
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ (⨆ k, (D.hom k).range : Subgroup X) := by rw [D.generate]; trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp ((iSup_le key) hg)

omit [Finite G] in
theorem exists_conj_modOddIn_of_fund3 {a : G} {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)) {M K : Subgroup G} {i : ι}
    {R R' : Subgroup (D.kind i).G}
    (hMR : modOddIn (centralizingLayer Ω {a}) M = R.map (D.hom i))
    (hKR' : modOddIn (centralizingLayer Ω {a}) K = R'.map (D.hom i)) (g : (D.kind i).G)
    (hg : R' = conjSub g R) :
    ∃ w ∈ centralizingLayer Ω {a}, modOddIn (centralizingLayer Ω {a}) K =
      modOddIn (centralizingLayer Ω {a}) (conjSub w M) := by
  set Y := centralizingLayer Ω {a} with hY
  obtain ⟨wT, hwT⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) (D.hom i g)
  refine ⟨(wT : G), wT.2, ?_⟩
  calc modOddIn Y K = R'.map (D.hom i) := hKR'
    _ = (conjSub g R).map (D.hom i) := by rw [hg]
    _ = conjSub (D.hom i g) (R.map (D.hom i)) := (conjSub_map _ _ _).symm
    _ = conjSub (D.hom i g) (modOddIn Y M) := by rw [← hMR]
    _ = conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) wT) (modOddIn Y M) := by
        rw [hwT]
    _ = (conjSub wT (M.subgroupOf Y)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) :=
        conjSub_map _ _ _
    _ = ((conjSub (wT : G) M).subgroupOf Y).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
        rw [conjSub_subgroupOf]
    _ = modOddIn Y (conjSub (wT : G) M) := rfl

@[expose] def LieCovers3 (Ω : Set (Subgroup G)) (S : Set (Subgroup G)) (a : G) : Prop :=
  ∀ (ι : Type) (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)) (i : ι),
    ∃ K ∈ S, K ≤ Subgroup.centralizer ({a} : Set G) ∧
      modOddIn (centralizingLayer Ω {a}) K ≤ (D.hom i).range

theorem involutionLink_of_lieCovers3 (hL : LocalHypotheses3 Ω A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hS : S ⊆ Ω) (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z)
    (hcov : LieCovers3 Ω S a) : InvolutionLink3 Ω A S a := by
  intro M hMmem z hz
  have hΩ := hL.inClass.conjInvariant
  obtain ⟨ι, -, ⟨D⟩⟩ := hL.lie {a} (fun h => hL.noncentral a haA ha1 (h rfl))
  set Y := centralizingLayer Ω {a} with hY
  have hMfam : modOddIn Y M ∈ localFamily Ω a :=
    ⟨M.subgroupOf Y, ⟨M, hMmem, le_centralizingLayer hMmem, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain ⟨K', hK'S, hK'a, hK'i⟩ := hcov ι D i
  have hK'mem : K' ∈ centralizingMembers Ω {a} := ⟨hS hK'S, hK'a⟩
  have hK'fam : modOddIn Y K' ∈ localFamily Ω a :=
    ⟨K'.subgroupOf Y, ⟨K', hK'mem, le_centralizingLayer hK'mem, rfl⟩, rfl⟩
  obtain ⟨j, R', hR', hK'R'⟩ := D.fundamental _ hK'fam
  have hij : j = i := by
    by_contra hne
    refine not_le_center_of_mem3 hL.inClass hK'mem ?_
    have h1 : modOddIn Y K' ≤ (D.hom j).range := hK'R' ▸ Subgroup.map_le_range _ _
    exact (le_inf hK'i h1).trans (range_inf_range_le_center3 D (Ne.symm hne))
  subst hij
  obtain ⟨g, hg⟩ := hL.single a haA ha1 ι D j R hR R' hR'
  obtain ⟨w, hwY, hmod⟩ := exists_conj_modOddIn_of_fund3 D hMR hK'R' g hg
  obtain ⟨z', hz'A, hK'z'⟩ := hinv K' hK'S
  have hK'' : IsClassicalMember3 (conjSub w M) (w * z * w⁻¹) := hz.conj w
  have hwC : w ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a} hwY
  have hK''Y : conjSub w M ≤ centralizingLayer Ω {a} :=
    le_centralizingLayer (conjSub_mem_centralizingMembers hΩ hwC hMmem)
  have hU := mul_mem_oddCoreIn_of_modOddIn_eq3 hK'z' hK'' (le_centralizingLayer hK'mem)
    hK''Y hmod
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem hK''.isCentralInvolution.sq
    hK'z'.isCentralInvolution.sq (odd_card_oddCoreIn _) hU
  have hoY : o ∈ centralizingLayer Ω {a} := oddCoreIn_le _ ho
  refine ⟨K', hK'S, z', hz'A, hK'z', w⁻¹ * o⁻¹, mul_mem (inv_mem hwY) (inv_mem hoY), ?_⟩
  rw [hoz]
  group

end Link

end CFSG.ClassicalInvolution.Q3
