module

public import CFSG.ClassicalInvolution.Balance.BootstrapStage2Alpha
public import CFSG.ClassicalInvolution.Balance.LayerGenerationField
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureLink
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem range_inf_range_le_center {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) {i j : Fin D.card} (h : i ≠ j) :
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
theorem singleClassComponents_of_tags {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) :
    SingleClassComponents p f D := fun i =>
  ModelFacts.fundamentalSingleClass (D.tag i) (D.rank i) p (D.exp i) Fact.out (D.isFundTag i)
    (D.admissible i) (hD i).1 (hD i).2

theorem eq_of_modOdd_le_map_range (hΩ : InClass p f Ω) {a : G} (D : LocalLieSystemAt p f Ω a)
    {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {a}) {i j : Fin D.card}
    (hi : modOddIn (centralizingLayer Ω {a}) M ≤ (D.hom i).range)
    (hj : modOdd a M ≤ (D.hom j).range.map (layerQuotientHom hΩ.conjInvariant a)) : i = j := by
  by_contra hne
  have hθ := layerQuotientHom_injective (a := a) hΩ.conjInvariant
  have hmap : (modOddIn (centralizingLayer Ω {a}) M).map (layerQuotientHom hΩ.conjInvariant a) =
      modOdd a M := by
    show ((M.subgroupOf (centLayer Ω a)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Ω a)))).map
        (layerQuotientHom hΩ.conjInvariant a) = modOdd a M
    rw [Subgroup.map_map]
    exact map_layerToOddQuot_subgroupOf (le_centLayer hM)
  have hj' : modOddIn (centralizingLayer Ω {a}) M ≤ (D.hom j).range := by
    rw [← hmap] at hj
    exact (Subgroup.map_le_map_iff_of_injective hθ).mp hj
  exact not_le_center_of_mem hΩ hM ((le_inf hi hj').trans (range_inf_range_le_center D hne))


theorem exists_conj_modOddIn_of_inCommonComponent (hΩ : InClass p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {a : G} (D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a))
    (hD : SingleClassComponents p f D) {M K : Subgroup G} (hM : M ∈ centralizingMembers Ω {a})
    (hK : K ∈ centralizingMembers Ω {a}) (hcc : InCommonComponent a M K) :
    ∃ w ∈ centralizingLayer Ω {a}, modOddIn (centralizingLayer Ω {a}) K =
      modOddIn (centralizingLayer Ω {a}) (conjSub w M) := by
  set Y := centralizingLayer Ω {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hKY : K ≤ Y := le_centralizingLayer hK
  have hMfam : modOddIn Y M ∈ localFamily Ω a := ⟨M.subgroupOf Y, ⟨M, hM, hMY, rfl⟩, rfl⟩
  have hKfam : modOddIn Y K ∈ localFamily Ω a := ⟨K.subgroupOf Y, ⟨K, hK, hKY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain ⟨j, R', hR', hKR'⟩ := D.fundamental _ hKfam
  have hMi : modOddIn Y M ≤ (D.hom i).range := hMR ▸ Subgroup.map_le_range _ _
  have hKj : modOddIn Y K ≤ (D.hom j).range := hKR' ▸ Subgroup.map_le_range _ _
  have hij : i = j := by
    obtain ⟨Q, hQ, hMQ, hKQ⟩ := hcc
    have hQc : IsComponentOf Q ⊤ := (CFSG.isComponent_iff_open Q).mp hQ
    have : (memberJoin Ω a).Normal := memberJoin_normal hΩ.conjInvariant
    obtain ⟨D', hD'Q, -⟩ := lieDecomposition_localSystem_comp hp2 ModelFacts.modelClauseZero
      fundamentalWholeA1 hq hΩ D
    rcases D'.eq_or_commutes_of_isComponentOf hQc with ⟨i', hi'⟩ | hcomm
    · obtain ⟨j₀, hj₀⟩ := hD'Q i'
      have hQeq : Q = (D.hom j₀).range.map (layerQuotientHom hΩ.conjInvariant a) := by
        rw [hi', ← hj₀]
        exact MonoidHom.range_comp _ _
      have h1 := eq_of_modOdd_le_map_range hΩ D hM hMi (hQeq ▸ hMQ)
      have h2 := eq_of_modOdd_le_map_range hΩ D hK hKj (hQeq ▸ hKQ)
      exact h1.trans h2.symm
    · exfalso
      obtain ⟨z, hz⟩ := hΩ.classical M hM.1
      obtain ⟨hperf, hne⟩ := modOdd_perfect_ne_bot hz hM.2
      have hMJ : modOdd a M ≤ memberJoin Ω a :=
        le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) M hM
      apply hne
      rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm x (hMQ hx) y (hMJ hy)
  subst hij
  obtain ⟨g, hg⟩ := hD i R hR R' hR'
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

theorem involutionLink_of_inCommonComponent (hL : LocalHypotheses p f Ω A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hS : S ⊆ Ω) (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hcover : ∀ M ∈ centralizingMembers Ω {a}, ∃ K ∈ S,
      K ≤ Subgroup.centralizer ({a} : Set G) ∧ InCommonComponent a M K) :
    InvolutionLink p f Ω A S a := by
  intro M hMmem z hz
  have hΩ := hL.inClass.conjInvariant
  have hodd := odd_card_galoisField hL.odd hL.five
  obtain ⟨K', hK'S, hK'a, hcc⟩ := hcover M hMmem
  have hK'mem : K' ∈ centralizingMembers Ω {a} := ⟨hS hK'S, hK'a⟩
  obtain ⟨D⟩ := hL.lie {a} (fun h => hL.noncentral a haA ha1 (h rfl))
  obtain ⟨w, hwY, hmod⟩ := exists_conj_modOddIn_of_inCommonComponent hL.inClass hL.odd hL.five D
    (hL.single a haA ha1 D) hMmem hK'mem hcc
  obtain ⟨z', hz'A, hK'z'⟩ := hinv K' hK'S
  have hK'' : IsClassicalMember p f (conjSub w M) (w * z * w⁻¹) := hz.conj w
  have hwC : w ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a} hwY
  have hK''Y : conjSub w M ≤ centralizingLayer Ω {a} :=
    le_centralizingLayer (conjSub_mem_centralizingMembers hΩ hwC hMmem)
  have hU := mul_mem_oddCoreIn_of_modOddIn_eq hodd hK'z' hK'' (le_centralizingLayer hK'mem)
    hK''Y hmod
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem (sq_eq_one hK'') (sq_eq_one hK'z')
    (odd_card_oddCoreIn _) hU
  have hoY : o ∈ centralizingLayer Ω {a} := oddCoreIn_le _ ho
  refine ⟨K', hK'S, z', hz'A, hK'z', w⁻¹ * o⁻¹, mul_mem (inv_mem hwY) (inv_mem hoY), ?_⟩
  rw [hoz]
  group

theorem involutionLink_of_tripleMeetsAt {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hL : LocalHypotheses p f Ω T.group)
    (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember p f K₁ z₁)
    (hz₂ : IsClassicalMember p f K₂ z₂) (hz₃ : IsClassicalMember p f K₃ z₃)
    (hmeet : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      TripleMeetsAt Ω K₁ K₂ K₃ a) :
    ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a := by
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₂A : z₂ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₃A : z₃ ∈ T.group := Subgroup.subset_closure (by simp)
  intro a ha hfa
  obtain ⟨K, hKS, hK⟩ := hfa
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (T.group : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  refine involutionLink_of_inCommonComponent hL ha hK.ne_one ?_ ?_ ?_
  · intro K hK
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl | rfl <;> assumption
  · intro K hK
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl | rfl
    exacts [⟨z₁, hz₁A, hz₁⟩, ⟨z₂, hz₂A, hz₂⟩, ⟨z₃, hz₃A, hz₃⟩]
  · intro M hM
    rcases hmeet a ha ⟨K, hKS, hK⟩ M hM with h | h | h
    · exact ⟨K₁, by simp, hcen T.le_centralizer₁, h⟩
    · exact ⟨K₂, by simp, hcen T.le_centralizer₂, h⟩
    · exact ⟨K₃, by simp, hcen T.le_centralizer₃, h⟩

theorem exactMembers_and_localOddCentral_of_exactTriple_meets [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω)
    (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃)
    (hMF1 : ∀ a ∈ T.group, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hloc : ∀ a ∈ T.group, a ≠ 1 → ComponentLayersAt Ω T.group a) (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hmeet : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      TripleMeetsAt Ω K₁ K₂ K₃ a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hL : LocalHypotheses p f Ω T.group :=
    { inClass := hΩ
      odd := hp2
      five := hq
      noncentral := fun a _ ha1 hc =>
        not_subset_center_of_ne_one hnab ha1 (Set.singleton_subset_iff.mpr hc)
      lie := hIH
      single := hMF1 }
  exact exactMembers_and_localOddCentral_of_exactTriple_wb hnab hp2 hq h9
    ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hsingle hIH T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
    hloc hconn hgenModO
    (involutionLink_of_tripleMeetsAt T hL hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ hmeet)
    (hmeet z₁ hz₁A ⟨K₁, by simp, hz₁⟩)

end CFSG.ClassicalInvolution.Balance.Bootstrap
