module

public import CFSG.ClassicalInvolution.AschTight.Basic
public import CFSG.ClassicalInvolution.AschTight.Lemma33

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def TightP1 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranch p f K z → LocalOddCentral (CoreAssembly.conjClass K) {z}

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem centralizingLayer_eq_of_tight (ht : TightBranch p f K z) :
    centralizingLayer (CoreAssembly.conjClass K) {z} = K := by
  have hU := uniqueInvolutionNormal_of_tight (S19R.tightStdDelta_of_tightBranch ht)
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h := hU.1
    simp at h
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨⟨g, rfl⟩, hLz⟩ := hL
    have hgK : conjSubgroup g K = K :=
      singleMemberControl_of_tight ht z hz1 (isPGroup_two_zpowers_of_orderOf_two hU.1) _
        (conjSubgroup_mem_conjugateSet g (self_mem_conjugateSet K)) K (self_mem_conjugateSet K)
        hLz hU.2.2.2.1
    exact hgK.le
  · exact le_iSup₂ (f := fun L (_ : L ∈ centralizingMembers (CoreAssembly.conjClass K) {z}) => L)
      K ⟨CoreAssembly.mem_conjClass_self K, hU.2.2.2.1⟩

theorem oddCore_le_center_of_tightP1 (hP1 : TightP1 p f) [IsSimpleGroup G]
    (ht : TightBranch p f K z) : classicalInvolutionOddCore K ≤ Subgroup.center K := by
  have h := hP1 G K z ht
  unfold LocalOddCentral at h
  rwa [centralizingLayer_eq_of_tight ht] at h

omit [Finite G] in
theorem commute_of_commutator_mem_center (hK : Group.IsPerfect K) {t : G}
    (htN : t ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ k ∈ K, k * t * k⁻¹ * t⁻¹ ∈ (Subgroup.center K).map K.subtype) :
    ∀ k ∈ K, k * t = t * k := by
  have hmemK : ∀ k : K, (k : G) * t * (k : G)⁻¹ * t⁻¹ ∈ K := fun k =>
    commutator_mem_of_mem_normalizer htN k.2
  have hcen : ∀ k : K, (⟨(k : G) * t * (k : G)⁻¹ * t⁻¹, hmemK k⟩ : K) ∈ Subgroup.center K := by
    intro k
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp (h k k.2)
    have hc' : c = ⟨(k : G) * t * (k : G)⁻¹ * t⁻¹, hmemK k⟩ := Subtype.ext hce
    rw [← hc']
    exact hc
  let _ : CommGroup (Subgroup.center K) :=
    { (inferInstance : Group (Subgroup.center K)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : K →* Subgroup.center K :=
    { toFun := fun k => ⟨⟨(k : G) * t * (k : G)⁻¹ * t⁻¹, hmemK k⟩, hcen k⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun k k' => by
        apply Subtype.ext
        apply Subtype.ext
        change (k : G) * k' * t * ((k : G) * k')⁻¹ * t⁻¹ =
          ((k : G) * t * (k : G)⁻¹ * t⁻¹) * ((k' : G) * t * (k' : G)⁻¹ * t⁻¹)
        have hk' : (k : G) * ((k' : G) * t * (k' : G)⁻¹ * t⁻¹) =
            ((k' : G) * t * (k' : G)⁻¹ * t⁻¹) * k :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen k') k)
        rw [commutator_mul hk']
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen k) ⟨_, hmemK k'⟩) }
  intro k hk
  have h1 := eq_one_of_perfect φ ⟨k, hk⟩
  have h2 : k * t * k⁻¹ * t⁻¹ = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
  calc k * t = k * t * k⁻¹ * t⁻¹ * (t * k) := by group
    _ = t * k := by rw [h2, one_mul]

theorem commutingSylowForcesCommuting_of_oddCentral (ht : TightBranch p f K z)
    (hP1 : classicalInvolutionOddCore K ≤ Subgroup.center K) : CommutingSylowForcesCommuting K := by
  intro g hg P₁ P₂ hP₁ hP₂ hcomm
  exfalso
  have hs := S19R.tightStdDelta_of_tightBranch ht
  have hU := uniqueInvolutionNormal_of_tight hs
  have hzP₁ := mem_of_isSylow2Of_of_tight hs hP₁
  have hP₂' : IsSylow2Of (conjSubgroup g⁻¹ P₂) K := by
    have := hP₂.conj g⁻¹
    rwa [conjSubgroup_inv_conjSubgroup] at this
  have htP₂ : g * z * g⁻¹ ∈ P₂ := by
    have h := mem_conjSubgroup_iff.mp (mem_of_isSylow2Of_of_tight hs hP₂')
    simpa using h
  have ht2 : orderOf (g * z * g⁻¹) = 2 := by
    have := (MulAut.conj g).orderOf_eq z
    simpa [MulAut.conj_apply, hU.1] using this
  have ht1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    rw [h] at ht2
    simp at ht2
  have htR : ∀ r ∈ P₁, r * (g * z * g⁻¹) = (g * z * g⁻¹) * r := fun r hr =>
    hcomm r hr _ htP₂
  have htN : g * z * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight hs, Subgroup.mem_centralizer_singleton_iff]
    exact (htR z hzP₁).symm
  have hKt := commute_of_commutator_mem_center ht.branch.member.perfect htN fun k hk =>
    Subgroup.map_mono hP1 (commutator_mem_oddCore_of_centralizes_sylow hU.1 hU.2.1 hU.2.2.1 ht2
      htN hP₁ htR hk)
  have hK : K ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKt k hk
  have hKg : conjSubgroup g K ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ K := mem_conjSubgroup_iff.mp hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hU.2.2.2.1 hx')
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * x := by group
  have hgK : conjSubgroup g K = K :=
    singleMemberControl_of_tight ht _ ht1 (isPGroup_two_zpowers_of_orderOf_two ht2) _
      (conjSubgroup_mem_conjugateSet g (self_mem_conjugateSet K)) K (self_mem_conjugateSet K)
      hKg hK
  exact hg (conjSubgroup_eq_self_iff.mp hgK)

theorem tightCSM_of_tightP1 (hP1 : TightP1 p f) : TightCSM p f := by
  intro G _ _ _ K z ht
  exact commutingSylowForcesCommuting_of_oddCentral ht (oddCore_le_center_of_tightP1 hP1 ht)

end CFSG.ClassicalInvolution.Disconnected.AschTight
