module

public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLevi
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelRoots

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model

set_option linter.unusedSectionVars false


section Descent

theorem rootSpan_image_of_fixed {τ : Tag} {K K₀ : Type} [Field K] [Field K₀] (σ : K ≃+* K)
    (ι₀ : K₀ →+* K) (hι : ∀ c : K, σ c = c → ∃ c₀ : K₀, ι₀ c₀ = c)
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S)
    (hfix : Units.map (entrywiseHom σ.toRingHom) u = u) :
    u ∈ (rootSpan τ K₀ S).map (baseChangeGL ι₀) := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : Units.map (entrywiseHom σ.toRingHom)
      ((List.ofFn fun k => pinnedX τ K (α k) (c k)).prod) =
        (List.ofFn fun k => pinnedX τ K (α k) (σ (c k))).prod := by
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    refine Units.ext ?_
    rw [Function.comp_apply, Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom (α k) (c k)
  rw [hmap] at hfix
  have hc : (fun k => σ (c k)) = c := hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfix
  choose c₀ hc₀ using fun k => hι (c k) (congrFun hc k)
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  have hαk : α k ∈ S := hrange ▸ Set.mem_range_self k
  show pinnedX τ K (α k) (c k) ∈ (rootSpan τ K₀ S).map (baseChangeGL ι₀)
  rw [← hc₀ k, ← baseChangeGL_pinnedX]
  exact Subgroup.mem_map_of_mem _ (pinnedX_mem_rootSpan hαk _)

theorem levi_image_of_fixed {K K₀ : Type} [Field K] [Field K₀] (σ : K ≃+* K) (ι₀ : K₀ →+* K)
    (hι : ∀ c : K, σ c = c → ∃ c₀ : K₀, ι₀ c₀ = c) {J : Set (Fin (Tag.rank .E7))}
    {g : ModGL .E7 K} (hg : g ∈ parabolicLevi .E7 K J)
    (hfix : Units.map (entrywiseHom σ.toRingHom) g = g) :
    ∃ a : Fin (Tag.rank .E7) → K₀ˣ, ∃ η ∈ NJ K₀ J,
      g = baseChangeGL ι₀ (rootDiagUnit .E7 a * η) := by
  classical
  obtain ⟨t, ht, η, hη, rfl⟩ := exists_mul_of_mem_levi hg
  have hη' : η ∈ (subsystemGroup .E7 K J : Set (ModGL .E7 K)) := hη
  rw [coe_subsystemGroup_eq_iUnion_supportedCell J] at hη'
  simp only [Set.mem_iUnion, exists_prop] at hη'
  obtain ⟨v, hv, hηv⟩ := hη'
  obtain ⟨h, hh, u, hu, u', hu', hηeq⟩ := mem_supportedCell.1 hηv
  set n := canonicalRep (coxeterSystem .E7) K v with hn
  have hhT : h ∈ torusGroup .E7 K := supportedTorus_le_torusGroup J hh
  have hthT : t * h ∈ torusGroup .E7 K := mul_mem ht hhT
  have huU : u ∈ posUnipotent .E7 K := parabolicLeviUnipotent_le_posUnipotent J hu
  have hbB : t * h * u ∈ borelGroup .E7 K :=
    mul_mem (torusGroup_le_borelGroup hthT) (Subgroup.mem_sup_right huU)
  have hu'I : u' ∈ rootSpan .E7 K (inversionSet v) := rootSpan_mono Set.inter_subset_right hu'
  have hg : t * η = (t * h * u) * n * u' := by
    rw [← hηeq]
    simp only [mul_assoc]
  have hσg : Units.map (entrywiseHom σ.toRingHom) (t * h * u) * n *
      Units.map (entrywiseHom σ.toRingHom) u' = (t * h * u) * n * u' := by
    calc Units.map (entrywiseHom σ.toRingHom) (t * h * u) * n *
          Units.map (entrywiseHom σ.toRingHom) u' =
        Units.map (entrywiseHom σ.toRingHom) (t * h * u) *
          Units.map (entrywiseHom σ.toRingHom) n * Units.map (entrywiseHom σ.toRingHom) u' := by
          rw [hn, entrywise_canonicalRep σ]
      _ = Units.map (entrywiseHom σ.toRingHom) ((t * h * u) * n * u') := by
          simp only [map_mul]
      _ = (t * h * u) * n * u' := by rw [← hg]; exact hfix
  have hbij := (bruhat_cell_factorization .E7 K).1 v
  have hpair : (Units.map (entrywiseHom σ.toRingHom) (t * h * u),
      Units.map (entrywiseHom σ.toRingHom) u') = (t * h * u, u') :=
    hbij.2.1 (x₁ := (Units.map (entrywiseHom σ.toRingHom) (t * h * u),
      Units.map (entrywiseHom σ.toRingHom) u')) (x₂ := (t * h * u, u'))
      ⟨entrywise_mem_borelGroup hbB,
        rootSpan_mono Set.inter_subset_right (entrywise_mem_rootSpan hu')⟩ ⟨hbB, hu'I⟩ hσg
  obtain ⟨hbF, hu'F⟩ := Prod.mk.inj hpair
  obtain ⟨htF, huF⟩ := (triangular_borel_structure.{0, 0} .E7 K).2.2.2.2.2.2.1 _
    (entrywise_mem_torusGroup (σ := σ) hthT) (t * h) hthT _ (entrywise_mem_rootSpan (σ := σ) huU)
    u huU (by rw [← map_mul]; exact hbF)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hthT
  have hσb : ∀ i, Units.map σ.toRingHom.toMonoidHom (b i) = b i := by
    have hF' : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit .E7 b) = rootDiagUnit .E7 b := by
      rw [← hb]
      exact htF
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit .E7 b) =
        rootDiagUnit .E7 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom b)
    exact congrFun (rootDiagUnit_injective (h0.symm.trans hF'))
  have hb₀ : ∀ i, ∃ a : K₀ˣ, Units.map ι₀.toMonoidHom a = b i := by
    intro i
    obtain ⟨c₀, hc₀⟩ := hι (b i : K) (congrArg Units.val (hσb i))
    have hc0 : c₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc₀
      exact (b i).ne_zero hc₀.symm
    exact ⟨Units.mk0 c₀ hc0, Units.ext hc₀⟩
  choose a ha using hb₀
  have hda : baseChangeGL ι₀ (rootDiagUnit .E7 a) = t * h := by
    rw [baseChangeGL_rootDiagUnit, hb]
    congr 2
    funext i
    exact ha i
  have hS1 : (parabolicPosRoots .E7 J).Finite :=
    (finite_setOf_isRoot .E7).subset fun β hβ => hβ.2.1
  have hu₀ : u ∈ (rootSpan .E7 K₀ (parabolicPosRoots .E7 J)).map (baseChangeGL ι₀) :=
    rootSpan_image_of_fixed σ ι₀ hι hS1
      (fun α hα hr => bijOn_prod_pinnedX_parabolicPosRoots α hα hr) hu huF
  have hS2 : (parabolicRoots .E7 J ∩ inversionSet v).Finite :=
    (inversionSet_finite v).subset Set.inter_subset_right
  have hu'₀ : u' ∈ (rootSpan .E7 K₀ (parabolicRoots .E7 J ∩ inversionSet v)).map
      (baseChangeGL ι₀) :=
    rootSpan_image_of_fixed σ ι₀ hι hS2
      (fun α hα hr => bijOn_prod_pinnedX_parabolicRoots_inter_inversionSet v α hα hr) hu' hu'F
  have hn₁ : canonicalRep (coxeterSystem .E7) K₀ v ∈ subsystemGroup .E7 K₀ J := by
    have hmem : canonicalRep (coxeterSystem .E7) K₀ v ∈ supportedCell .E7 K₀ J v :=
      mem_supportedCell.2 ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
    have hmem' : canonicalRep (coxeterSystem .E7) K₀ v ∈ (subsystemGroup .E7 K₀ J : Set _) := by
      rw [coe_subsystemGroup_eq_iUnion_supportedCell J]
      exact Set.mem_iUnion₂.2 ⟨v, hv, hmem⟩
    exact hmem'
  obtain ⟨u₁, hu₁, rfl⟩ := hu₀
  obtain ⟨u₁', hu₁', rfl⟩ := hu'₀
  refine ⟨a, u₁ * canonicalRep (coxeterSystem .E7) K₀ v * u₁', ?_, ?_⟩
  · have h1 : u₁ ∈ subsystemGroup .E7 K₀ J := by
      rw [subsystemGroup_eq_rootSpan]
      exact rootSpan_mono (Set.inter_subset_left : parabolicPosRoots .E7 J ⊆ parabolicRoots .E7 J)
        hu₁
    have h2 : u₁' ∈ subsystemGroup .E7 K₀ J := by
      rw [subsystemGroup_eq_rootSpan]
      exact rootSpan_mono Set.inter_subset_left hu₁'
    exact mul_mem (mul_mem h1 hn₁) h2
  · rw [map_mul, map_mul, map_mul, hda, baseChangeGL_canonicalRep, hg, hn]
    simp only [mul_assoc]

theorem levi_image_of_frobenius_fixed {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]
    [IsAlgClosed L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
    {J : Set (Fin (Tag.rank .E7))} {g : ModGL .E7 L} (hg : g ∈ parabolicLevi .E7 L J)
    (hgF : Units.map (entrywiseHom Fr) g = g) :
    ∃ a : Fin (Tag.rank .E7) → Fˣ, ∃ η ∈ NJ F J,
      g = baseChangeGL (algebraMap F L) (rootDiagUnit .E7 a * η) := by
  let σ : L ≃+* L := RingEquiv.ofBijective Fr (frobenius_bijective Fr hFr)
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  refine levi_image_of_fixed σ (algebraMap F L) (fun c hc => ?_) hg (by rw [hσ]; exact hgF)
  refine mem_range_algebraMap_of_pow_card_eq ?_
  rw [← hFr]
  exact hc

theorem mem_rational_levi_of_baseChange {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]
    [IsAlgClosed L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
    {J : Set (Fin (Tag.rank .E7))} {g : ModGL .E7 F}
    (hg : baseChangeGL (algebraMap F L) g ∈ parabolicLevi .E7 L J) :
    ∃ a : Fin (Tag.rank .E7) → Fˣ, ∃ η ∈ NJ F J, g = rootDiagUnit .E7 a * η := by
  obtain ⟨a, η, hη, he⟩ := levi_image_of_frobenius_fixed Fr hFr hg
    (units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g)
  exact ⟨a, η, hη, baseChangeGL_injective _ he⟩

end Descent

end CFSG.ClassicalInvolution.Q3.Q3W
