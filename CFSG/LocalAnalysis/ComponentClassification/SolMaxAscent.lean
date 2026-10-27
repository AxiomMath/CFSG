module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxMoved

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

@[expose] def StarAt (K A : Subgroup G) : Prop :=
  twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G))

@[expose] def InvAt (K A : Subgroup G) : Prop :=
  ∀ M : Subgroup G, IsTwoComponentIn M (centralizer (A : Set G)) →
    ¬ twoLayerIn (K ⊓ centralizer (A : Set G)) ≤ coreActionKernel M →
    Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥K ⧸ Open.fusionZStar ↥K)

variable [Finite G]

omit [Finite G] in
theorem centralizer_sup_zpowers (A : Subgroup G) (s : G) :
    centralizer ((A ⊔ zpowers s : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer ({s} : Set G) := by
  ext x
  constructor
  · intro hx
    refine mem_inf.mpr ⟨centralizer_le (le_sup_left : A ≤ A ⊔ zpowers s) hx, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.mp hx) s (mem_sup_right (mem_zpowers s))).symm
  · intro hx
    obtain ⟨hxA, hxs⟩ := mem_inf.mp hx
    have hle : A ⊔ zpowers s ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp hxA) a ha
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_singleton_iff.mp hxs).symm
    rw [mem_centralizer_iff]
    intro b hb
    exact mem_centralizer_singleton_iff.mp (hle hb)

theorem layerAt_facts {K A : Subgroup G} (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hA2 : IsPGroup 2 A) (hAQ : A ≤ coreActionKernel K) :
    ⁅twoLayerIn (K ⊓ centralizer (A : Set G)), twoLayerIn (K ⊓ centralizer (A : Set G))⁆ =
        twoLayerIn (K ⊓ centralizer (A : Set G)) ∧
      IsQuasisimple (↥(twoLayerIn (K ⊓ centralizer (A : Set G))) ⧸
        pPrimeCore 2 ↥(twoLayerIn (K ⊓ centralizer (A : Set G)))) ∧
      Nat.card (↥(twoLayerIn (K ⊓ centralizer (A : Set G))) ⧸
        Open.fusionZStar ↥(twoLayerIn (K ⊓ centralizer (A : Set G)))) =
          Nat.card (↥K ⧸ Open.fusionZStar ↥K) ∧
      Nonempty (↥(twoLayerIn (K ⊓ centralizer (A : Set G))) ⧸
        Open.fusionZStar ↥(twoLayerIn (K ⊓ centralizer (A : Set G))) ≃*
          ↥K ⧸ Open.fusionZStar ↥K) := by
  obtain ⟨hJc, hLB, -, ⟨eJ⟩⟩ := Sol76.cover_facts hKq inf_le_left
    (Sol76.inf_centralizer_sup_oddCoreIn_eq hA2 hAQ)
  rw [hLB]
  refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hJc.1 hJc.2,
    LocalCores.isQuasisimple_of_mulEquiv eJ.symm hKq,
    Nat.card_congr (Sol78.fusionZStarQuotOfCore eJ).toEquiv, ⟨Sol78.fusionZStarQuotOfCore eJ⟩⟩

theorem layerAt_mono {K A B : Subgroup G} (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B) (hAB : A ≤ B) (hBQ : B ≤ coreActionKernel K) :
    twoLayerIn (K ⊓ centralizer (B : Set G)) ≤ twoLayerIn (K ⊓ centralizer (A : Set G)) := by
  obtain ⟨-, hLB, -, -⟩ := Sol76.cover_facts hKq inf_le_left
    (Sol76.inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  obtain ⟨-, hLA, -, -⟩ := Sol76.cover_facts hKq inf_le_left
    (Sol76.inf_centralizer_sup_oddCoreIn_eq hA2 (hAB.trans hBQ))
  rw [hLB, hLA]
  refine closure_mono fun x hx => ⟨?_, hx.2⟩
  exact inf_le_inf_left K (centralizer_le hAB) hx.1

theorem twoLayerIn_centralizer_mono {A B : Subgroup G} (hB2 : IsPGroup 2 B) (hAB : A ≤ B)
    (hBA : B ≤ normalizer (A : Set G)) :
    twoLayerIn (centralizer (B : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) := by
  have h := GrSLit.pLayer_inf_centralizer_le_of_normalizes hB2
    (Sol76.le_normalizer_centralizer hBA)
  rw [inf_eq_right.mpr (centralizer_le hAB)] at h
  exact h

theorem good_sup_zpowers {K A : Subgroup G} {s : G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hA2 : IsPGroup 2 A)
    (hAQ : A ≤ coreActionKernel K) (hs : IsPGroup 2 (zpowers s)) (hsQ : s ∈ coreActionKernel K)
    (hsA : s ∈ normalizer (A : Set G)) (hs2A : s ^ 2 ∈ A) (hstar : StarAt K A)
    (hinv : InvAt K A) : StarAt K (A ⊔ zpowers s) ∧ InvAt K (A ⊔ zpowers s) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := A ⊔ zpowers s with hB
  set CA := centralizer (A : Set G) with hCA
  set Cs := centralizer ({s} : Set G) with hCs
  set Xs := CA ⊔ zpowers s with hXs
  have hzA : zpowers s ≤ normalizer (A : Set G) := zpowers_le.mpr hsA
  have hB2 : IsPGroup 2 B := by
    have := IsPGroup.to_sup_of_normal_right' hs hA2 hzA
    rwa [sup_comm] at this
  have hBQ : B ≤ coreActionKernel K := sup_le hAQ (zpowers_le.mpr hsQ)
  have hBA : B ≤ normalizer (A : Set G) := sup_le le_normalizer hzA
  have hzCA : zpowers s ≤ normalizer (CA : Set G) := Sol76.le_normalizer_centralizer hzA
  have hCB : centralizer (B : Set G) = CA ⊓ Cs := centralizer_sup_zpowers A s
  obtain ⟨hJp, hJq, hJZ, -⟩ := layerAt_facts hKq hB2 hBQ
  set J := twoLayerIn (K ⊓ centralizer (B : Set G)) with hJ
  have hJLA : J ≤ twoLayerIn (K ⊓ CA) := layerAt_mono hKq hA2 hB2 le_sup_left hBQ
  have hJA : J ≤ twoLayerIn CA := hJLA.trans hstar
  have hCAX : CA ≤ Xs := le_sup_left
  have hXn : Xs ≤ normalizer (CA : Set G) := sup_le le_normalizer hzCA
  have hJX : J ≤ twoLayerIn Xs :=
    hJA.trans (GrSLit.pLayer_map_le_of_isSubnormal hCAX
      (Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hCAX).mpr hXn)))
  have hJs : J ≤ Cs := by
    intro x hx
    have hx1 : x ∈ K ⊓ centralizer (B : Set G) := (map_subtype_le _) hx
    rw [hCB] at hx1
    exact (mem_inf.mp (mem_inf.mp hx1).2).2
  have htype : ∀ M : Subgroup G, IsTwoComponentIn M Xs → ¬ J ≤ coreActionKernel M →
      Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) := by
    intro M hMX hmove
    have hXA : twoLayerIn Xs ≤ twoLayerIn CA :=
      GrSLit.pLayer_map_le_of_le_sup hCAX le_rfl hs hzCA
    have hMCA : M ≤ CA :=
      (le_twoLayerIn_of_isTwoComponentIn hMX).trans (hXA.trans (map_subtype_le _))
    have hMc : IsTwoComponentIn M CA :=
      ⟨hMCA, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hMCA hCAX hMX.2⟩
    rw [hJZ]
    exact hinv M hMc fun h => hmove (hJLA.trans h)
  have hsX : s ∈ Xs := mem_sup_right (mem_zpowers s)
  have hs2X : ∀ x ∈ Xs, s ^ 2 * x = x * s ^ 2 := by
    have hle : Xs ≤ centralizer ({s ^ 2} : Set G) := by
      refine sup_le (fun c hc => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp hc) _ hs2A).symm
      · rw [mem_centralizer_singleton_iff]
        exact ((Commute.refl s).pow_right 2).eq
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hle hx)).symm
  have hmain := Sol76.le_twoLayerIn_inf_centralizer hsX hs2X hs hJX hJs hJp hJq htype
  have hstarB : StarAt K B := by
    refine hmain.trans ?_
    rw [hCB]
    have hsCs : s ∈ Cs := mem_centralizer_singleton_iff.mpr rfl
    have hQY : CA ⊓ Cs ≤ Xs ⊓ Cs := inf_le_inf_right _ hCAX
    have hYQ : Xs ⊓ Cs ≤ (CA ⊓ Cs) ⊔ zpowers s := by
      intro y hy
      obtain ⟨hyX, hys⟩ := mem_inf.mp hy
      obtain ⟨c, hc, t, ht, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hzCA hyX
      have htC : t ∈ Cs := zpowers_le.mpr hsCs ht
      have hcC : c ∈ Cs := by
        have : c = c * t * t⁻¹ := by group
        rw [this]
        exact mul_mem hys (inv_mem htC)
      exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hc, hcC⟩)) (mem_sup_right ht)
    have hzQ : zpowers s ≤ normalizer ((CA ⊓ Cs : Subgroup G) : Set G) := by
      rw [zpowers_le]
      exact Sol76.mem_normalizer_inf (hzCA (mem_zpowers s)) (le_normalizer hsCs)
    exact GrSLit.pLayer_map_le_of_le_sup hQY hYQ hs hzQ
  refine ⟨hstarB, fun M hM hmove => ?_⟩
  have hge := (card_fusionZStar_quot_le hstarB hJp hJq hM hmove).1
  have hBCA : twoLayerIn (centralizer (B : Set G)) ≤ twoLayerIn CA :=
    twoLayerIn_centralizer_mono hB2 le_sup_left hBA
  have hMp : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hM.1 hM.2
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hM.1).mp hM.2).2.2
  have hMCA : M ≤ twoLayerIn CA := (le_twoLayerIn_of_isTwoComponentIn hM).trans hBCA
  have hJM : J ≤ normalizer (M : Set G) := hstarB.trans (twoLayerIn_le_normalizer hM.1 hM.2)
  obtain ⟨M', hM', hJM', hMM'⟩ := exists_moved_both hMCA hJA hMp hJM hmove
  have hle := (card_fusionZStar_quot_le hMCA hMp hMq hM' hMM').1
  have hM'eq := hinv M' hM' fun h => hJM' (hJLA.trans h)
  rw [hJZ] at hge
  omega

end CFSG.ComponentClassification.SolMax
