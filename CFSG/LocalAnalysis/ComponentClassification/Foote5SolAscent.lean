module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolType
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

theorem star_sup_zpowers {L A : Subgroup G} {s : G}
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (hA2 : IsPGroup 2 A) (hAQ : A ≤ coreActionKernel L) (hs : IsPGroup 2 (zpowers s))
    (hsQ : s ∈ coreActionKernel L) (hsA : s ∈ normalizer (A : Set G)) (hs2A : s ^ 2 ∈ A)
    (h : twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)))
    (htyp : ∀ K : Subgroup G, IsTwoComponentIn K (centralizer (A : Set G)) →
      ¬ twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ coreActionKernel K →
      Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥L ⧸ Open.fusionZStar ↥L)) :
    twoLayerIn (L ⊓ centralizer ((A ⊔ zpowers s : Subgroup G) : Set G)) ≤
      twoLayerIn (centralizer ((A ⊔ zpowers s : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := A ⊔ zpowers s with hB
  set CA := centralizer (A : Set G) with hCA
  set Cs := centralizer ({s} : Set G) with hCs
  set X := CA ⊔ zpowers s with hX
  have hzA : zpowers s ≤ normalizer (A : Set G) := zpowers_le.mpr hsA
  have hB2 : IsPGroup 2 B := by
    have := IsPGroup.to_sup_of_normal_right' hs hA2 hzA
    rwa [sup_comm] at this
  have hBQ : B ≤ coreActionKernel L := sup_le hAQ (zpowers_le.mpr hsQ)
  have hzCA : zpowers s ≤ normalizer (CA : Set G) := le_normalizer_centralizer hzA
  have hCB : centralizer (B : Set G) = CA ⊓ Cs := by
    ext x
    constructor
    · intro hx
      refine mem_inf.mpr ⟨centralizer_le (le_sup_left : A ≤ B) hx, ?_⟩
      rw [hCs, mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp hx) s (mem_sup_right (mem_zpowers s))).symm
    · intro hx
      obtain ⟨hxA, hxs⟩ := mem_inf.mp hx
      have hle : B ≤ centralizer ({x} : Set G) := by
        refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.mp hxA) a ha
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_singleton_iff.mp hxs).symm
      rw [mem_centralizer_iff]
      intro b hb
      exact mem_centralizer_singleton_iff.mp (hle hb)
  obtain ⟨hJc, hLB, -, ⟨eJ⟩⟩ := cover_facts hLq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  obtain ⟨-, hLA, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hA2 hAQ)
  set J := twoLayerIn (L ⊓ centralizer (B : Set G)) with hJ
  have hJLA : J ≤ twoLayerIn (L ⊓ CA) := by
    rw [hLB, hLA]
    refine closure_mono fun x hx => ⟨?_, hx.2⟩
    exact inf_le_inf_left L (centralizer_le (le_sup_left : A ≤ B)) hx.1
  have hJA : J ≤ twoLayerIn CA := hJLA.trans h
  have hCAX : CA ≤ X := le_sup_left
  have hXn : X ≤ normalizer (CA : Set G) := sup_le le_normalizer hzCA
  have hJX : J ≤ twoLayerIn X :=
    hJA.trans (GrSLit.pLayer_map_le_of_isSubnormal hCAX
      (Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hCAX).mpr hXn)))
  have hJs : J ≤ Cs := by
    intro x hx
    have hx1 : x ∈ L ⊓ centralizer (B : Set G) := (map_subtype_le _) hx
    rw [hCB] at hx1
    exact (mem_inf.mp (mem_inf.mp hx1).2).2
  have hJp : ⁅J, J⁆ = J := by
    rw [hLB]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hJc.1 hJc.2
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) := by
    rw [hLB]
    exact LocalCores.isQuasisimple_of_mulEquiv eJ.symm hLq
  have hJZ : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
    rw [hLB]
    exact Nat.card_congr (Sol78.fusionZStarQuotOfCore eJ).toEquiv
  have htype : ∀ K : Subgroup G, IsTwoComponentIn K X → ¬ J ≤ coreActionKernel K →
      Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) := by
    intro K hKX hmove
    have hXA : twoLayerIn X ≤ twoLayerIn CA :=
      GrSLit.pLayer_map_le_of_le_sup hCAX le_rfl hs hzCA
    have hKCA : K ≤ CA :=
      (le_twoLayerIn_of_isTwoComponentIn hKX).trans (hXA.trans (map_subtype_le _))
    have hKc : IsTwoComponentIn K CA :=
      ⟨hKCA, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKCA hCAX hKX.2⟩
    have hmoveA : ¬ twoLayerIn (L ⊓ CA) ≤ coreActionKernel K := fun hc => hmove (hJLA.trans hc)
    rw [hJZ]
    exact htyp K hKc hmoveA
  have hsX : s ∈ X := mem_sup_right (mem_zpowers s)
  have hs2X : ∀ x ∈ X, s ^ 2 * x = x * s ^ 2 := by
    have hle : X ≤ centralizer ({s ^ 2} : Set G) := by
      refine sup_le (fun c hc => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp hc) _ hs2A).symm
      · rw [mem_centralizer_singleton_iff]
        exact ((Commute.refl s).pow_right 2).eq
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hle hx)).symm
  have hmain := le_twoLayerIn_inf_centralizer hsX hs2X hs hJX hJs hJp hJq htype
  refine hmain.trans ?_
  rw [hCB]
  have hsCs : s ∈ Cs := mem_centralizer_singleton_iff.mpr rfl
  have hQY : CA ⊓ Cs ≤ X ⊓ Cs := inf_le_inf_right _ hCAX
  have hYQ : X ⊓ Cs ≤ (CA ⊓ Cs) ⊔ zpowers s := by
    intro y hy
    obtain ⟨hyX, hys⟩ := mem_inf.mp hy
    obtain ⟨c, hc, t, ht, rfl⟩ := exists_mul_of_mem_sup_normalizer hzCA hyX
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

theorem le_coreActionKernel_of_cover {L Ls Lb M : Subgroup G} (hsb : Ls ≤ Lb) (hbL : Lb ≤ L)
    (hsup : Ls ⊔ oddCoreIn L = L) (hperf : ⁅Lb, Lb⁆ = Lb) (hN : Lb ≤ normalizer (M : Set G))
    (h : Ls ≤ coreActionKernel M) : Lb ≤ coreActionKernel M := by
  set K₀ := (coreActionKernel M).subgroupOf Lb with hK₀
  have hK₀n : K₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hK₀, mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ normalizer (coreActionKernel M : Set G) :=
      normalizer_le_normalizer_coreActionKernel M (hN g.2)
    have := (mem_normalizer_iff.mp hg (n : G)).mp hn
    simpa using this
  set R := (oddCoreIn L ⊓ Lb).subgroupOf Lb with hR
  have hRn : R.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hR, mem_subgroupOf] at hn ⊢
    obtain ⟨hnO, hnL⟩ := mem_inf.mp hn
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have hg : (g : G) ∈ normalizer (oddCoreIn L : Set G) := le_normalizer_oddCoreIn L (hbL g.2)
      have := (mem_normalizer_iff.mp hg (n : G)).mp hnO
      simpa using this
    · simp only [coe_mul, coe_inv]
      exact mul_mem (mul_mem g.2 hnL) (inv_mem g.2)
  have hRodd : Odd (Nat.card R) := by
    have h1 : Nat.card R ∣ Nat.card (oddCoreIn L) := by
      rw [hR, ← Subgroup.card_map_of_injective Lb.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
    exact (Nat.coprime_two_left.mp (coprime_card_oddCoreIn L)).of_dvd_nat h1
  have hT : (⊤ : Subgroup ↥Lb) ≤ K₀ ⊔ R := by
    rintro ⟨x, hx⟩ -
    have hxL : x ∈ oddCoreIn L ⊔ Ls := by rw [sup_comm, hsup]; exact hbL hx
    obtain ⟨o, ho, t, ht, rfl⟩ :=
      exists_mul_of_mem_sup_normalizer ((hsb.trans hbL).trans (le_normalizer_oddCoreIn L)) hxL
    have hoLb : o ∈ Lb := by
      have : o = o * t * t⁻¹ := by group
      rw [this]; exact mul_mem hx (inv_mem (hsb ht))
    have e : (⟨o * t, hx⟩ : ↥Lb) = ⟨o, hoLb⟩ * ⟨t, hsb ht⟩ := rfl
    rw [e]
    exact mul_mem (mem_sup_right (mem_subgroupOf.mpr (mem_inf.mpr ⟨ho, hoLb⟩)))
      (mem_sup_left (mem_subgroupOf.mpr (h ht)))
  have hTp : Group.IsPerfect ↥(⊤ : Subgroup ↥Lb) := by
    have : Group.IsPerfect ↥Lb := Subgroup.isPerfect_iff.mpr hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥Lb)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := ↥Lb)).symm.surjective
  have htop := le_of_perfect_le_sup_of_odd hRodd (le_normalizer_of_normal) hTp hT
  intro x hx
  have := htop (mem_top (⟨x, hx⟩ : ↥Lb))
  exact mem_subgroupOf.mp this

end CFSG.ComponentClassification.Foote5.SolMax
