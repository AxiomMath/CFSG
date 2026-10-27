module

import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSTarget
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwFusIDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHoltX
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34Lemma43OddOrbitStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    S ⊓ zStarIn J = ⊥ →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        IsSylowTwoIn S (normalizer (W : Set G)) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
        S ≤ normalizer (K : Set G) → ¬ normalizer (W : Set G) ≤ normalizer (K : Set G) →
        ¬ oddIn K ≤ J →
        L34ConjKernelIncl a J S W

end CFSG.ComponentClassification.GrSLit

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem not_odd_card_commutator_of_perfect {L A B : Subgroup G} (hLper : ⁅L, L⁆ = L)
    (hLev : ¬ Odd (Nat.card L)) (hAL : A ≤ L) (hBL : B ≤ L) (hA : A ⊔ oddIn L = L)
    (hB : B ⊔ oddIn L = L) : ¬ Odd (Nat.card ↥⁅A, B⁆) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLper
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  have hP : (pPrimeCore 2 ↥L).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hcov : ∀ {C : Subgroup G}, C ≤ L → C ⊔ oddIn L = L → (C.subgroupOf L).map π = ⊤ := by
    intro C hCL hC
    have h1 : C.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
      have h2 := congrArg (fun H : Subgroup G => H.subgroupOf L) hC
      unfold oddIn at h2
      rwa [subgroupOf_sup hCL (map_subtype_le _), map_subtype_subgroupOf_self,
        subgroupOf_self] at h2
    have h3 : (⊤ : Subgroup ↥L).map π = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    rwa [← h1, Subgroup.map_sup, hP, sup_bot_eq] at h3
  intro hodd
  have hper : commutator (↥L ⧸ pPrimeCore 2 ↥L) = ⊤ := Group.IsPerfect.commutator_eq_top
  have hcomm : (⁅A.subgroupOf L, B.subgroupOf L⁆).map π = ⊤ := by
    rw [map_commutator, hcov hAL hA, hcov hBL hB, ← commutator_def, hper]
  have hcard : Nat.card ↥⁅A.subgroupOf L, B.subgroupOf L⁆ = Nat.card ↥⁅A, B⁆ := by
    rw [← card_map_of_injective L.subtype_injective, map_commutator,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hAL, inf_of_le_left hBL]
  have hdvd := card_map_dvd (⁅A.subgroupOf L, B.subgroupOf L⁆) π
  rw [hcomm, card_top, hcard] at hdvd
  have hq : Odd (Nat.card (↥L ⧸ pPrimeCore 2 ↥L)) := hodd.of_dvd_nat hdvd
  have hO : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  apply hLev
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L)]
  exact hq.mul hO

theorem mem_normalizer_of_commute
    (hMax : MaximalTwoComponentInput) (hS : SchreierFor Blueprint.Catalog)
    (hbase : L34BaseSetting G) {a : G} {J W K : Subgroup G} (hs : SingleComponentSetting G a J W K)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) {s : G} (hs2 : orderOf s = 2)
    (has : a * s = s * a) (hsK : s ∈ coreActionKernel K) {m : G}
    (hm : m ∈ normalizer (W : Set G)) (hms : m * s = s * m) : m ∈ normalizer (K : Set G) := by
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hs.toGSMaximalSetting
  have hsN : s ∈ normalizer (J : Set G) := hCaN (mem_centralizer_singleton_iff.mpr has.symm)
  have hsJ : s ∈ coreActionKernel J := mem_coreActionKernel_of_mem_kernel hs hsK hsN
  obtain ⟨L', hL's, hL'c, hCN, -, -, hFL', hFsup⟩ := exists_target hMax hS hbase
    hs.orderOf_eq hs2 has hs.le_centralizer hs.isPComponent hs.maximal hL34 hsJ
  by_contra hmK
  set F : Subgroup G := gsFixedLayer J s with hFdef
  have hFK : F ≤ K :=
    ((gsFixedLayer_le_inf J s).trans inf_le_left).trans (GrS4.le_of_singleComponentSetting hs)
  have hmL' : m ∈ normalizer (L' : Set G) := hCN (mem_centralizer_singleton_iff.mpr hms)
  have hL'm : conjugate L' m = L' := conjugate_eq_of_mem_normalizer hmL'
  have hOm : conjugate (oddIn L') m = oddIn L' := conjugate_eq_of_mem_normalizer
    (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L' (pPrimeCore 2 L') hmL')
  have hFmL' : conjugate F m ≤ L' := by
    rw [← hL'm]
    exact map_mono hFL'
  have hFmsup : conjugate F m ⊔ oddIn L' = L' := by
    have h1 : conjugate (F ⊔ oddIn L') m = conjugate F m ⊔ conjugate (oddIn L') m :=
      Subgroup.map_sup _ _ _
    rw [hFsup, hL'm, hOm] at h1
    exact h1.symm
  have hKm : conjugate K m ≠ K := fun h' => hmK (mem_normalizer_of_conjugate_eq h')
  have hcomm : ⁅F, conjugate F m⁆ ≤ oddIn K :=
    (commutator_mono hFK (map_mono hFK)).trans
      ((GrS5.commutator_le_inf_oddIn hs.le_normalizer (conjugate_le_of_mem hs.le_normalizer hm)
        hs.isPComponent_K (isPComponent_conjugate_subgroupOf hm hs.isPComponent_K)
        fun e => hKm e.symm).trans inf_le_left)
  exact not_odd_card_commutator_of_perfect (commutator_eq_of_isPComponent hL's hL'c)
    (GrS4.not_odd_card_of_isPComponent hL's hL'c) hFL' hFmL' hFsup hFmsup
    ((UnbalancedCorr.odd_card_map_pPrimeCore K).of_dvd_nat (card_dvd_of_le hcomm))

theorem false_of_sylowIncl
    (hMax : MaximalTwoComponentInput)
    (hSyl : L34Lemma43SylowStepS) (hFus : L34Lemma43FusionStepI)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) {a x : G} {J S A : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hrun : L34Sec4Running J A) (h3 : IsThreeConnected (S ⊓ withKernel J)) {W : Subgroup G}
    (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G))
    (hincl : L34ConjKernelIncl a J S W) (hSM : IsSylowTwoIn S (normalizer (W : Set G))) :
    False := by
  obtain ⟨hbase, hU3, hL34, hmax, -, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hMtop : M ≠ ⊤ := GrS4.normalizer_ne_top_of_odd hW hWodd ha2
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hCaM : centralizer ({a} : Set G) ≤ M := hCaN.trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨T, hTS⟩ := hSyl G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ hSM
  have hfus := hFus G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ hincl hSM ⟨T, hTS⟩
  have hfix : ∃! ω : G ⧸ M, a • ω = ω := by
    refine ⟨QuotientGroup.mk 1, ?_, fun ω' hω' => ?_⟩
    · show a • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa using inv_mem haM
    induction ω' using QuotientGroup.induction_on with
    | H g =>
    have h : a • (QuotientGroup.mk g : G ⧸ M) = QuotientGroup.mk g := hω'
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
    rw [QuotientGroup.eq, mul_one]
    have h1 : g⁻¹ * a * g ∈ M := by
      have h2 := inv_mem h
      rwa [show ((a * g)⁻¹ * g)⁻¹ = g⁻¹ * a * g by group] at h2
    obtain ⟨m, hm, hgm⟩ := hfus g h1
    have hc : g * m⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * m⁻¹ * a = g * (m⁻¹ * a * m) * m⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * m⁻¹ := by rw [← hgm]
        _ = a * (g * m⁻¹) := by group
    have h3 := mul_mem (hCaM hc) hm
    rw [inv_mul_cancel_right] at h3
    exact inv_mem h3
  have hTa : ∃ T' : Sylow 2 G, a ∈ (T' : Subgroup G) ∧
      (T' : Subgroup G) ≤ centralizer ({a} : Set G) :=
    ⟨T, by rw [hTS]; exact haS, by
      rw [hTS]
      exact fun s hs => mem_centralizer_singleton_iff.mpr (hcent s hs)⟩
  rcases hHS G hnab M hMtop a ha2 hTa hfix with ⟨M', hM'⟩ | ⟨n, -, ⟨e⟩⟩
  · obtain ⟨-, ⟨hAe, hA8⟩, -⟩ := hrun
    obtain ⟨V, hVA, hV4⟩ := exists_le_card_four hAe.isPGroup (by omega)
    have hJ1 : J ≠ ⊥ := by
      intro hJb
      have hd : Nat.card (↥J ⧸ Open.fusionZStar ↥J) ∣ Nat.card ↥J :=
        Subgroup.card_quotient_dvd_card _
      rw [CatLeaf.card_of_isL34Type hL34, hJb, Subgroup.card_bot] at hd
      norm_num at hd
    exact GrS5S.false_of_isStronglyEmbedded_perfect hM' hV4
      (fun v hv => by rw [pow_two]; exact hAe.2 v (hVA hv)) ha2 hJa
      (GSThmB.commutator_eq_self_of_isPComponent hJa hJc) hJ1
  · exact GrS5S.false_of_mulEquiv_alternatingGroup_l34 e ha2 hJa hCaN hJc hL34

end CFSG.ComponentClassification.GrSLit.KSw
