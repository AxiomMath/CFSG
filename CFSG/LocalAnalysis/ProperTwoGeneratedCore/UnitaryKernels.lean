module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsArgument
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PointKernelRootProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairGenerationTheorem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoSectionEightFour

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryKernels

open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.RankOnePair
open CFSG.ProperTwoGeneratedCore.HighRankPair (distinguishedRoots rootCoset)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem unitary_pair_centralizer_hulls_have_involutory_kernels
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huE : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hut : Commute u t)
    (hdeg : Nat.card (elementFixedSet H u) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) ^ 3 + 1)
    (R : Sylow 2 ↥(localInvolutionPointHull z u ⊓ H))
    (Rv : Sylow 2 ↥(localInvolutionPointHull z (u * z) ⊓ H))
    (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) :
    let v := u * z
    let Lu := localInvolutionPointHull z u
    let Lv := localInvolutionPointHull z v
    let U : Set G := {1} ∪ distinguishedRoots H z u
    let q := Nat.card U
    let Rg := (R : Subgroup ↥(Lu ⊓ H)).map (Lu ⊓ H).subtype
    let Rvg := (Rv : Subgroup ↥(Lv ⊓ H)).map (Lv ⊓ H).subtype
    let A := (T₁ : Subgroup ↥(H ⊓ Subgroup.centralizer ({u} : Set G))).map
      (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype
    v ∈ involutionPointClass u ∧
      U = {1} ∪ distinguishedRoots H z v ∧
      (((CFSG.omega₁ (G := R) (p := 2)).map
        ((Lu ⊓ H).subtype.comp (R : Subgroup ↥(Lu ⊓ H)).subtype) : Subgroup G) : Set G) = U ∧
      (((CFSG.omega₁ (G := Rv) (p := 2)).map
        ((Lv ⊓ H).subtype.comp (Rv : Subgroup ↥(Lv ⊓ H)).subtype) : Subgroup G) : Set G) = U ∧
      Nat.card R = q ^ 3 ∧ Nat.card Rv = q ^ 3 ∧
      Lv.relIndex Rg ≤ 2 ∧ Lu.relIndex Rvg ≤ 2 ∧
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (Lu : Set G) =
        Subgroup.zpowers u ∧
      Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer (Lv : Set G) =
        Subgroup.zpowers v ∧
      CFSG.oddCore Lu = ⊥ ∧ CFSG.oddCore Lv = ⊥ ∧
      (A : Set G) ∩ ((Lu : Set G) * (Subgroup.centralizer (Lu : Set G) : Set G)) =
        ((Subgroup.zpowers u ⊔ Rg : Subgroup G) : Set G) ∧
      Disjoint (Subgroup.zpowers u) Rg ∧
      (∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Rg, Commute a b) ∧
      (∃ e : Subgroup.zpowers u × Rg ≃* ↥(Subgroup.zpowers u ⊔ Rg),
        ∀ (a : Subgroup.zpowers u) (b : Rg), (e (a, b) : G) = (a : G) * b) ∧
      Group.IsSolvable (Subgroup.centralizer (rootCoset H z u)) := by
  intro v Lu Lv U q Rg Rvg A
  classical
  have hcomm := HighRankPair.properStrongEmbeddingCommutingImages_holds G
  have hsmallerR1 := HighRankPair.smallerR1Full G
  have hgen : PairCommutatorGenerationTheorem G := fun H z h beta hbeta t ht => by
    rw [← minimalLocalFailureProperPairHull_eq_native]
    exact PairGeneration.pair_generated_hull_eq_top G H z h hbeta ht
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huE
  have hzH : z ∈ H := h.local_datum.distinguished_mem
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := point_centralizer_le h.local_datum
  have hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H := fun hle =>
    flip_not_mem_point hbeta ht (hle (Subgroup.mem_centralizer_singleton_iff.mpr hut.symm.eq))
  obtain ⟨-, -, -, -, -, Uu, hUuset, -, -, hΩR, hzUu, -, -, -, -, hOmT, -, -, -, -, -, -, -, -, -,
    hvclass, -⟩ := rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm
      hsmallerR1 beta hbeta hrank huE hu huz hescape R T₁
  have hUu : originalPointRoot H z u = Uu := closure_eq_of_coe_eq hUuset
  have hUset : U = (originalPointRoot H z u : Set G) := by
    change {1} ∪ distinguishedRoots H z u = _
    rw [hUu, hUuset, distinguishedRoots, Set.inter_right_comm]
  have hq : q = Nat.card (originalPointRoot H z u) := by
    change Nat.card ↥U = _
    rw [hUset]
    rfl
  have hfix' : Nat.card (elementFixedSet H u) = Nat.card (originalPointRoot H z u) ^ 3 + 1 := by
    rw [← hq]
    exact hdeg
  have hzU : z ∈ originalPointRoot H z u := by
    rw [hUu]
    exact hzUu.1
  have hHu := unitaryKernelHullData_of_pair h hcomm hsmallerR1 beta hbeta hrank huE hu huz
    hescape hfix'
  have hvH : v ∈ H := H.mul_mem huH hzH
  obtain ⟨beta', hbeta', hpairRank', hvE, hescape', hfixv, hcardv⟩ :=
    point_conj_partner_pair h beta hbeta hrank huE hu hescape hvH hvclass
  have hv2 : orderOf v = 2 := order_two_of_mem_pointClass hu hvclass
  have hvz : Commute v z := huz.mul_left (Commute.refl z)
  have hUle : originalPointRoot H z u ≤ originalPointRoot H z v := by
    rw [originalPointRoot, originalPointRoot]
    apply Subgroup.closure_mono
    rintro x ⟨⟨hxD, hxu⟩, hxH⟩
    refine ⟨⟨hxD, ?_⟩, hxH⟩
    have hxU : x ∈ originalPointRoot H z u := Subgroup.subset_closure ⟨⟨hxD, hxu⟩, hxH⟩
    have hxz : x * z = z * x := mul_comm_of_sq_eq_one (hHu.sq_eq_one x hxU)
      (hHu.sq_eq_one z hzU) (hHu.sq_eq_one _ (Subgroup.mul_mem _ hxU hzU))
    have hxu' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxu
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change x * (u * z) = u * z * x
    rw [← mul_assoc, hxu', mul_assoc, hxz, ← mul_assoc]
  have hUv : originalPointRoot H z v = originalPointRoot H z u :=
    (Subgroup.eq_of_le_of_card_ge hUle hcardv.le).symm
  have hfixv' : Nat.card (elementFixedSet H v) = Nat.card (originalPointRoot H z v) ^ 3 + 1 := by
    rw [hfixv, hcardv]
    exact hfix'
  have hHv := unitaryKernelHullData_of_pair h hcomm hsmallerR1 beta' hbeta' hpairRank' hvE hv2
    hvz hescape' hfixv'
  rw [hUv] at hHv
  obtain ⟨T₂⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({v} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, Uv, hUvset, -, -, hΩRv, -⟩ :=
    rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hsmallerR1 beta'
      hbeta' hpairRank' hvE hv2 hvz hescape' Rv T₂
  have hUv' : originalPointRoot H z v = Uv := closure_eq_of_coe_eq hUvset
  have hcc := pair_hull_centralizer_inf_eq_bot h hcomm hsmallerR1 hgen beta hbeta ht huE hu huz
    hut
  have hzz : z * z = 1 := by
    rw [← pow_two, ← h.local_datum.distinguished_order, pow_orderOf_eq_one]
  have hwuv : ∀ x : G, Commute x u → Commute x z → Commute x v := fun x hxu hxz =>
    hxu.mul_right hxz
  have hwvu : ∀ x : G, Commute x v → Commute x z → Commute x u := fun x hxv hxz => by
    have huv : u = v * z := by
      change u = u * z * z
      rw [mul_assoc, hzz, mul_one]
    rw [huv]
    exact hxv.mul_right hxz
  have hRu := hHu.sylow R
  have hRv := hHv.sylow Rv
  have hmemuv := unitary_root_mem_or_mul_mem_partner_hull hzU hwuv hHv hRu
  have hmemvu := unitary_root_mem_or_mul_mem_partner_hull hzU hwvu hHu hRv
  have hKv : Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer (Lv : Set G) =
      Subgroup.zpowers v := unitary_kernel_eq_zpowers_of_partner hCz hzU hwvu hHu hHv hcc hRu
    (exists_coset_of_mem_or_mul_mem hmemuv)
  have hKu : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (Lu : Set G) =
      Subgroup.zpowers u := unitary_kernel_eq_zpowers_of_partner hCz hzU hwuv hHv hHu
    (by rw [inf_comm]; exact hcc) hRv (exists_coset_of_mem_or_mul_mem hmemvu)
  have huA : u ∈ A := by
    have hu' : u ∈ (CFSG.omega₁ (G := T₁) (p := 2)).map
        ((H ⊓ Subgroup.centralizer ({u} : Set G)).subtype.comp (T₁ : Subgroup _).subtype) := by
      rw [hOmT]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
    obtain ⟨y, -, hy⟩ := hu'
    exact ⟨y, y.2, hy⟩
  have hdisj : Disjoint (Subgroup.zpowers u) Rg := by
    rw [Subgroup.disjoint_def]
    intro x hxu hxR
    rcases (mem_zpowers_involution_iff hu).mp hxu with h1 | h1
    · exact h1
    · subst h1
      exact absurd (hRu.le hxR).1 hHu.not_mem
  have hcommute : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Rg, Commute a b := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hub : Commute u b := (Subgroup.mem_centralizer_singleton_iff.mp
      (localInvolutionPointHull_le_centralizer z u (hRu.le hb).1)).symm
    exact hub.zpow_left k
  have hprod : ∀ b ∈ Subgroup.zpowers u ⊔ Rg,
      ∃ a ∈ Subgroup.zpowers u, ∃ r ∈ Rg, b = a * r := by
    intro b hb
    obtain ⟨⟨a, r⟩, hab⟩ := (commutingJoinEquiv _ _ hdisj hcommute).surjective ⟨b, hb⟩
    refine ⟨a, a.2, r, r.2, ?_⟩
    rw [← commutingJoinEquiv_apply _ _ hdisj hcommute a r, hab]
  have hB : Subgroup.centralizer (rootCoset H z u) =
      Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (originalPointRoot H z u : Set G) := by
    change Subgroup.centralizer ((fun x : G => u * x) '' U) = _
    rw [hUset, centralizer_image_mul_eq]
  refine ⟨hvclass, ?_, ?_, ?_, ?_, ?_, relIndex_le_two_of_mem_or_mul_mem hmemuv,
    relIndex_le_two_of_mem_or_mul_mem hmemvu, hKu, hKv,
    oddCore_eq_bot_of_kernel hu hHu.core_central hHu.not_mem hKu,
    oddCore_eq_bot_of_kernel hv2 hHv.core_central hHv.not_mem hKv,
    unitary_sylow_inter_hull_mul_centralizer hRu hKu hprod T₁ huA, hdisj, hcommute,
    ⟨commutingJoinEquiv _ _ hdisj hcommute,
      fun a b => commutingJoinEquiv_apply _ _ hdisj hcommute a b⟩, ?_⟩
  · rw [hUset, ← hUv, hUv', hUvset, distinguishedRoots, Set.inter_right_comm]
  · rw [hΩR, ← hUu, ← hUset]
  · rw [hΩRv, ← hUv', hUv, ← hUset]
  · rw [hq, ← hRu.card]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  · rw [hq, ← hRv.card]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  · rw [hB]
    exact centralizer_root_solvable hCz hzU hHu hRu hKu

theorem unitary_pair_hull_oddCore_eq_bot
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {w : G} (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hwt : Commute w t)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1) :
    CFSG.oddCore (localInvolutionPointHull z w) = ⊥ ∧
      CFSG.oddCore (localInvolutionPointHull z (w * z)) = ⊥ := by
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨Rv⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z (w * z) ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hodd, hoddv, -⟩ :=
    unitary_pair_centralizer_hulls_have_involutory_kernels h hbeta ht hrank hwB hw hwz hwt hdeg
      R Rv T₁
  exact ⟨hodd, hoddv⟩

theorem unitaryInvolutoryKernelsConclusion
    (G : Type) [Group G] [Finite G] :
    UnitaryPairIndex.UnitaryInvolutoryKernelsConclusion G := by
  intro H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨Rv⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z (w * z) ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, -, -, -, hKw, hKv, hodd, hoddv, -⟩ :=
    unitary_pair_centralizer_hulls_have_involutory_kernels h hbeta ht hrank hwB hw hwz hwt hdeg
      R Rv T₁
  exact ⟨hKw, hKv, hodd, hoddv⟩

end CFSG.ProperTwoGeneratedCore.UnitaryKernels
