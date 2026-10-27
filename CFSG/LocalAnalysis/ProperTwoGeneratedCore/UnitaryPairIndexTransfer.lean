module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexInner
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PairHullCommonCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineTorusCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Transfer

open Matrix CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryHulls
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.PairHullCommonCentralizer
open CFSG.ProperTwoGeneratedCore.HighRankPair
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Model
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Inner
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_comm_of_isElementaryAbelian {U : Subgroup G} (hU : IsElementaryAbelian 2 U)
    {x y : G} (hx : x ∈ U) (hy : y ∈ U) : x * y = y * x := by
  have := hU.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem unitary_pair_torus_in_wz
    {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1) {w : G}
    (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hwt : Commute w t)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1)
    (hKv : Subgroup.centralizer ({w * z} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z (w * z) : Set G) =
      Subgroup.zpowers (w * z))
    (hoddv : CFSG.oddCore (localInvolutionPointHull z (w * z)) = ⊥)
    {f : ℕ} (hf : 2 ≤ f) (hq : Nat.card ({1} ∪ distinguishedRoots H z w : Set G) = 2 ^ f)
    {W₀ : Subgroup G} (hW₀L : W₀ ≤ localInvolutionPointHull z w)
    (hW₀U : ∀ x ∈ W₀, ∀ y ∈ ({1} ∪ distinguishedRoots H z w : Set G), x * y = y * x)
    (hW₀card : Nat.card W₀ = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (J : HermitianForm 3 k)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
      Nat.card k = (2 ^ f) ^ 2 ∧ Nat.card {x : k // J.conj x = x} = 2 ^ f ∧
      W₀ ≤ localInvolutionPointHull z (w * z) ∧
      ∃ θ : J.specialSubgroup ⧸ scalarCenter J ≃* localInvolutionPointHull z (w * z),
        (W₀.subgroupOf (localInvolutionPointHull z (w * z))).map θ.symm.toMonoidHom =
          torusL J (scalarCenter J) hJ := by
  classical
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  have htclass : t ∈ involutionPointClass z := ht.1
  have hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta := by
    rw [LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate]
    exact ht.2
  have hesc := original_pair_centralizer_escapes H beta hbeta w t hwt hflip
  have htH : t ∉ H := not_mem_of_mem_rightPairFlipFiber hbeta ht
  have hbeta_eq : beta = rightCosetMk H t := by
    rw [← ht.2, rightCosetTranslate_mk, one_mul]
  have hzH := h.local_datum.distinguished_mem
  have hz2 := h.local_datum.distinguished_order
  have hwH : w ∈ H := by
    have := hwB.1
    rwa [rightCosetStabilizer_base] at this
  have hww : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hvH : w * z ∈ H := H.mul_mem hwH hzH
  have hvz : Commute (w * z) z := hwz.mul_left (Commute.refl z)
  have hwz_ne : w ≠ z := by
    intro hwz'
    have hzβ : z ∈ rightCosetStabilizer H beta := hwz' ▸ hwB.2
    rw [hbeta_eq, rightCosetStabilizer_mk] at hzβ
    exact htH ((h.local_datum.unique_containment t).mp hzβ)
  have hv2 : orderOf (w * z) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · rw [pow_two]
      calc w * z * (w * z) = w * (z * w) * z := by group
        _ = w * (w * z) * z := by rw [← hwz.eq]
        _ = 1 := by rw [← mul_assoc, hww, one_mul, hzz]
    · intro h1
      apply hwz_ne
      rw [← mul_inv_eq_one, ← h1, mul_right_inj, inv_eq_of_mul_eq_one_left hzz]
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, U, hU, helem, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hwzclass, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hR1
      beta hbeta hrank hwB hw hwz hesc R T₁
  have hUset : (U : Set G) = {1} ∪ distinguishedRoots H z w := by
    rw [hU]
    ext x
    simp only [distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hUcomm : ∀ x ∈ ({1} ∪ distinguishedRoots H z w : Set G),
      ∀ y ∈ ({1} ∪ distinguishedRoots H z w : Set G), x * y = y * x := by
    intro x hx y hy
    rw [← hUset] at hx hy
    exact mul_comm_of_isElementaryAbelian helem hx hy
  have hzU : z ∈ ({1} ∪ distinguishedRoots H z w : Set G) :=
    Or.inr ⟨⟨distinguished_mem_pointClass z, hzH⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hwz.symm.eq⟩
  obtain ⟨-, -, -, -, -, hΔY, -, -⟩ :=
    minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hR1 hwH hw hwz hesc
  obtain ⟨g', hg'₀⟩ := hwzclass
  have hg' : rightConjugateElem w g' = w * z := hg'₀
  have hfixv : Nat.card (elementFixedSet H (w * z)) = Nat.card (elementFixedSet H w) := by
    rw [← hg']
    exact (Nat.card_congr (elementFixedSetConjugateEquiv H w g')).symm
  have hαv : rightCosetMk H 1 ∈ elementFixedSet H (w * z) :=
    (mem_rightCosetStabilizer_iff_pointRightCosetMul H _ (w * z)).mp
      (by rw [rightCosetStabilizer_base]; exact hvH)
  have hvesc : ¬ Subgroup.centralizer ({w * z} : Set G) ≤ H := by
    intro hle
    have hα' : pointRightCosetMul H (rightCosetMk H 1) g'⁻¹ ∈ elementFixedSet H w := by
      rw [← elementFixedSet_conjugate_iff, hg']
      exact hαv
    have hcard2 : 1 < Nat.card (elementFixedSet H w) := by
      rw [hdeg]
      have : 0 < Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 := by
        rw [hq]
        positivity
      omega
    have : Nontrivial (elementFixedSet H w) := Finite.one_lt_card_iff_nontrivial.mp hcard2
    obtain ⟨γ, hγ⟩ := exists_ne (⟨_, hα'⟩ : elementFixedSet H w)
    have h1 := hα'
    rw [hΔY] at h1
    obtain ⟨y₁, hy₁, hy₁α⟩ := h1
    have h2 : (γ : pointRightCosetSpace H) ∈ numeratorRightOrbit H
        (Subgroup.centralizer ({w} : Set G)) (rightCosetMk H 1) := by
      rw [← hΔY]
      exact γ.2
    obtain ⟨y₂, hy₂, hy₂α⟩ := h2
    have hm : y₁⁻¹ * y₂ ∈ Subgroup.centralizer ({w} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hy₁) hy₂
    have hyv : g'⁻¹ * (y₁⁻¹ * y₂) * g' ∈ Subgroup.centralizer ({w * z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg']
      have hm' := Subgroup.mem_centralizer_singleton_iff.mp hm
      simp only [rightConjugateElem]
      calc g'⁻¹ * (y₁⁻¹ * y₂) * g' * (g'⁻¹ * w * g') = g'⁻¹ * ((y₁⁻¹ * y₂) * w) * g' := by
            group
        _ = g'⁻¹ * (w * (y₁⁻¹ * y₂)) * g' := by rw [hm']
        _ = g'⁻¹ * w * g' * (g'⁻¹ * (y₁⁻¹ * y₂) * g') := by group
    have hyH := hle hyv
    have hfixα : pointRightCosetMul H (rightCosetMk H 1) (g'⁻¹ * (y₁⁻¹ * y₂) * g') =
        rightCosetMk H 1 :=
      (mem_rightCosetStabilizer_iff_pointRightCosetMul H _ _).mp
        (by rw [rightCosetStabilizer_base]; exact hyH)
    have h3 : pointRightCosetMul H (pointRightCosetMul H (rightCosetMk H 1) g'⁻¹)
        (y₁⁻¹ * y₂) = pointRightCosetMul H (rightCosetMk H 1) g'⁻¹ := by
      have := congrArg (fun ω => pointRightCosetMul H ω g'⁻¹) hfixα
      simp only [pointRightCosetMul_mul] at this ⊢
      rw [← this]
      congr 1
      group
    rw [← hy₁α, pointRightCosetMul_mul] at h3
    apply hγ
    apply Subtype.ext
    change (γ : pointRightCosetSpace H) = pointRightCosetMul H (rightCosetMk H 1) g'⁻¹
    rw [← hy₂α, ← hy₁α, ← h3]
    congr 1
    group
  obtain ⟨-, -, -, -, -, -, -, hxor⟩ :=
    minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hR1 hvH hv2 hvz hvesc
  have hcommv : ∀ y ∈ distinguishedRoots H z w, Commute y (w * z) := by
    intro y hy
    have hyw : Commute y w := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hyz : Commute y z := hUcomm y (Or.inr hy) z hzU
    exact hyw.mul_right hyz
  rcases hxor with ⟨⟨-, hDHY, -⟩, -⟩ | ⟨⟨-, Uv, hUv, helemv, -, -, -, -, -, hmodelsv, -⟩, -⟩
  ·
    exfalso
    obtain ⟨y, hyU, hy1, hyz⟩ : ∃ y ∈ ({1} ∪ distinguishedRoots H z w : Set G),
        y ≠ 1 ∧ y ≠ z := by
      by_contra hcon
      push Not at hcon
      have hsub : ({1} ∪ distinguishedRoots H z w : Set G) ⊆ {1, z} := fun y hy => by
        by_cases h1 : y = 1
        · exact Or.inl h1
        · exact Or.inr (hcon y hy h1)
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, hq] at h1
      have h2 : ({1, z} : Set G).ncard ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    have hyD : y ∈ distinguishedRoots H z w := hyU.resolve_left hy1
    have hy' : y ∈ involutionPointClass z ∩ (H : Set G) ∩
        (Subgroup.centralizer ({w * z} : Set G) : Set G) :=
      ⟨hyD.1, Subgroup.mem_centralizer_singleton_iff.mpr (hcommv y hyD).eq⟩
    rw [hDHY] at hy'
    exact hyz hy'
  have hzUv : z ∈ Uv := by
    rw [← SetLike.mem_coe, hUv]
    exact Or.inr ⟨⟨distinguished_mem_pointClass z, hzH⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hvz.symm.eq⟩
  have hUvset : (Uv : Set G) = {1} ∪ distinguishedRoots H z w := by
    rw [hUv]
    ext y
    constructor
    · rintro (hy | ⟨⟨hyD, hyH⟩, hyv⟩)
      · exact Or.inl hy
      · refine Or.inr ⟨⟨hyD, hyH⟩, ?_⟩
        have hyUv : y ∈ Uv := by
          rw [← SetLike.mem_coe, hUv]
          exact Or.inr ⟨⟨hyD, hyH⟩, hyv⟩
        have hyz : y * z = z * y := mul_comm_of_isElementaryAbelian helemv hyUv hzUv
        have hcv : Commute y (w * z) := Subgroup.mem_centralizer_singleton_iff.mp hyv
        have hcw : Commute y (w * z * z⁻¹) := hcv.mul_right (Commute.inv_right hyz)
        rw [mul_inv_cancel_right] at hcw
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcw.eq
    · rintro (hy | hy)
      · exact Or.inl hy
      · exact Or.inr ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr (hcommv y hy).eq⟩
  have hUvcard : Nat.card Uv = 2 ^ f := by
    rw [← hq, ← hUvset]
    rfl
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hfixv' : Nat.card (elementFixedSet H (w * z)) = (2 ^ f) ^ 3 + 1 := by
    rw [hfixv, hdeg, hq]
  rcases hmodelsv with ⟨hΔ1, -⟩ | ⟨hΔ2, -⟩ |
      ⟨-, f', hf', hUvf', K, _, _, A, hA, hK, hfixK, ρ, hρ, E, ψ, hψα, hψ⟩
  · exfalso
    rw [hfixv', hUvcard] at hΔ1
    have : (2 ^ f) ^ 1 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rw [pow_one] at this
    omega
  · exfalso
    rw [hfixv', hUvcard] at hΔ2
    have : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hff : f' = f := by
    have := hUvf'.symm.trans hUvcard
    exact Nat.pow_right_injective le_rfl this
  subst hff
  have hK' : Nat.card K = (2 ^ f') ^ 2 := by rw [hK, hUvcard]
  have hfixK' : Nat.card {x : K // A.conj x = x} = 2 ^ f' := by rw [hfixK, hUvcard]
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f' * 2) (by
    rw [← Nat.card_eq_fintype_card, hK', ← pow_mul])
  obtain ⟨θ₀, hθ₀⟩ := exists_cover_point_of_model hαv hoddv A hA ρ hρ E ψ hψα hψ
  have hroot : ∀ y ∈ ({1} ∪ distinguishedRoots H z w : Set G),
      ∃ hyL : y ∈ localInvolutionPointHull z (w * z),
        θ₀.symm ⟨y, hyL⟩ ∈ upperRootL A (scalarCenter A) hA := by
    rintro y (hy | hy)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨(localInvolutionPointHull z (w * z)).one_mem, ?_⟩
      rw [show (⟨1, (localInvolutionPointHull z (w * z)).one_mem⟩ :
        localInvolutionPointHull z (w * z)) = 1 from rfl, map_one]
      exact Subgroup.one_mem _
    · have hyL : y ∈ localInvolutionPointHull z (w * z) :=
        mem_localInvolutionPointHull hy.1.1 (hcommv y hy)
      refine ⟨hyL, ?_⟩
      have hy2 : orderOf y = 2 := order_two_of_mem_pointClass hz2 hy.1.1
      have hyy : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
      apply mem_upperRootL_of_sq hf' hK' hfixK' hA le_rfl
      · rw [← hθ₀, MulEquiv.apply_symm_apply]
        exact hy.1.2
      · apply θ₀.injective
        apply Subtype.ext
        rw [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, hyy, map_one, Subgroup.coe_one]
  have hQU : ∀ x ∈ upperRootL A (scalarCenter A) hA,
      ((θ₀ x : localInvolutionPointHull z (w * z)) : G) ∈
        ({1} ∪ distinguishedRoots H z w : Set G) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQcard⟩ :=
      unitary_central_cover_subline_torus_centralizer A f' hf' hK' hfixK' hA (scalarCenter A)
        le_rfl
    set S₁ : Set G := (fun x => ((θ₀ x : localInvolutionPointHull z (w * z)) : G)) ''
      (upperRootL A (scalarCenter A) hA : Set (A.specialSubgroup ⧸ scalarCenter A)) with hS₁
    have hinj : Function.Injective
        (fun x => ((θ₀ x : localInvolutionPointHull z (w * z)) : G)) :=
      Subtype.val_injective.comp θ₀.injective
    have hsub : ({1} ∪ distinguishedRoots H z w : Set G) ⊆ S₁ := by
      intro y hy
      obtain ⟨hyL, hyQ⟩ := hroot y hy
      exact ⟨_, hyQ, by simp⟩
    have hS₁card : S₁.ncard = 2 ^ f' := by
      rw [hS₁, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
      exact hQcard
    have heq : ({1} ∪ distinguishedRoots H z w : Set G) = S₁ := by
      apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
      rw [hS₁card, ← hq, Nat.card_coe_set_eq]
    intro x hx
    rw [heq]
    exact ⟨x, hx, rfl⟩
  have hW₀w : ∀ x ∈ W₀, Commute x w := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (localInvolutionPointHull_le_centralizer z w (hW₀L hx)))
  have hW₀v : W₀ ≤ Subgroup.centralizer ({w * z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hW₀w x hx).mul_right (hW₀U x hx z hzU)).eq
  have hW₀N : W₀ ≤ Subgroup.normalizer (localInvolutionPointHull z (w * z) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    have hav : Commute a (w * z) := Subgroup.mem_centralizer_singleton_iff.mp (hW₀v ha)
    intro l
    constructor
    · intro hl
      have := conj_mem_localHull_of_commute (z := z) hav.inv_left hl
      simpa only [inv_inv] using this
    · intro hl
      have := conj_mem_localHull_of_commute (z := z) hav hl
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
  have hWQ : ∀ a ∈ W₀, ∀ x ∈ upperRootL A (scalarCenter A) hA,
      a * ((θ₀ x : localInvolutionPointHull z (w * z)) : G) =
        ((θ₀ x : localInvolutionPointHull z (w * z)) : G) * a :=
    fun a ha x hx => hW₀U a ha _ (hQU x hx)
  have hWpow : ∀ a ∈ W₀, a ^ ((2 ^ f' + 1) / Nat.gcd 3 (2 ^ f' + 1)) = 1 := by
    intro a ha
    rw [← hW₀card]
    have := pow_card_eq_one' (G := W₀) (x := ⟨a, ha⟩)
    exact congrArg Subtype.val this
  obtain ⟨hW₀Lv, hWR⟩ := le_hull_and_mem_root_torus hf' hK' hfixK' hA θ₀ hv2
    (localInvolutionPointHull_le_centralizer z (w * z)) hKv hW₀v hW₀N hWQ hWpow
  obtain ⟨θ, hθ⟩ := exists_cover_eq_torusL hf' hK' hfixK' hA θ₀ hW₀Lv hWR hW₀card
  exact ⟨K, inferInstance, inferInstance, inferInstance, A, hA, hK', hfixK', hW₀Lv, θ, hθ⟩

theorem unitary_pair_torus_in_wt
    {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1) {w : G}
    (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hwt : Commute w t)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1)
    (hKv : Subgroup.centralizer ({w * z} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z (w * z) : Set G) =
      Subgroup.zpowers (w * z))
    (hoddv : CFSG.oddCore (localInvolutionPointHull z (w * z)) = ⊥)
    {f : ℕ} (hf : 2 ≤ f) (hq : Nat.card ({1} ∪ distinguishedRoots H z w : Set G) = 2 ^ f)
    {W₀ : Subgroup G} (hW₀L : W₀ ≤ localInvolutionPointHull z w)
    (hW₀U : ∀ x ∈ W₀, ∀ y ∈ ({1} ∪ distinguishedRoots H z w : Set G), x * y = y * x)
    (hW₀card : Nat.card W₀ = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1))
    {g : G} (hgL : g ∈ localInvolutionPointHull z w) (hgz : g⁻¹ * z * g = t)
    (hgW : ∀ x ∈ W₀, g * x = x * g) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (J : HermitianForm 3 k)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
      Nat.card k = (2 ^ f) ^ 2 ∧ Nat.card {x : k // J.conj x = x} = 2 ^ f ∧
      W₀ ≤ localInvolutionPointHull z (w * t) ∧
      ∃ φ : localInvolutionPointHull z (w * t) ≃* J.specialSubgroup ⧸ scalarCenter J,
        (W₀.subgroupOf (localInvolutionPointHull z (w * t))).map φ.toMonoidHom =
          torusL J (scalarCenter J) hJ := by
  obtain ⟨k, _, _, _, J, hJ, hk, hfix, hW₀Lv, θ, hθ⟩ :=
    unitary_pair_torus_in_wz h hbeta ht hrank hwB hw hwz hwt hdeg hKv hoddv hf hq hW₀L hW₀U
      hW₀card
  have hgw : g * w = w * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (localInvolutionPointHull_le_centralizer z w hgL)
  have hvg : rightConjugateElem (w * z) g = w * t := by
    rw [← hgz]
    simp only [rightConjugateElem]
    calc g⁻¹ * (w * z) * g = (g⁻¹ * w * g) * (g⁻¹ * z * g) := by group
      _ = w * (g⁻¹ * z * g) := by
        rw [show g⁻¹ * w * g = w by rw [mul_assoc, ← hgw, inv_mul_cancel_left]]
  set e : localInvolutionPointHull z (w * z) ≃* localInvolutionPointHull z (w * t) :=
    (localHullConjugateEquiv z (w * z) g).trans
      (MulEquiv.subgroupCongr (congrArg (localInvolutionPointHull z) hvg)) with he
  have heapp : ∀ x : localInvolutionPointHull z (w * z), (e x : G) = g⁻¹ * x * g := fun x => rfl
  have hfixg : ∀ x ∈ W₀, g⁻¹ * x * g = x := by
    intro x hx
    rw [mul_assoc, ← hgW x hx, inv_mul_cancel_left]
  have hW₀t : W₀ ≤ localInvolutionPointHull z (w * t) := by
    intro x hx
    have := (e ⟨x, hW₀Lv hx⟩).2
    rwa [heapp, hfixg x hx] at this
  have hesymm : ∀ x (hx : x ∈ W₀), e.symm ⟨x, hW₀t hx⟩ = ⟨x, hW₀Lv hx⟩ := by
    intro x hx
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [heapp, hfixg x hx]
  refine ⟨k, inferInstance, inferInstance, inferInstance, J, hJ, hk, hfix, hW₀t,
    e.symm.trans θ.symm, ?_⟩
  rw [← hθ]
  ext y
  constructor
  · rintro ⟨⟨x, hxL⟩, hxW, rfl⟩
    refine ⟨⟨x, hW₀Lv hxW⟩, hxW, ?_⟩
    change θ.symm ⟨x, hW₀Lv hxW⟩ = θ.symm (e.symm ⟨x, hxL⟩)
    rw [hesymm x hxW]
  · rintro ⟨⟨x, hxL⟩, hxW, rfl⟩
    refine ⟨⟨x, hW₀t hxW⟩, hxW, ?_⟩
    change θ.symm (e.symm ⟨x, hW₀t hxW⟩) = θ.symm ⟨x, hxL⟩
    rw [hesymm x hxW]

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Transfer
