module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexSL2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineTorusCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Torus

open Matrix CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryHulls
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.HighRankPair
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Model
open scoped LinearAlgebra.Projectivization

section Subline

variable {K : Type} [Field K] [Finite K] [CharP K 2] {J : HermitianForm 3 K}

theorem exists_mul_self_eq_fixed (a : unitaryCoverFixedField J) :
    ∃ b : unitaryCoverFixedField J, b * b = a := by
  obtain ⟨b, hb⟩ := isSquare_of_charTwo' (a : K)
  have ha : J.conj (a : K) = a := a.2
  have hbfix : J.conj b = b := by
    have h1 : (J.conj b + b) ^ 2 = 0 := by
      rw [add_pow_char, ← map_pow, sq, ← hb, ha, CharTwo.add_self_eq_zero]
    have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    exact CharTwo.add_eq_zero.mp h2
  exact ⟨⟨b, hbfix⟩, Subtype.ext hb.symm⟩

theorem exists_sublineL_conj {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {C : Subgroup J.specialSubgroup} [C.Normal]
    (hC : C ≤ scalarCenter J) {x y : J.specialSubgroup ⧸ C} (hx : x ∈ sublineL J C hJ)
    (hy : y ∈ sublineL J C hJ) (hxx : x * x = 1) (hx1 : x ≠ 1) (hyy : y * y = 1)
    (hy1 : y ≠ 1) : ∃ g ∈ sublineL J C hJ, g⁻¹ * x * g = y := by
  obtain ⟨-, -, -, -, -, ⟨e⟩, -⟩ :=
    unitary_central_cover_subline_torus_centralizer J f hf hcard hfixed hJ C hC
  set x' : sublineL J C hJ := ⟨x, hx⟩
  set y' : sublineL J C hJ := ⟨y, hy⟩
  have h2 : (2 : unitaryCoverFixedField J) = 0 := Subtype.ext (by
    change (2 : K) = 0
    exact CharTwo.two_eq_zero)
  have hx' : e x' * e x' = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hxx
  have hy' : e y' * e y' = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hyy
  have hx1' : e x' ≠ 1 := by
    rw [ne_eq, ← map_one e, e.injective.eq_iff]
    intro h
    exact hx1 (congrArg Subtype.val h)
  have hy1' : e y' ≠ 1 := by
    rw [ne_eq, ← map_one e, e.injective.eq_iff]
    intro h
    exact hy1 (congrArg Subtype.val h)
  obtain ⟨g₀, hg₀⟩ :=
    SL2.sl2_involutions_conj h2 exists_mul_self_eq_fixed hx' hx1' hy' hy1'
  refine ⟨(e.symm g₀ : J.specialSubgroup ⧸ C), (e.symm g₀).2, ?_⟩
  have : (e.symm g₀)⁻¹ * x' * e.symm g₀ = y' := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg₀]
  exact congrArg Subtype.val this

end Subline

variable {G : Type} [Group G] [Finite G]

theorem unitary_pair_hull_torus
    {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1) {w : G}
    (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hwt : Commute w t)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1)
    (hodd : CFSG.oddCore (localInvolutionPointHull z w) = ⊥) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card ({1} ∪ distinguishedRoots H z w : Set G) = 2 ^ f ∧
      ∃ W₀ : Subgroup G, W₀ ≤ pairPointStabilizer H beta ∧
        W₀ ≤ localInvolutionPointHull z w ∧ (∀ x ∈ W₀, x * t = t * x) ∧
        (∀ x ∈ W₀, ∀ y ∈ ({1} ∪ distinguishedRoots H z w : Set G), x * y = y * x) ∧
        (∀ x ∈ W₀, ∀ y ∈ localInvolutionPointHull z w ⊓ pairPointStabilizer H beta,
          x * y = y * x) ∧
        Nat.card W₀ = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) ∧
        ∃ g ∈ localInvolutionPointHull z w, g⁻¹ * z * g = t ∧ ∀ x ∈ W₀, g * x = x * g := by
  classical
  have htclass : t ∈ involutionPointClass z := ht.1
  have hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta := by
    rw [LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate]
    exact ht.2
  have hesc := LocalCriterionNumerator.original_pair_centralizer_escapes H beta hbeta w t hwt
    hflip
  obtain ⟨ht2, htL, -, -, -⟩ :=
    LocalCriterionNumerator.original_pair_local_hull_inputs h.local_datum beta hbeta w t hw hwz
      hwt htclass hflip
  have htH : t ∉ H := not_mem_of_mem_rightPairFlipFiber hbeta ht
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hbeta_eq : beta = rightCosetMk H t := by
    rw [← ht.2, rightCosetTranslate_mk, one_mul]
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, U, hU, -, hU4, -, -, hmodel, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) beta hbeta hrank hwB hw
      hwz hesc R T₁
  have hUset : (U : Set G) = {1} ∪ distinguishedRoots H z w := by
    rw [hU]
    ext x
    simp only [distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hUcard : Nat.card U = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) := by
    rw [← hUset]
    rfl
  rw [← hUcard] at hdeg
  have hlt2 : Nat.card U ^ 2 < Nat.card U ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hlt1 : Nat.card U < Nat.card U ^ 2 := by
    calc Nat.card U = Nat.card U ^ 1 := (pow_one _).symm
      _ < Nat.card U ^ 2 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rcases hmodel with ⟨hΓ, -⟩ | ⟨hΓ, -⟩ |
      ⟨-, f, hf, hUf, k, _, _, J, hJ, hk, hfixk, ρ, hρ, E, ψ, hψα, hψ⟩
  · omega
  · omega
  refine ⟨f, hf, hUcard.symm.trans hUf, ?_⟩
  have hk' : Nat.card k = (2 ^ f) ^ 2 := by rw [hk, hUf]
  have hfix' : Nat.card {x : k // J.conj x = x} = 2 ^ f := by rw [hfixk, hUf]
  let : Fintype k := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hk', ← pow_mul])
  have huα : rightCosetMk H 1 ∈ elementFixedSet H w :=
    (mem_rightCosetStabilizer_iff_pointRightCosetMul H _ w).mp hwB.1
  obtain ⟨θ₀, hθ₀⟩ := exists_cover_point_of_model huα hodd J hJ ρ hρ E ψ hψα hψ
  obtain ⟨θ, hmem, hflipθ⟩ := exists_flip_cover_of_cover htL htH J hJ hf hk' hfix' θ₀ hθ₀
  let F : UnitaryHullFrame H t (localInvolutionPointHull z w) (2 ^ f) :=
    { k := k, J := J, hJ := hJ, f := f, hf := hf, hq := rfl, hcard := hk', hfixed := hfix',
      C := scalarCenter J, hC := le_rfl, θ := θ, mem_point := hmem, flip := hflipθ }
  have hFE : ∀ x, ((θ x : (localInvolutionPointHull z w)) : G) ∈ pairPointStabilizer H beta ↔
      x ∈ pairStabilizerL J (scalarCenter J) hJ le_rfl :=
    F.mem_pairPointStabilizer_iff htL htt hbeta_eq
  set τ := θ.symm ⟨t, htL⟩ with hτ
  have hθτ : ((θ τ : localInvolutionPointHull z w) : G) = t := by
    rw [hτ, MulEquiv.apply_symm_apply]
  have hτ0 : coverToPGL J (scalarCenter J) hJ le_rfl τ • unitaryCoordinatePoint (K := k) 0 =
      unitaryCoordinatePoint 2 := hflipθ τ hθτ
  have hττ : τ * τ = 1 := by
    apply θ.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, hθτ, htt, map_one, Subgroup.coe_one]
  have hτ2 : coverToPGL J (scalarCenter J) hJ le_rfl τ • unitaryCoordinatePoint (K := k) 2 =
      unitaryCoordinatePoint 0 := by
    rw [← hτ0, ← mul_smul, ← map_mul, hττ, map_one, one_smul]
  have hτcomm : ∀ x ∈ torusL J (scalarCenter J) hJ, Commute τ x := fun x hx =>
    commute_torusL_of_swap hJ le_rfl hτ0 hτ2 hx
  have hroot : ∀ y ∈ ({1} ∪ distinguishedRoots H z w : Set G),
      ∃ hyL : y ∈ localInvolutionPointHull z w,
      θ.symm ⟨y, hyL⟩ ∈ upperRootL J (scalarCenter J) hJ := by
    rintro y (hy | ⟨⟨hyD, hyH⟩, hyw⟩)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨(localInvolutionPointHull z w).one_mem, ?_⟩
      rw [show (⟨1, (localInvolutionPointHull z w).one_mem⟩ : localInvolutionPointHull z w) = 1
        from rfl, map_one]
      exact Subgroup.one_mem _
    · have hyL : y ∈ (localInvolutionPointHull z w) := mem_localInvolutionPointHull hyD
        (Subgroup.mem_centralizer_singleton_iff.mp hyw)
      refine ⟨hyL, ?_⟩
      have hy2 : orderOf y = 2 := order_two_of_mem_pointClass h.local_datum.distinguished_order hyD
      have hyy : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
      apply mem_upperRootL_of_sq hf hk' hfix' hJ le_rfl
      · rw [← hmem, MulEquiv.apply_symm_apply]
        exact hyH
      · apply θ.injective
        apply Subtype.ext
        rw [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, hyy, map_one, Subgroup.coe_one]
  set W₀ : Subgroup G := (torusL J (scalarCenter J) hJ).map
      ((localInvolutionPointHull z w).subtype.comp θ.toMonoidHom)
    with hW₀
  have hmemW : ∀ x ∈ W₀, ∃ x' ∈ torusL J (scalarCenter J) hJ,
      ((θ x' : localInvolutionPointHull z w) : G) = x := by
    rintro _ ⟨x', hx', rfl⟩
    exact ⟨x', hx', rfl⟩
  refine ⟨W₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hFE x).mpr (torusL_le_pairStabilizerL hJ le_rfl hx)
  · rintro _ ⟨x, -, rfl⟩
    exact (θ x).2
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := hmemW x hx
    rw [← hθτ, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      (hτcomm x' hx').eq]
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hmemW x hx
    obtain ⟨hyL, hy'⟩ := hroot y hy
    have hc := sublineL_commute_torusL hJ _ (upperRootL_le_sublineL hJ hy') x' hx'
    have h1 : ((θ (θ.symm ⟨y, hyL⟩) : localInvolutionPointHull z w) : G) = y := by
      rw [MulEquiv.apply_symm_apply]
    rw [← h1, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hmemW x hx
    have hy' : θ.symm ⟨y, hy.1⟩ ∈ pairStabilizerL J (scalarCenter J) hJ le_rfl := by
      rw [← hFE, MulEquiv.apply_symm_apply]
      exact hy.2
    have hc := pairStabilizerL_commute hJ le_rfl (torusL_le_pairStabilizerL hJ le_rfl hx') hy'
    have h1 : ((θ (θ.symm ⟨y, hy.1⟩) : localInvolutionPointHull z w) : G) = y := by
      rw [MulEquiv.apply_symm_apply]
    rw [← h1, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc.eq]
  · have hinj : Function.Injective ((localInvolutionPointHull z w).subtype.comp θ.toMonoidHom) :=
      Subtype.val_injective.comp θ.injective
    rw [hW₀, Subgroup.card_map_of_injective hinj, card_torusL_scalarCenter hf hk' hfix' hJ]
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨p, -, -, -, A, -, -, -, -, c, hc3, -⟩, hcentr,
        -⟩ := unitary_central_cover_subline_torus_centralizer J f hf hk' hfix' hJ (scalarCenter J)
      le_rfl
    obtain ⟨-, -, hinvol⟩ := hcentr (torusL J (scalarCenter J) hJ) le_rfl ⟨c, hc3, ⟨c, rfl⟩⟩
    have hzU : z ∈ ({1} ∪ distinguishedRoots H z w : Set G) :=
      Or.inr ⟨⟨distinguished_mem_pointClass z, h.local_datum.distinguished_mem⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hwz.symm.eq⟩
    obtain ⟨hzL, hzQ⟩ := hroot z hzU
    have hτJ : τ ∈ sublineL J (scalarCenter J) hJ := by
      apply hinvol
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hτcomm y hy).eq.symm
      · rw [pow_two]
        exact hττ
    have hz1 : θ.symm ⟨z, hzL⟩ ≠ 1 := by
      intro h1
      have := congrArg (fun x => ((θ x : (localInvolutionPointHull z w)) : G)) h1
      simp only [MulEquiv.apply_symm_apply, map_one, Subgroup.coe_one] at this
      rw [this] at hzL
      have hz2 := h.local_datum.distinguished_order
      rw [this, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hτ1 : τ ≠ 1 := by
      intro h1
      rw [h1, map_one, Subgroup.coe_one] at hθτ
      rw [← hθτ, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have hzz : θ.symm ⟨z, hzL⟩ * θ.symm ⟨z, hzL⟩ = 1 := by
      apply θ.injective
      apply Subtype.ext
      rw [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, map_one, Subgroup.coe_one,
        ← pow_two, ← h.local_datum.distinguished_order, pow_orderOf_eq_one]
    obtain ⟨g', hg'J, hg'⟩ := exists_sublineL_conj hf hk' hfix' hJ le_rfl
      (upperRootL_le_sublineL hJ hzQ) hτJ hzz hz1 hττ hτ1
    refine ⟨((θ g' : (localInvolutionPointHull z w)) : G), (θ g').2, ?_, ?_⟩
    · have := congrArg (fun x => ((θ x : (localInvolutionPointHull z w)) : G)) hg'
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      rw [this, hθτ]
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := hmemW x hx
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
        sublineL_commute_torusL hJ g' hg'J x' hx']

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Torus
