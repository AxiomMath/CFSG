module

public import CFSG.CharacterTheory.Wreathed.CentralizerFullQuotient
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.CharacterTheory.Semidihedral.CentralizerAlternatives
public import CFSG.CharacterTheory.Semidihedral.FourPointLifts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateSemilinear

public noncomputable section

namespace CFSG.Wreathed.FourPointResidual

open Matrix CFSG.Wreathed
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u

theorem coordinate_line_three_card : Nat.card (Omega (ZMod 3)) = 4 := by
  simp [Omega, Nat.card_eq_fintype_card]

theorem coordinate_group_three_card : Nat.card (coordinateG (ZMod 3)) = 12 := by
  rw [← Nat.card_congr (pslEquivCoordinateG (ZMod 3)).toEquiv]
  exact CFSG.GorensteinWalter.nat_card_psl2_zmod3

theorem coordinate_group_three_eq_alternating :
    coordinateG (ZMod 3) = alternatingGroup (Omega (ZMod 3)) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hperm : Nat.card (Equiv.Perm (Omega (ZMod 3))) = 24 := by
    rw [Nat.card_perm, coordinate_line_three_card]
    decide
  have h := Subgroup.card_mul_index (coordinateG (ZMod 3))
  rw [coordinate_group_three_card, hperm] at h
  omega

theorem coordinate_general_three_eq_top : coordinateD (ZMod 3) = ⊤ := by
  have hcard : Nat.card (coordinateD (ZMod 3)) = 24 := by
    rw [← Nat.card_congr (pglEquivCoordinateD (ZMod 3)).toEquiv]
    exact CFSG.GorensteinWalter.nat_card_pgl2_zmod3
  have hperm : Nat.card (Equiv.Perm (Omega (ZMod 3))) = 24 := by
    rw [Nat.card_perm, coordinate_line_three_card]
    decide
  apply Subgroup.index_eq_one.mp
  have h := Subgroup.card_mul_index (coordinateD (ZMod 3))
  rw [hcard, hperm] at h
  omega

theorem coordinate_semilinear_three_eq_top : coordinateE (ZMod 3) = ⊤ := by
  apply top_unique
  rw [← coordinate_general_three_eq_top]
  exact coordinateD_le_E (ZMod 3)

variable {G : Type u} [Group G] [Finite G]

theorem four_point_parameter (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) : n = 2 := by
  have h := CFSG.Semidihedral.CentralizerAlternatives.n_eq_four_of_symmetricFour
    (n + 2) (by omega) (centralizerFullQuotientSylow n hn S e)
    (by rw [show n + 2 - 2 = n by omega]; exact centralizerFullQuotientSylowEquiv n hn S e)
    alpha
  omega

theorem four_point_quotient_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) :
    Nat.card (centralizerFullQuotient n hn S e) = 24 :=
  (Nat.card_congr alpha.toEquiv).trans
    CFSG.Semidihedral.CentralizerAlternatives.symmetricFour_card

theorem four_point_centralizer_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) :
    Nat.card (centralizerOddCoreQuotient n S e) = 96 := by
  have h := Subgroup.card_mul_index (centralizerFullCenterImage n hn S e)
  rw [centralizerFullCenterImage_card n hn S e, Subgroup.index_eq_card] at h
  have hq := four_point_quotient_card n hn S e alpha
  change Nat.card (centralizerOddCoreQuotient n S e ⧸ centralizerFullCenterImage n hn S e) = 24 at hq
  have hpow : 2 ^ n = 4 := by rw [four_point_parameter n hn S e alpha]; decide
  rw [hq, hpow] at h
  norm_num at h
  exact h.symm

theorem four_point_residual_card [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) :
    Nat.card (centralizerResidualImage n hn S e) = 24 := by
  have h := Subgroup.card_mul_index (centralizerResidualImage n hn S e)
  rw [centralizerResidualImage_index hnonab n hn S e,
    four_point_centralizer_card n hn S e alpha] at h
  have hpow : 2 ^ n = 4 := by rw [four_point_parameter n hn S e alpha]; decide
  rw [hpow] at h
  omega

@[expose] def coordinateAction (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    centralizerFullQuotient n hn S e ≃* Equiv.Perm (Omega (ZMod 3)) :=
  alpha.trans b.permCongrHom

theorem coordinateAction_apply (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) (g : centralizerFullQuotient n hn S e)
    (x : Omega (ZMod 3)) :
    coordinateAction n hn S e alpha b g x = b (alpha g (b.symm x)) := rfl

theorem coordinateAction_range (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    (coordinateAction n hn S e alpha b).toMonoidHom.range = coordinateE (ZMod 3) := by
  rw [coordinate_semilinear_three_eq_top]
  exact MonoidHom.range_eq_top.mpr (coordinateAction n hn S e alpha b).surjective

variable [IsSimpleGroup G]

theorem coordinateAction_residual_image (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    (centralizerDihedralImage n hn S e).map
      (coordinateAction n hn S e alpha b).toMonoidHom = coordinateG (ZMod 3) := by
  rw [coordinate_group_three_eq_alternating]
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  exact ((centralizerDihedralImage n hn S e).index_map_of_bijective
    (coordinateAction n hn S e alpha b).bijective).trans
      (centralizerDihedralImage_index hnonab n hn S e)

@[expose] def coordinateResidualEquiv (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    centralizerDihedralImage n hn S e ≃* coordinateG (ZMod 3) :=
  ((centralizerDihedralImage n hn S e).equivMapOfInjective
    (coordinateAction n hn S e alpha b).toMonoidHom
    (coordinateAction n hn S e alpha b).injective).trans
      (MulEquiv.subgroupCongr (coordinateAction_residual_image hnonab n hn S e alpha b))

@[expose] def residualCoordinateMap (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    centralizerResidualImage n hn S e →* coordinateG (ZMod 3) :=
  (coordinateResidualEquiv hnonab n hn S e alpha b).toMonoidHom.comp
    (centralizerDihedralImageMap n hn S e)

theorem residualCoordinateMap_coe (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) (t : centralizerResidualImage n hn S e) :
    (residualCoordinateMap hnonab n hn S e alpha b t : Equiv.Perm (Omega (ZMod 3))) =
      coordinateAction n hn S e alpha b (centralizerFullQuotientMap n hn S e (t :
        centralizerOddCoreQuotient n S e)) := rfl

theorem residualCoordinateMap_surjective (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    Function.Surjective (residualCoordinateMap hnonab n hn S e alpha b) :=
  (coordinateResidualEquiv hnonab n hn S e alpha b).surjective.comp
    (centralizerDihedralImageMap_surjective n hn S e)

theorem residualCoordinateMap_ker (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    (residualCoordinateMap hnonab n hn S e alpha b).ker =
      Subgroup.zpowers (centralizerResidualInvolution hnonab n hn S e) := by
  rw [residualCoordinateMap, MonoidHom.ker_comp_of_injective _ _
    (coordinateResidualEquiv hnonab n hn S e alpha b).injective]
  change ((QuotientGroup.mk' (centralizerFullCenterImage n hn S e)).subgroupMap
    (centralizerResidualImage n hn S e)).ker = _
  rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers]
  change centralizerFullCenterImage n hn S e ⊓ centralizerResidualImage n hn S e =
    Subgroup.zpowers (centralizerResidualInvolution hnonab n hn S e :
      centralizerOddCoreQuotient n S e)
  rw [centralizerResidualInvolution_coe]
  exact centralizerFullCenterImage_inf_residualImage hnonab n hn S e

@[expose] def residualProjectiveMap (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    centralizerResidualImage n hn S e →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3) :=
  (pslEquivCoordinateG (ZMod 3)).symm.toMonoidHom.comp
    (residualCoordinateMap hnonab n hn S e alpha b)

theorem residualProjectiveMap_surjective (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    Function.Surjective (residualProjectiveMap hnonab n hn S e alpha b) :=
  (pslEquivCoordinateG (ZMod 3)).symm.surjective.comp
    (residualCoordinateMap_surjective hnonab n hn S e alpha b)

theorem residualProjectiveMap_ker (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    (residualProjectiveMap hnonab n hn S e alpha b).ker =
      Subgroup.zpowers (centralizerResidualInvolution hnonab n hn S e) := by
  rw [residualProjectiveMap, MonoidHom.ker_comp_of_injective _ _
    (pslEquivCoordinateG (ZMod 3)).symm.injective,
    residualCoordinateMap_ker hnonab n hn S e alpha b]

@[expose] def residualQuaternionEightEquiv (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) :
    centralizerResidualSylow hnonab n hn S e ≃* QuaternionGroup (2 ^ (3 - 2)) := by
  have hpar : 2 ^ n / 2 = 2 ^ (3 - 2) := by
    rw [four_point_parameter n hn S e alpha]
    decide
  rw [← hpar]
  exact (centralizerResidualQuaternionEquiv hnonab n hn S e).symm

theorem exists_compatible_residual_sl2 (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    ∃ eta : centralizerResidualImage n hn S e ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient (ZMod 3)).comp eta.toMonoidHom =
        residualProjectiveMap hnonab n hn S e alpha b ∧
      eta (centralizerResidualInvolution hnonab n hn S e) =
        CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3) := by
  exact CFSG.Semidihedral.ProjectiveSL2Cover.quaternion_central_double_cover_native
    (ZMod 3) (by rw [ZMod.ringChar_zmod_n]; decide)
    (centralizerResidualInvolution hnonab n hn S e)
    (centralizerResidualInvolution_order hnonab n hn S e)
    (centralizerResidualInvolution_mem_center hnonab n hn S e)
    (residualProjectiveMap hnonab n hn S e alpha b)
    (residualProjectiveMap_surjective hnonab n hn S e alpha b)
    (residualProjectiveMap_ker hnonab n hn S e alpha b)
    (centralizerResidualSylow hnonab n hn S e) 3 (by decide)
    (residualQuaternionEightEquiv hnonab n hn S e alpha)

theorem exists_compatible_residual_sl2_action (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))
    (b : Fin 4 ≃ Omega (ZMod 3)) :
    ∃ eta : centralizerResidualImage n hn S e ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      eta (centralizerResidualInvolution hnonab n hn S e) =
        CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3) ∧
      ∀ t : centralizerResidualImage n hn S e,
        coordinatePSLAction (ZMod 3)
          (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient (ZMod 3) (eta t)) =
        coordinateAction n hn S e alpha b
          (centralizerFullQuotientMap n hn S e (t : centralizerOddCoreQuotient n S e)) := by
  obtain ⟨eta, hprojective, hinvolution⟩ :=
    exists_compatible_residual_sl2 hnonab n hn S e alpha b
  refine ⟨eta, hinvolution, ?_⟩
  intro t
  have hvalue := DFunLike.congr_fun hprojective t
  change CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient (ZMod 3) (eta t) =
    residualProjectiveMap hnonab n hn S e alpha b t at hvalue
  rw [hvalue]
  change ((pslEquivCoordinateG (ZMod 3))
    ((pslEquivCoordinateG (ZMod 3)).symm
      (residualCoordinateMap hnonab n hn S e alpha b t)) :
        Equiv.Perm (Omega (ZMod 3))) = _
  rw [MulEquiv.apply_symm_apply]
  exact residualCoordinateMap_coe hnonab n hn S e alpha b t

end CFSG.Wreathed.FourPointResidual

namespace CFSG.Wreathed.FourPointResidual

open Matrix CFSG.Wreathed
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u

variable {G : Type u} [Group G] [Finite G]

@[expose] def centralInvolutionInFullCenter [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenterImage n hn S e :=
  ⟨centralizerOddCoreMap n S e (centralInvolution n S e), by
    have h := Subgroup.mem_zpowers (centralizerOddCoreMap n S e (centralInvolution n S e))
    rw [← centralizerFullCenterImage_inf_residualImage hnonab n hn S e] at h
    exact h.1⟩

theorem centralInvolutionInFullCenter_coe [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralInvolutionInFullCenter hnonab n hn S e : centralizerOddCoreQuotient n S e) =
      centralizerOddCoreMap n S e (centralInvolution n S e) := rfl

@[expose] def residualCentralProductAmbient (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (centralizerFullCenterImage n hn S e) × SpecialLinearGroup (Fin 2) (ZMod 3) →*
      centralizerOddCoreQuotient n S e :=
  MonoidHom.noncommCoprod (centralizerFullCenterImage n hn S e).subtype
    ((centralizerResidualImage n hn S e).subtype.comp eta.symm.toMonoidHom)
    (fun a B => (Subgroup.mem_center_iff.mp
      ((centralizerFullCenterImage_le_center_and_factorization n hn S e).1 a.property)
      (eta.symm B : centralizerOddCoreQuotient n S e)).symm)

@[expose] def residualCentralProductMap (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (centralizerFullCenterImage n hn S e) × SpecialLinearGroup (Fin 2) (ZMod 3) →*
      ↥(centralizerFullCenterImage n hn S e ⊔ centralizerResidualImage n hn S e) :=
  (residualCentralProductAmbient n hn S e eta).codRestrict _ (fun p =>
    Subgroup.mul_mem_sup p.1.property (eta.symm p.2).property)

theorem residualCentralProductMap_coe (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3))
    (a : centralizerFullCenterImage n hn S e) (B : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (residualCentralProductMap n hn S e eta (a, B) :
      centralizerOddCoreQuotient n S e) =
        (a : centralizerOddCoreQuotient n S e) * (eta.symm B : centralizerOddCoreQuotient n S e) := rfl

theorem residualCentralProductMap_surjective (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3)) :
    Function.Surjective (residualCentralProductMap n hn S e eta) := by
  intro c
  obtain ⟨a, ha, t, ht, hmul⟩ := Subgroup.mem_sup_of_normal_right.mp c.property
  refine ⟨(⟨a, ha⟩, eta ⟨t, ht⟩), ?_⟩
  apply Subtype.ext
  rw [residualCentralProductMap_coe, eta.symm_apply_apply]
  exact hmul

variable [IsSimpleGroup G]

theorem centralInvolutionInFullCenter_order (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (centralInvolutionInFullCenter hnonab n hn S e) = 2 := by
  have h := centralizerResidualInvolution_order hnonab n hn S e
  rw [← Subgroup.orderOf_coe, centralizerResidualInvolution_coe] at h
  rw [← Subgroup.orderOf_coe, centralInvolutionInFullCenter_coe]
  exact h

@[expose] def residualCentralProductDiagonal (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerFullCenterImage n hn S e) × SpecialLinearGroup (Fin 2) (ZMod 3) :=
  (centralInvolutionInFullCenter hnonab n hn S e,
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3))

theorem residualCentralProductDiagonal_order (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (residualCentralProductDiagonal hnonab n hn S e) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · apply Prod.ext
    · have h := pow_orderOf_eq_one (centralInvolutionInFullCenter hnonab n hn S e)
      rw [centralInvolutionInFullCenter_order hnonab n hn S e] at h
      exact h
    · exact CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_square (ZMod 3)
  · intro h
    have hfst := congrArg Prod.fst h
    have hord := centralInvolutionInFullCenter_order hnonab n hn S e
    change centralInvolutionInFullCenter hnonab n hn S e = 1 at hfst
    rw [hfst, orderOf_one] at hord
    omega

theorem residualCentralProductMap_ker (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3))
    (heta : eta (centralizerResidualInvolution hnonab n hn S e) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3)) :
    (residualCentralProductMap n hn S e eta).ker =
      Subgroup.zpowers (residualCentralProductDiagonal hnonab n hn S e) := by
  ext p
  rw [CFSG.Semidihedral.FourPointLifts.mem_zpowers_order_two_iff _ _
    (residualCentralProductDiagonal_order hnonab n hn S e)]
  change residualCentralProductMap n hn S e eta p = 1 ↔ _
  rw [Subtype.ext_iff]
  change (p.1 : centralizerOddCoreQuotient n S e) *
    (eta.symm p.2 : centralizerOddCoreQuotient n S e) = 1 ↔ _
  constructor
  · intro hp
    have ha : (p.1 : centralizerOddCoreQuotient n S e) ∈
        centralizerFullCenterImage n hn S e ⊓ centralizerResidualImage n hn S e := by
      refine ⟨p.1.property, ?_⟩
      rw [mul_eq_one_iff_eq_inv.mp hp]
      exact (centralizerResidualImage n hn S e).inv_mem (eta.symm p.2).property
    rw [centralizerFullCenterImage_inf_residualImage hnonab n hn S e] at ha
    have hz : orderOf (centralizerOddCoreMap n S e (centralInvolution n S e)) = 2 := by
      rw [← centralizerResidualInvolution_coe hnonab n hn S e,
        Subgroup.orderOf_coe]
      exact centralizerResidualInvolution_order hnonab n hn S e
    rcases (CFSG.Semidihedral.FourPointLifts.mem_zpowers_order_two_iff _ _ hz).mp ha with h1 | hx
    · left
      have ha1 : p.1 = 1 := Subtype.ext h1
      have ht1 : eta.symm p.2 = 1 := by
        apply Subtype.ext
        simpa only [h1, one_mul, Subgroup.coe_one] using hp
      have hb1 : p.2 = 1 := by
        apply eta.symm.injective
        simpa only [map_one] using ht1
      exact Prod.ext ha1 hb1
    · right
      have hax : p.1 = centralInvolutionInFullCenter hnonab n hn S e := Subtype.ext hx
      have htx : eta.symm p.2 = centralizerResidualInvolution hnonab n hn S e := by
        apply Subtype.ext
        have h := mul_eq_one_iff_eq_inv'.mp hp
        rw [hx, ← centralizerResidualInvolution_coe hnonab n hn S e] at h
        have hi : (centralizerResidualInvolution hnonab n hn S e)⁻¹ =
            centralizerResidualInvolution hnonab n hn S e := by
          apply inv_eq_of_mul_eq_one_left
          simpa only [pow_two, centralizerResidualInvolution_order hnonab n hn S e]
            using pow_orderOf_eq_one (centralizerResidualInvolution hnonab n hn S e)
        simpa only [← Subgroup.coe_inv, hi] using h
      have hbx : p.2 = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3) := by
        rw [← heta, ← htx, eta.apply_symm_apply]
      exact Prod.ext hax hbx
  · rintro (rfl | rfl)
    · simp
    · change (centralInvolutionInFullCenter hnonab n hn S e : centralizerOddCoreQuotient n S e) *
        (eta.symm (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3)) :
          centralizerOddCoreQuotient n S e) = 1
      rw [← heta, eta.symm_apply_apply, centralInvolutionInFullCenter_coe,
        centralizerResidualInvolution_coe]
      have h := pow_orderOf_eq_one (centralizerResidualInvolution hnonab n hn S e)
      rw [centralizerResidualInvolution_order hnonab n hn S e, pow_two] at h
      simpa only [Subgroup.coe_mul, centralizerResidualInvolution_coe, Subgroup.coe_one]
        using congrArg Subtype.val h

theorem residualCentralProductDiagonal_mem_center (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    residualCentralProductDiagonal hnonab n hn S e ∈
      Subgroup.center ((centralizerFullCenterImage n hn S e) ×
        SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  apply Subgroup.mem_center_iff.mpr
  intro p
  apply Prod.ext
  · change p.1 * centralInvolutionInFullCenter hnonab n hn S e =
      centralInvolutionInFullCenter hnonab n hn S e * p.1
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      ((centralizerFullCenterImage_le_center_and_factorization n hn S e).1
        (centralInvolutionInFullCenter hnonab n hn S e).property) p.1
  · exact Subgroup.mem_center_iff.mp
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_mem_center (ZMod 3)) p.2

instance residualCentralProductDiagonal_normal (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.zpowers (residualCentralProductDiagonal hnonab n hn S e)).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr
    (residualCentralProductDiagonal_mem_center hnonab n hn S e))

@[expose] def residualCentralProductEquiv (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3))
    (heta : eta (centralizerResidualInvolution hnonab n hn S e) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3)) :
    ((centralizerFullCenterImage n hn S e) × SpecialLinearGroup (Fin 2) (ZMod 3)) ⧸
      Subgroup.zpowers (residualCentralProductDiagonal hnonab n hn S e) ≃*
        ↥(centralizerFullCenterImage n hn S e ⊔ centralizerResidualImage n hn S e) :=
  QuotientGroup.liftEquiv _ (residualCentralProductMap_surjective n hn S e eta)
    (residualCentralProductMap_ker hnonab n hn S e eta heta).symm

theorem residualCentralProductEquiv_mk (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3))
    (heta : eta (centralizerResidualInvolution hnonab n hn S e) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3))
    (p : (centralizerFullCenterImage n hn S e) × SpecialLinearGroup (Fin 2) (ZMod 3)) :
    residualCentralProductEquiv hnonab n hn S e eta heta
        (QuotientGroup.mk' (Subgroup.zpowers (residualCentralProductDiagonal hnonab n hn S e)) p) =
      residualCentralProductMap n hn S e eta p := rfl

theorem residualCentralProductEquiv_mk_coe (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3))
    (heta : eta (centralizerResidualInvolution hnonab n hn S e) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3))
    (a : centralizerFullCenterImage n hn S e) (B : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (residualCentralProductEquiv hnonab n hn S e eta heta
        (QuotientGroup.mk' (Subgroup.zpowers (residualCentralProductDiagonal hnonab n hn S e))
          (a, B)) : centralizerOddCoreQuotient n S e) =
      (a : centralizerOddCoreQuotient n S e) *
        (eta.symm B : centralizerOddCoreQuotient n S e) := rfl

omit [IsSimpleGroup G] in
theorem four_point_center_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) :
    Nat.card (centralizerFullCenterImage n hn S e) = 4 := by
  rw [centralizerFullCenterImage_card n hn S e, four_point_parameter n hn S e alpha]
  decide

theorem four_point_residual_alternating (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) :
    (centralizerDihedralImage n hn S e).map alpha.toMonoidHom = alternatingGroup (Fin 4) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  exact ((centralizerDihedralImage n hn S e).index_map_of_bijective alpha.bijective).trans
    (centralizerDihedralImage_index hnonab n hn S e)

structure FourPointFullCenterResidualData (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) : Prop where
  parameter : n = 2
  full_center : centralizerFullCenterImage n hn S e =
    Subgroup.center (centralizerOddCoreQuotient n S e)
  center_cyclic : IsCyclic (centralizerFullCenterImage n hn S e)
  center_card : Nat.card (centralizerFullCenterImage n hn S e) = 4
  centralizer_card : Nat.card (centralizerOddCoreQuotient n S e) = 96
  kernel_exists : ∃ K : Subgroup (involutionCentralizer n S e),
    K.Normal ∧ centralizerOddCore n S e ≤ K ∧ K.index = 4 ∧
    (K.map (involutionCentralizer n S e).subtype) ⊓ (S : Subgroup G) = modelY S e ∧
    K.map (centralizerOddCoreMap n S e) = centralizerResidualImage n hn S e
  residual_card : Nat.card (centralizerResidualImage n hn S e) = 24
  center_residual_intersection :
    centralizerFullCenterImage n hn S e ⊓ centralizerResidualImage n hn S e =
      Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e))
  residual_alternating : (centralizerDihedralImage n hn S e).map alpha.toMonoidHom =
    alternatingGroup (Fin 4)
  product_index : (centralizerFullCenterImage n hn S e ⊔ centralizerResidualImage n hn S e).index = 2
  every_coordinate_bijection : ∀ b : Fin 4 ≃ Omega (ZMod 3),
    (coordinateAction n hn S e alpha b).toMonoidHom.range = coordinateE (ZMod 3) ∧
    (centralizerDihedralImage n hn S e).map
      (coordinateAction n hn S e alpha b).toMonoidHom = coordinateG (ZMod 3) ∧
    ∃ eta : centralizerResidualImage n hn S e ≃* SpecialLinearGroup (Fin 2) (ZMod 3),
      ∃ heta : eta (centralizerResidualInvolution hnonab n hn S e) =
        CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3),
      (∀ t : centralizerResidualImage n hn S e,
        coordinatePSLAction (ZMod 3)
          (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient (ZMod 3) (eta t)) =
        coordinateAction n hn S e alpha b
          (centralizerFullQuotientMap n hn S e (t : centralizerOddCoreQuotient n S e))) ∧
      Function.Surjective (residualCentralProductMap n hn S e eta) ∧
      (residualCentralProductMap n hn S e eta).ker =
        Subgroup.zpowers (residualCentralProductDiagonal hnonab n hn S e) ∧
      ∀ p : (centralizerFullCenterImage n hn S e) × SpecialLinearGroup (Fin 2) (ZMod 3),
        residualCentralProductEquiv hnonab n hn S e eta heta
          (QuotientGroup.mk' (Subgroup.zpowers (residualCentralProductDiagonal hnonab n hn S e)) p) =
        residualCentralProductMap n hn S e eta p

theorem four_point_full_center_quotient_actual_sl2_three_residual
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) :
    FourPointFullCenterResidualData hnonab n hn S e alpha := by
  refine ⟨four_point_parameter n hn S e alpha,
    (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e).symm,
    inferInstance, four_point_center_card n hn S e alpha,
    four_point_centralizer_card n hn S e alpha, ?_,
    four_point_residual_card hnonab n hn S e alpha,
    centralizerFullCenterImage_inf_residualImage hnonab n hn S e,
    four_point_residual_alternating hnonab n hn S e alpha,
    centralizerFullCenterImage_sup_residualImage_index hnonab n hn S e, ?_⟩
  · refine ⟨centralizerTransferKernel n hn S e, inferInstance,
      centralizerOddCore_le_transferKernel n hn S e, ?_,
      (wreathed_involution_centralizer_quaternion_two_residual hnonab n hn S e).ambient_intersection,
      rfl⟩
    rw [centralizerTransferKernel_index hnonab n hn S e,
      four_point_parameter n hn S e alpha]
    decide
  · intro b
    refine ⟨coordinateAction_range n hn S e alpha b,
      coordinateAction_residual_image hnonab n hn S e alpha b, ?_⟩
    obtain ⟨eta, heta, haction⟩ := exists_compatible_residual_sl2_action hnonab n hn S e alpha b
    exact ⟨eta, heta, haction, residualCentralProductMap_surjective n hn S e eta,
      residualCentralProductMap_ker hnonab n hn S e eta heta,
      residualCentralProductEquiv_mk hnonab n hn S e eta heta⟩

end CFSG.Wreathed.FourPointResidual
