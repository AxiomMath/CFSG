module

public import CFSG.CharacterTheory.Semidihedral.ReducedQuotients
public import CFSG.CharacterTheory.Semidihedral.ActualLayerOddExtensions
public import CFSG.CharacterTheory.Semidihedral.MatrixCover
public import CFSG.CharacterTheory.Semidihedral.Principal.ProjectiveLineFixedPoints

public section

namespace CFSG.Semidihedral.ActualSimpleLayerLocalPackage

noncomputable section

open CFSG.Open CFSG.Semidihedral
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.TwoRankLowerBound.Helpers CFSG.GorensteinWalter

universe u v

variable {G : Type u} [Group G]

abbrev C (t : G) := Subgroup.centralizer ({t} : Set G)

@[expose] def tInC (t : G) : C t :=
  ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem tInC_central (t : G) : tInC t ∈ Subgroup.center (C t) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.property)

abbrev N (t : G) := CFSG.pPrimeCore 2 (C t)

abbrev Z (t : G) := Subgroup.zpowers (tInC t)

instance Z_normal (t : G) : (Z t).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (tInC_central t))

abbrev NZ (t : G) := N t ⊔ Z t

instance NZ_normal (t : G) : (NZ t).Normal := Subgroup.sup_normal _ _

abbrev K (t : G) := CFSG.Semidihedral.primeResidual 2 (C t)

abbrev H (t : G) := C t ⧸ N t

abbrev Gamma (t : G) := C t ⧸ NZ t

abbrev nu (t : G) : C t →* H t := QuotientGroup.mk' (N t)

abbrev kappa (t : G) : C t →* Gamma t := QuotientGroup.mk' (NZ t)

@[expose] def barKappa (t : G) : H t →* Gamma t :=
  QuotientGroup.lift (N t) (kappa t)
    (by simpa only [QuotientGroup.ker_mk'] using (le_sup_left : N t ≤ NZ t))

theorem barKappa_nu (t : G) (x : C t) : barKappa t (nu t x) = kappa t x := rfl

theorem barKappa_comp_nu (t : G) : (barKappa t).comp (nu t) = kappa t := rfl

theorem barKappa_surjective (t : G) : Function.Surjective (barKappa t) := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (NZ t) x
  exact ⟨nu t c, rfl⟩

theorem barKappa_kernel (t : G) :
    (barKappa t).ker = Subgroup.zpowers (nu t (tInC t)) := by
  rw [barKappa, QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  change (N t ⊔ Z t).map (nu t) = _
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]

abbrev J (t : G) := (K t).map (kappa t)

abbrev T (t : G) := (K t).map (nu t)

instance J_normal (t : G) : (J t).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

instance T_normal (t : G) : (T t).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem K_eq_odd_order_closure (t : G) :
    K t = Subgroup.closure {x : C t | Odd (orderOf x)} := by
  rw [K, CFSG.Semidihedral.primeResidual]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, ← even_iff_two_dvd, Nat.not_even_iff_odd]

theorem simple_le_index_two {Q : Type v} [Group Q]
    (L J : Subgroup Q) [IsSimpleGroup L] (hJ : J.index = 2)
    (hnonab : ∃ a b : L, a * b ≠ b * a) : L ≤ J := by
  let : J.Normal := Subgroup.normal_of_index_eq_two hJ
  let q := QuotientGroup.mk' J
  let chi := q.comp L.subtype
  have hcard : Nat.card (Q ⧸ J) = 2 := hJ
  let : IsCyclic (Q ⧸ J) := isCyclic_of_prime_card hcard
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal chi.ker with hbot | htop
  · have hinj : Function.Injective chi := (MonoidHom.ker_eq_bot_iff chi).mp hbot
    obtain ⟨a, b, hab⟩ := hnonab
    exact False.elim (hab (hinj (by
      simpa only [map_mul] using
        (IsMulCommutative.is_comm.comm (chi a) (chi b)))))
  · intro x hx
    have hchi : chi (⟨x, hx⟩ : L) = 1 := by
      change (⟨x, hx⟩ : L) ∈ chi.ker
      rw [htop]
      exact Subgroup.mem_top _
    exact (QuotientGroup.eq_one_iff (N := J) (x := x)).mp hchi

theorem barKappa_preimage_J (t : G) (hNZK : NZ t ≤ K t) :
    (J t).comap (barKappa t) = T t := by
  apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (N t))
  rw [Subgroup.comap_comap, barKappa_comp_nu,
    Subgroup.comap_map_eq_self (by simpa only [QuotientGroup.ker_mk'] using hNZK),
    Subgroup.comap_map_eq_self (by
      simpa only [QuotientGroup.ker_mk'] using (le_sup_left.trans hNZK : N t ≤ K t))]

theorem actual_quotient_inputs [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2) :
    NZ t ≤ K t ∧ (J t).index = 2 ∧
      orderOf (nu t (tInC t)) = 2 ∧
      nu t (tInC t) ∈ Subgroup.center (H t) ∧
      (∀ x : (J t).comap (barKappa t),
        orderOf x = 2 → (x : H t) = nu t (tInC t)) ∧
      (∃ (P : Sylow 2 (Gamma t)),
        Nonempty (P ≃* DihedralGroup (2 ^ (n - 2)))) ∧
      (∃ (P : Sylow 2 (H t)), Nonempty (P ≃* SemidihedralGroup n)) := by
  obtain ⟨S, f, hcenter⟩ := InvolutionFusion.exists_centered_semidihedral_sylow
    n hn S0 f0 hG t ht
  have hcenter' : CentralizerResidual.centeredInvolution n S f = t := hcenter
  subst t
  have hNZK : NZ (CentralizerResidual.centeredInvolution n S f) ≤
      K (CentralizerResidual.centeredInvolution n S f) :=
    ReducedQuotients.centralizerFullKernel_le_residual n hn S f hG
  have hindex : (J (CentralizerResidual.centeredInvolution n S f)).index = 2 :=
    ReducedQuotients.reducedResidual_index n hn S f hG
  let P := CentralizerResidual.centralizerSylow n hn S f
  have hPz : tInC (CentralizerResidual.centeredInvolution n S f) ∈ P := by
    change CentralizerResidual.centralInvolution n S f ∈ P
    exact CentralQuotients.ambientZ_le_sylow P _
      (CentralizerResidual.centralInvolution_mem_center n S f)
      (CentralizerResidual.centralInvolution_order n hn S f)
      (Subgroup.mem_zpowers _)
  have hzorder : orderOf (nu (CentralizerResidual.centeredInvolution n S f)
      (tInC (CentralizerResidual.centeredInvolution n S f))) = 2 :=
    CoreResidual.coreQuotient_involution_order P _ hPz
      (CentralizerResidual.centralInvolution_order n hn S f)
  have hzcentral : nu (CentralizerResidual.centeredInvolution n S f)
      (tInC (CentralizerResidual.centeredInvolution n S f)) ∈
      Subgroup.center (H (CentralizerResidual.centeredInvolution n S f)) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
      (Subgroup.mem_map_of_mem _ (tInC_central _))
  refine ⟨hNZK, hindex, hzorder, hzcentral, ?_, ?_, ?_⟩
  · change ∀ x : (J (CentralizerResidual.centeredInvolution n S f)).comap
      (barKappa (CentralizerResidual.centeredInvolution n S f)),
      orderOf x = 2 → (x : H (CentralizerResidual.centeredInvolution n S f)) =
        nu (CentralizerResidual.centeredInvolution n S f)
          (tInC (CentralizerResidual.centeredInvolution n S f))
    intro x hx
    have hxT : x.val ∈
        T (CentralizerResidual.centeredInvolution n S f) := by
      rw [← barKappa_preimage_J _ hNZK]
      exact x.property
    let e := ReducedQuotients.primeResidualCoreQuotientEquiv
      (H := C (CentralizerResidual.centeredInvolution n S f)) 2
    let y := e.symm ⟨x.val, hxT⟩
    have hy : orderOf y = 2 := (e.symm.orderOf_eq _).trans
      ((Subgroup.orderOf_coe ⟨x.val, hxT⟩).symm.trans
        ((Subgroup.orderOf_coe x).trans hx))
    have hyz := (CoreResidual.residualCoreQuotient_involution_iff n hn S f hG y).mp hy
    have hyz' : y = QuotientGroup.mk' (pPrimeCore 2 (K
        (CentralizerResidual.centeredInvolution n S f)))
        (CoreResidual.residualInvolution n hn S f hG) := hyz
    change x.val = nu (CentralizerResidual.centeredInvolution n S f)
      (tInC (CentralizerResidual.centeredInvolution n S f))
    calc
      x.val = (e y : H (CentralizerResidual.centeredInvolution n S f)) :=
        (congrArg Subtype.val (e.apply_symm_apply ⟨x.val, hxT⟩)).symm
      _ = (e (QuotientGroup.mk' (pPrimeCore 2 (K
          (CentralizerResidual.centeredInvolution n S f)))
          (CoreResidual.residualInvolution n hn S f hG)) :
          H (CentralizerResidual.centeredInvolution n S f)) :=
        congrArg (fun v => (e v : H (CentralizerResidual.centeredInvolution n S f))) hyz'
      _ = nu (CentralizerResidual.centeredInvolution n S f)
          (tInC (CentralizerResidual.centeredInvolution n S f)) :=
        ReducedQuotients.primeResidualCoreQuotientEquiv_coe 2
          (CoreResidual.residualInvolution n hn S f hG)
  · exact ⟨ReducedQuotients.reducedCentralizerSylow n hn S f,
      ⟨(ReducedQuotients.reducedCentralizerDihedralEquiv n hn S f).symm⟩⟩
  · exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective _),
      ⟨(CoreResidual.coreQuotientSylowEquiv 2 P).symm.trans
        (CentralizerResidual.centralizerCoordinates n hn S f).symm⟩⟩

variable {t : G}

@[expose] def coordinateCover {Q : Type v} [Group Q]
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : Q →* Gamma t) (rho : Gamma t →* coordinateE F)
    (hrange : rho.range = OddFieldLift.Gamma F A) : Q →* OddFieldLift.Gamma F A :=
  ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp rho.rangeRestrict).comp pi

theorem coordinateCover_value {Q : Type v} [Group Q]
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : Q →* Gamma t) (rho : Gamma t →* coordinateE F)
    (hrange : rho.range = OddFieldLift.Gamma F A) (x : Q) :
    (coordinateCover F A pi rho hrange x : coordinateE F) = rho (pi x) := rfl

theorem coordinateCover_surjective {Q : Type v} [Group Q]
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : Q →* Gamma t) (hpi : Function.Surjective pi)
    (rho : Gamma t →* coordinateE F)
    (hrange : rho.range = OddFieldLift.Gamma F A) :
    Function.Surjective (coordinateCover F A pi rho hrange) :=
  ((MulEquiv.subgroupCongr hrange).surjective.comp
    rho.rangeRestrict_surjective).comp hpi

theorem coordinateCover_kernel {Q : Type v} [Group Q]
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : Q →* Gamma t) (rho : Gamma t →* coordinateE F)
    (hinj : Function.Injective rho)
    (hrange : rho.range = OddFieldLift.Gamma F A) :
    (coordinateCover F A pi rho hrange).ker = pi.ker := by
  apply MonoidHom.ker_comp_of_injective
  exact (MulEquiv.subgroupCongr hrange).injective.comp
    (MonoidHom.rangeRestrict_injective_iff.mpr hinj)

theorem coordinateCover_special_preimage
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (hinj : Function.Injective rho)
    (hrange : rho.range = OddFieldLift.Gamma F A)
    (hL : (CFSG.generalizedFitting (Gamma t)).map rho = specialLayer F) :
    OddFieldLift.Lambda F A (coordinateCover F A (barKappa t) rho hrange) =
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  ext x
  change rho (barKappa t x) ∈ specialLayer F ↔
    barKappa t x ∈ CFSG.generalizedFitting (Gamma t)
  rw [← hL]
  exact Subgroup.mem_map_iff_mem hinj

structure ActualMatrixData (t : G) (n p f : ℕ)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) : Prop where
  field_card : Nat.card F = p ^ f
  field_group_odd : Odd (Nat.card A)
  field_group_dvd : Nat.card A ∣ f
  faithful : Function.Injective rho
  layer_image : (CFSG.generalizedFitting (Gamma t)).map rho = specialLayer F
  full_image : rho.range = OddFieldLift.Gamma F A
  residual_image : (J t).map rho = OddFieldLift.SpecialGamma F A
  fixed_field_card : Nat.card (FixedPoints.subfield A F) = p ^ (f / Nat.card A)
  field_power : Nat.card F = (p ^ (f / Nat.card A)) ^ Nat.card A
  field_mod_eight : Nat.card F % 8 = p ^ (f / Nat.card A) % 8
  two_part : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 ^ (n - 1)
  fixed_two_part : 2 ^ ((p ^ (f / Nat.card A)) ^ 2 - 1).factorization 2 = 2 ^ (n - 1)
  compatible_layer :
    ∃ eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F,
      eta ⟨nu t (tInC t), QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
        (nu t (tInC t)) (barKappa t) (barKappa_kernel t)
          (CFSG.generalizedFitting (Gamma t))⟩ = -1 ∧
      (∀ x : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
        (rho (barKappa t x)).val =
          coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x))) ∧
      Nat.card (((J t).comap (barKappa t)) ⧸
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).subgroupOf
          ((J t).comap (barKappa t))) = Nat.card A
  every_coefficient : ∀ (a : (MatrixCover.FixedField F A)ˣ), ¬ IsSquare a →
    ¬ IsSquare (MatrixCover.fixedUnit F A a) ∧
    ∃ phi : MatrixCover.MatrixFieldModel F A a ≃* H t,
      phi (SemidirectProduct.inl
        (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A a)
          (OddFieldSL2.minusIdentity F))) = nu t (tInC t) ∧
      (phi.toMonoidHom.comp
        ((SemidirectProduct.inl : MatrixCoverData.M F (MatrixCover.fixedUnit F A a) →*
          MatrixCover.MatrixFieldModel F A a).comp
            (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A a)))).range =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ∧
      ∀ x : MatrixCover.MatrixFieldModel F A a,
        (rho (barKappa t (phi x)) : Equiv.Perm (Omega F)) =
          coordinatePGLAction F (Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL x.left.left *
              MatrixCoverData.J F (MatrixCover.fixedUnit F A a) ^
                MatrixCoverData.exponent x.left.right)) * fieldExtension F x.right

theorem actual_simple_layer_matrix_data
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F))
      (rho : Gamma t →* coordinateE F), ActualMatrixData t n p f F A rho := by
  obtain ⟨hNZK, hJindex, hz, hc, hunique, ⟨P, ⟨eP⟩⟩, S, ⟨eS⟩⟩ :=
    actual_quotient_inputs n hn S0 f0 hG t ht
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t :=
    simple_le_index_two _ _ hJindex hnonab
  have hp2 : p ≠ 2 := fun h => (by decide : ¬Odd (2 : ℕ)) (h ▸ hpodd)
  obtain ⟨_, _, _, _, F, hfield, hfinite, hcard, A, rho, eta,
      hAodd, hAdvd, hinj, hL, hrange, hJ, _, _, hetaz, heta,
      _, _, _, hTcard, _, _, htwo, hfixed, hpower, hmod, _, hfixedtwo⟩ :=
    ActualLayerOddExtensions.actual_linear_two_local_layer_odd_field_extension
      (nu t (tInC t)) hz hc (barKappa t) (barKappa_surjective t) (barKappa_kernel t)
      (n - 1) (by omega) P (by
        have he : n - 1 - 1 = n - 2 := by omega
        rw [he]
        exact eP) hnonab hcentral hnc (J t) hJindex
      hLJ hunique ⟨hp, hp2, hf⟩ hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  let pi := coordinateCover F A (barKappa t) rho hrange
  have hpi : Function.Surjective pi :=
    coordinateCover_surjective F A (barKappa t) (barKappa_surjective t) rho hrange
  have hpiker : pi.ker = Subgroup.zpowers (nu t (tInC t)) :=
    (coordinateCover_kernel F A (barKappa t) rho hinj hrange).trans (barKappa_kernel t)
  have hLambda := coordinateCover_special_preimage F A rho hinj hrange hL
  let eta' : OddFieldLift.Lambda F A pi ≃* MatrixCoverData.SL F :=
    (MulEquiv.subgroupCongr hLambda).trans eta
  have hetaz' : eta' ⟨nu t (tInC t), MatrixCover.kernel_le_Lambda F A pi
      (by rw [hpiker]; exact Subgroup.mem_zpowers _)⟩ = OddFieldSL2.minusIdentity F := by
    exact hetaz
  have heta' : ∀ x : OddFieldLift.Lambda F A pi,
      OddFieldLift.slCoordinateAction F (eta' x) = OddFieldLift.coordinateProjection F A pi x := by
    intro x
    exact (heta ((MulEquiv.subgroupCongr hLambda) x)).symm
  refine ⟨F, hfield, hfinite, A, rho, ?_⟩
  refine
    { field_card := hcard
      field_group_odd := hAodd
      field_group_dvd := hAdvd
      faithful := hinj
      layer_image := hL
      full_image := hrange
      residual_image := hJ
      fixed_field_card := hfixed
      field_power := hpower
      field_mod_eight := hmod
      two_part := htwo
      fixed_two_part := hfixedtwo
      compatible_layer := ⟨eta, hetaz, heta, hTcard⟩
      every_coefficient := ?_ }
  intro a ha
  obtain ⟨haF, _, u, _, _, _, _, phi, _, hphiz, hphilayer, _, hphicoord⟩ :=
    MatrixCover.semidihedral_local_cover_exact_matrix_field_model F p f hp hpodd hf
      hcard A hAodd pi hpi _ hz hc hpiker eta' hetaz' heta' S n hn eS a ha
  exact ⟨haF, phi, hphiz, hphilayer.trans hLambda, hphicoord⟩

theorem semidihedral_order_four_square (n : ℕ) (hn : 4 ≤ n)
    (x : SemidihedralGroup n) (hx : orderOf x = 4) : x ^ 2 = z n := by
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n (Nat.le_trans (by decide : 3 ≤ 4) hn)).symm.surjective x
  change orderOf (element n (by omega) i e) = 4 at hx
  change element n (by omega) i e ^ 2 = z n
  rcases exponent_cases e with rfl | rfl
  · have hs : orderOf (element n (by omega) i 0 ^ 2) = 2 := by
      rw [orderOf_pow' _ (by decide : (2 : ℕ) ≠ 0), hx]
      decide
    rw [element_rotation_pow] at hs ⊢
    rw [(rotation_involution_iff n (by omega) _).mp hs, ← z_eq_element n (by omega)]
  · rw [element_reflection_sq,
      (half_mul_eq_half_iff n (by omega) _).mpr
        ((outside_order_four_iff n (by omega) i).mp hx), ← z_eq_element n (by omega)]

theorem semidihedral_order_four_mem_quaternion (n : ℕ) (hn : 4 ≤ n)
    (x : SemidihedralGroup n) (hx : orderOf x = 4) : x ∈ quaternionSubgroup n := by
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n (Nat.le_trans (by decide : 3 ≤ 4) hn)).symm.surjective x
  change orderOf (element n (by omega) i e) = 4 at hx
  change element n (by omega) i e ∈ quaternionSubgroup n
  rcases exponent_cases e with rfl | rfl
  · have hj : i.val % 2 = 0 := by
      have hfour := (rotation_order_four_iff n hn i).mp hx
      rcases hfour with rfl | rfl
      · have hM : modulus n = 4 * 2 ^ (n - 3) := by
          rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_quarter (by omega)]
          ring
        have hq : 0 < 2 ^ (n - 3) := pow_pos (by decide) _
        rw [ZMod.val_natCast_of_lt (by omega)]
        exact Nat.even_iff.mp (quarter_even n hn)
      · have hM : modulus n = 4 * 2 ^ (n - 3) := by
          rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_quarter (by omega)]
          ring
        have hq : 0 < 2 ^ (n - 3) := pow_pos (by decide) _
        have hneg : -((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) =
            ((3 * 2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
          apply Eq.symm
          apply eq_neg_iff_add_eq_zero.mpr
          rw [← Nat.cast_add, show 3 * 2 ^ (n - 3) + 2 ^ (n - 3) = modulus n by omega]
          exact ZMod.natCast_self _
        rw [hneg, ZMod.val_natCast_of_lt (by omega)]
        exact Nat.even_iff.mp ((quarter_even n hn).mul_left 3)
    exact (element_mem_quaternionSubgroup_iff n (by omega) i 0).mpr (by simpa using hj)
  · exact (element_mem_quaternionSubgroup_iff n (by omega) i 1).mpr (by
      simpa only [ZMod.val_one] using (outside_order_four_iff n (by omega) i).mp hx)

theorem actual_residual_unique_involution [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (x : K t) (hx : orderOf x = 2) : (x : C t) = tInC t := by
  obtain ⟨S, f, hcenter⟩ := InvolutionFusion.exists_centered_semidihedral_sylow
    n hn S0 f0 hG t ht
  have hcenter' : CentralizerResidual.centeredInvolution n S f = t := hcenter
  subst t
  exact CentralizerResidual.oddResidual_unique_involution n hn S f hG x hx

theorem actual_noncentral_involution_not_mem_K [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (x : C t) (hx : orderOf x = 2) (hxt : x ≠ tInC t) : x ∉ K t := by
  intro hxK
  exact hxt (actual_residual_unique_involution n hn S0 f0 hG t ht
    ⟨x, hxK⟩ ((Subgroup.orderOf_coe ⟨x, hxK⟩).symm.trans hx))

theorem actual_order_four_residual_and_square [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (x : C t) (hx : orderOf x = 4) : x ∈ K t ∧ x ^ 2 = tInC t := by
  obtain ⟨S, f, hcenter⟩ := InvolutionFusion.exists_centered_semidihedral_sylow
    n hn S0 f0 hG t ht
  have hcenter' : CentralizerResidual.centeredInvolution n S f = t := hcenter
  subst t
  change CentralizerResidual.involutionCentralizer n S f at x
  change orderOf x = 4 at hx
  change x ∈ CentralizerResidual.oddResidual n S f ∧
    x ^ 2 = CentralizerResidual.centralInvolution n S f
  let P := CentralizerResidual.centralizerSylow n hn S f
  let e := CentralizerResidual.centralizerCoordinates n hn S f
  have htwo : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow P x htwo
  let a := e.symm y
  have ha : orderOf a = 4 := (e.symm.orderOf_eq y).trans
    ((Subgroup.orderOf_coe y).symm.trans ((conjugate_orderOf_eq hxy).symm.trans hx))
  have hyQ : (y : CentralizerResidual.involutionCentralizer n S f) ∈
      CentralizerResidual.centralizerQuaternion n hn S f := by
    rw [← CentralizerResidual.sylowQuaternion_map n hn S f]
    apply Subgroup.mem_map_of_mem
    change y ∈ Subgroup.closure {e (r n) ^ 2, e (r n) * e (s n)}
    rw [← map_quaternionSubgroup n e]
    have hm := Subgroup.mem_map_of_mem (e : SemidihedralGroup n →* P)
      (semidihedral_order_four_mem_quaternion n hn a ha)
    change e a ∈ (quaternionSubgroup n).map (e : SemidihedralGroup n →* P) at hm
    rw [show e a = y from e.apply_symm_apply y] at hm
    exact hm
  have hyK : (y : CentralizerResidual.involutionCentralizer n S f) ∈
      CentralizerResidual.oddResidual n S f :=
    CentralizerResidual.centralizerQuaternion_le_oddResidual n hn S f hG hyQ
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  refine ⟨?_, ?_⟩
  · have h := (inferInstance : (CentralizerResidual.oddResidual n S f).Normal).conj_mem'
      _ hyK c
    simpa only [← hc, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using h
  · have hysq : (y : CentralizerResidual.involutionCentralizer n S f) ^ 2 =
        CentralizerResidual.centralInvolution n S f := by
      rw [show y = e a from (e.apply_symm_apply y).symm]
      calc
        (e a : CentralizerResidual.involutionCentralizer n S f) ^ 2 =
            (e (a ^ 2) : CentralizerResidual.involutionCentralizer n S f) := by
          rw [map_pow, Subgroup.coe_pow]
        _ = CentralizerResidual.centralInvolution n S f := by
          rw [semidihedral_order_four_square n hn a ha]
          exact CentralizerResidual.centralizerCoordinates_z n hn S f
    apply (MulAut.conj c).injective
    change c * x ^ 2 * c⁻¹ =
      c * CentralizerResidual.centralInvolution n S f * c⁻¹
    rw [← conj_pow, hc, hysq,
      Subgroup.mem_center_iff.mp (CentralizerResidual.centralInvolution_mem_center n S f) c,
      mul_assoc, mul_inv_cancel, mul_one]

@[expose] def localAction
    (F : Type) [Field F] (rho : Gamma t →* coordinateE F) :
    C t →* Equiv.Perm (Omega F) := (coordinateE F).subtype.comp (rho.comp (kappa t))

@[expose] def localPhi
    (F : Type) [Field F] (rho : Gamma t →* coordinateE F) (c : C t) : ℂ :=
  (Nat.card {x : Omega F // localAction F rho c x = x} : ℂ) - 1

@[expose] def localDelta
    (F : Type) [Field F] (rho : Gamma t →* coordinateE F) (c : C t) : ℂ :=
  by classical
     exact if ∃ (d : coordinateD F) (sigma : F ≃+* F) (a : Matrix.GeneralLinearGroup (Fin 2) F),
      localAction F rho c = d * fieldExtension F sigma ∧
        coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F)
  then 1 else -1

@[expose] def localEpsilon (F : Type) : ℂ :=
  if Nat.card F % 4 = 1 then 1 else -1

@[expose] def permutationGamma
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :
    Subgroup (Equiv.Perm (Omega F)) :=
  (OddFieldLift.Gamma F A).map (coordinateE F).subtype

@[expose] def permutationCover
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F)
    (hrange : rho.range = OddFieldLift.Gamma F A) : C t →* permutationGamma F A :=
  ((OddFieldLift.Gamma F A).equivMapOfInjective
    (coordinateE F).subtype (coordinateE F).subtype_injective).toMonoidHom.comp
      (coordinateCover F A (kappa t) rho hrange)

theorem permutationCover_value
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F)
    (hrange : rho.range = OddFieldLift.Gamma F A) (c : C t) :
    (permutationCover F A rho hrange c : Equiv.Perm (Omega F)) = localAction F rho c := rfl

theorem permutationCover_surjective
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F)
    (hrange : rho.range = OddFieldLift.Gamma F A) :
    Function.Surjective (permutationCover F A rho hrange) :=
  ((OddFieldLift.Gamma F A).equivMapOfInjective
    (coordinateE F).subtype (coordinateE F).subtype_injective).surjective.comp
      (coordinateCover_surjective F A (kappa t) (QuotientGroup.mk'_surjective _)
        rho hrange)

theorem permutationCover_kernel
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (hinj : Function.Injective rho)
    (hrange : rho.range = OddFieldLift.Gamma F A) :
    (permutationCover F A rho hrange).ker = NZ t := by
  ext c
  change permutationCover F A rho hrange c = 1 ↔ c ∈ NZ t
  change ((OddFieldLift.Gamma F A).equivMapOfInjective
    (coordinateE F).subtype (coordinateE F).subtype_injective)
      (coordinateCover F A (kappa t) rho hrange c) = 1 ↔ c ∈ NZ t
  rw [map_eq_one_iff _ ((OddFieldLift.Gamma F A).equivMapOfInjective
    (coordinateE F).subtype (coordinateE F).subtype_injective).injective]
  change c ∈
    (coordinateCover F A (kappa t) rho hrange).ker ↔ _
  rw [coordinateCover_kernel F A (kappa t) rho hinj hrange, QuotientGroup.ker_mk']

theorem permutationGamma_contains_D
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :
    coordinateD F ≤ permutationGamma F A := by
  intro x hx
  exact ⟨⟨x, (coordinateD_le_E F) hx⟩,
    (le_sup_left : linearLayer F ≤ OddFieldLift.Gamma F A) hx, rfl⟩

theorem permutationGamma_le_E
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :
    permutationGamma F A ≤ coordinateE F := Subgroup.map_subtype_le _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem actual_four_character_input [Fintype (C t)]
    (F : Type) [Field F] [Fintype F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (hinj : Function.Injective rho)
    (hrange : rho.range = OddFieldLift.Gamma F A)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (basis : FiniteIrreducibleCharacterBasis (C t))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    (∃ lam : C t →* ℂˣ, ∀ c, (lam c : ℂ) = localDelta F rho c) ∧
    (∃ ldelta lphi ldeltaPhi : basis.index,
      (∀ c, (basis.representation ldelta).character c = localDelta F rho c) ∧
      (∀ c, (basis.representation lphi).character c = localPhi F rho c) ∧
      (∀ c, (basis.representation ldeltaPhi).character c =
        localDelta F rho c * localPhi F rho c) ∧
      [principal, ldelta, lphi, ldeltaPhi].Nodup ∧
      (∀ l ∈ [principal, ldelta, lphi, ldeltaPhi],
        (basis.representation l).IsIrreducible ∧
        l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
        ∀ c, ∃ z : ℤ, (basis.representation l).character c = z) ∧
      Module.finrank ℂ (basis.representation principal).vector = 1 ∧
      Module.finrank ℂ (basis.representation ldelta).vector = 1 ∧
      Module.finrank ℂ (basis.representation lphi).vector = p ^ f ∧
      Module.finrank ℂ (basis.representation ldeltaPhi).vector = p ^ f ∧
      MonoidHom.ker (basis.representation lphi).representation = NZ t ∧
      MonoidHom.ker (basis.representation ldeltaPhi).representation = NZ t) ∧
    (∀ c, localDelta F rho c * localDelta F rho c = 1) ∧
    (∀ c, Odd (orderOf c) → localDelta F rho c = 1) ∧
    (∀ (c : C t) (X : Matrix.SpecialLinearGroup (Fin 2) F),
      (X : Matrix (Fin 2) (Fin 2) F) * X = -1 →
      localAction F rho c = coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) →
      localPhi F rho c = localEpsilon F ∧
        localDelta F rho c * localPhi F rho c = localEpsilon F) ∧
    (∀ (c : C t) (a : F) (ha : a ≠ 0), ¬ IsSquare a →
      localAction F rho c = coordinateGLAction F (Principal.jMatrix a ha) →
      localDelta F rho c = -1 ∧ localPhi F rho c = -localEpsilon F ∧
        localDelta F rho c * localPhi F rho c = localEpsilon F) := by
  classical
  obtain ⟨_, hlam, _, hdsq, ⟨ld, lp, ldp, hd, hphi, hdp, hnodup,
      hP, hdeg1, hdegd, hdegp, hdegdp, hkerp, hkerdp⟩,
      _, _, _, hdodd, hX, hJ⟩ :=
    Principal.projective_linear_two_four_principal_odd_degree_characters
      hp hpodd hf F hcard (permutationGamma F A)
      (permutationGamma_contains_D F A) (permutationGamma_le_E F A)
      (permutationCover F A rho hrange) (permutationCover_surjective F A rho hrange)
      basis ideal principal hprincipal
  have hker := permutationCover_kernel F A rho hinj hrange
  simp only [permutationCover_value] at hlam hd hphi hdp hdsq hdodd hX hJ
  have hdelta : ∀ c : C t,
      (if ∃ (d : coordinateD F) (sigma : F ≃+* F)
        (a : Matrix.GeneralLinearGroup (Fin 2) F),
        localAction F rho c = d * fieldExtension F sigma ∧
        coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F)
      then (1 : ℂ) else -1) = localDelta F rho c := by
    intro c
    unfold localDelta
    by_cases h : ∃ (d : coordinateD F) (sigma : F ≃+* F)
      (a : Matrix.GeneralLinearGroup (Fin 2) F),
      localAction F rho c = d * fieldExtension F sigma ∧
      coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F)
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
  refine ⟨?_, ⟨ld, lp, ldp, ?_, ?_, ?_, hnodup, hP,
    hdeg1, hdegd, hcard ▸ hdegp, hcard ▸ hdegdp,
    hkerp.trans hker, hkerdp.trans hker⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [hdelta] using hlam
  · simpa only [hdelta] using hd
  · simpa only [localPhi] using hphi
  · simpa only [hdelta, localPhi] using hdp
  · simpa only [hdelta] using hdsq
  · simpa only [hdelta] using hdodd
  · simpa only [hdelta, localPhi, localEpsilon] using hX
  · simpa only [hdelta, localPhi, localEpsilon] using hJ

theorem specialGamma_iff_theta_first
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (hF : IsOddPrimePower (Nat.card F)) (e : coordinateE F)
    (he : e ∈ OddFieldLift.Gamma F A) :
    e ∈ OddFieldLift.SpecialGamma F A ↔ (theta F hF e).1 = 1 := by
  constructor
  · intro hs
    obtain ⟨g, hg, a, ha, hga⟩ := Subgroup.mem_sup_of_normal_left.mp hs
    obtain ⟨sigma, hsigma, rfl⟩ := ha
    have hg1 : theta F hF g = 1 := by
      apply MonoidHom.mem_ker.mp
      rwa [theta_ker]
    rw [← hga, map_mul, hg1, one_mul, theta_fieldLift]
  · intro h1
    obtain ⟨g, hg, a, ha, hga⟩ := Subgroup.mem_sup_of_normal_left.mp he
    obtain ⟨sigma, hsigma, rfl⟩ := ha
    have hg2 : (theta F hF g).2 = 1 := by
      rw [theta_snd]
      apply MonoidHom.mem_ker.mp
      rwa [fieldProjection_ker]
    have hg1 : (theta F hF g).1 = 1 := by
      rw [← hga, map_mul, theta_fieldLift] at h1
      simpa only [Prod.fst_mul, mul_one] using h1
    have hgs : g ∈ specialLayer F := by
      rw [show specialLayer F = (theta F hF).ker from (theta_ker F hF).symm]
      exact Prod.ext hg1 hg2
    rw [← hga]
    exact Subgroup.mul_mem _
      ((le_sup_left : specialLayer F ≤ OddFieldLift.SpecialGamma F A) hgs)
      ((le_sup_right : liftedField F A ≤ OddFieldLift.SpecialGamma F A)
        ⟨sigma, hsigma, rfl⟩)

theorem localDelta_eq_one_iff
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (hinj : Function.Injective rho)
    (hrange : rho.range = OddFieldLift.Gamma F A)
    (hJ : (J t).map rho = OddFieldLift.SpecialGamma F A)
    (hNZK : NZ t ≤ K t) (hF : IsOddPrimePower (Nat.card F)) (c : C t) :
    localDelta F rho c = 1 ↔ c ∈ K t := by
  classical
  have hnormal : localDelta F rho c = 1 ↔
      (theta F hF (rho (kappa t c))).1 = 1 := by
    rw [← Principal.normalForm_square_iff_theta F hF]
    change (if _ then (1 : ℂ) else -1) = 1 ↔ _
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · constructor
      · intro hbad
        norm_num at hbad
      · intro hbad
        exact False.elim (h hbad)
  rw [hnormal, ← specialGamma_iff_theta_first F A hF _
    (hrange ▸ ⟨kappa t c, rfl⟩), ← hJ]
  rw [Subgroup.mem_map_iff_mem hinj]
  change c ∈ (J t).comap (kappa t) ↔ c ∈ K t
  rw [J, Subgroup.comap_map_eq_self
    (by simpa only [QuotientGroup.ker_mk'] using hNZK)]

theorem localDelta_eq_neg_one_of_not_mem
    (F : Type) [Field F] (rho : Gamma t →* coordinateE F) (c : C t)
    (hc : localDelta F rho c ≠ 1) : localDelta F rho c = -1 := by
  classical
  unfold localDelta at hc ⊢
  split_ifs with h
  · exact False.elim (hc (by simp only [h, ↓reduceIte]))
  · rfl

theorem localPhi_on_NZ
    (F : Type) [Field F] [Finite F] (rho : Gamma t →* coordinateE F)
    (c : C t) (hc : c ∈ NZ t) : localPhi F rho c = Nat.card F := by
  let : Fintype F := Fintype.ofFinite F
  have hq : kappa t c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
  have hact : localAction F rho c = 1 := by
    change (coordinateE F).subtype (rho (kappa t c)) = 1
    rw [hq, map_one, map_one]
  have hcard : Nat.card {x : Omega F // localAction F rho c x = x} =
      Nat.card (Omega F) := by
    rw [hact]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
  rw [localPhi, hcard, Principal.card_omega]
  push_cast
  ring

theorem degree_one_character_kernel {Q : Type v} [Group Q] [Fintype Q]
    (basis : FiniteIrreducibleCharacterBasis Q) (l : basis.index)
    (hdegree : Module.finrank ℂ (basis.representation l).vector = 1)
    (lam : Q →* ℂˣ)
    (hlam : ∀ c, (basis.representation l).character c = (lam c : ℂ)) :
    MonoidHom.ker (basis.representation l).representation = lam.ker := by
  apply le_antisymm
  · intro c hc
    have hc' := MonoidHom.mem_ker.mp hc
    have hvalue : (basis.representation l).character c =
        (basis.representation l).character 1 := by
      change LinearMap.trace ℂ _ ((basis.representation l).representation c) =
        LinearMap.trace ℂ _ ((basis.representation l).representation 1)
      rw [hc', map_one (basis.representation l).representation]
    have h1 : (basis.representation l).character 1 = 1 := by
      change (basis.representation l).representation.character 1 = 1
      rw [Representation.char_one, hdegree, Nat.cast_one]
    rw [hlam, h1] at hvalue
    apply Units.ext
    exact hvalue
  · apply CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree
    intro c hc
    change (basis.representation l).character c = (basis.representation l).character 1
    rw [hlam, hlam, MonoidHom.mem_ker.mp hc, map_one]


theorem fourth_power_mem_normal_layer {Q : Type v} [Group Q]
    (L T : Subgroup Q) [L.Normal]
    (hodd : Odd (Nat.card (T ⧸ L.subgroupOf T)))
    (x : Q) (hxT : x ∈ T) (hx4 : x ^ 4 = 1) : x ∈ L := by
  let y : T := ⟨x, hxT⟩
  let q := QuotientGroup.mk' (L.subgroupOf T) y
  have hq4 : q ^ 4 = 1 := by
    rw [← map_pow]
    have hy4 : y ^ 4 = 1 := Subtype.ext hx4
    rw [hy4, map_one]
  have hqcard : q ^ Nat.card (T ⧸ L.subgroupOf T) = 1 := pow_card_eq_one'
  have hcop : Nat.Coprime 4 (Nat.card (T ⧸ L.subgroupOf T)) :=
    hodd.coprime_two_left.pow_left 2
  have hq1 : q = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hq4, hqcard⟩
  have hyL : y ∈ L.subgroupOf T := (QuotientGroup.eq_one_iff y).mp hq1
  exact hyL

theorem actual_order_four_image_mem_layer [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (p f : ℕ) (rho : Gamma t →* coordinateE F)
    (data : ActualMatrixData t n p f F A rho) (x : C t) (hx : orderOf x = 4) :
    nu t x ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
  obtain ⟨hNZK, _, _, _, _, _, _⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  obtain ⟨hxK, _⟩ := actual_order_four_residual_and_square n hn S0 f0 hG t ht x hx
  have hxT : nu t x ∈ (J t).comap (barKappa t) := by
    rw [barKappa_preimage_J t hNZK]
    exact Subgroup.mem_map_of_mem (nu t) hxK
  obtain ⟨_, _, _, hcard⟩ := data.compatible_layer
  have hodd : Odd (Nat.card (((J t).comap (barKappa t)) ⧸
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).subgroupOf
        ((J t).comap (barKappa t)))) := hcard ▸ data.field_group_odd
  apply fourth_power_mem_normal_layer _ _ hodd _ hxT
  rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]

theorem actual_order_four_matrix [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (p f : ℕ) (rho : Gamma t →* coordinateE F)
    (data : ActualMatrixData t n p f F A rho) (x : C t) (hx : orderOf x = 4) :
    ∃ X : Matrix.SpecialLinearGroup (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * X = -1 ∧
      localAction F rho x = coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) := by
  obtain ⟨eta, hetaz, heta, _⟩ := data.compatible_layer
  have hxL := actual_order_four_image_mem_layer n hn S0 f0 hG t ht F A p f rho data x hx
  let y : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := ⟨nu t x, hxL⟩
  have hysq : y ^ 2 = ⟨nu t (tInC t),
      QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
        (nu t (tInC t)) (barKappa t) (barKappa_kernel t)
          (CFSG.generalizedFitting (Gamma t))⟩ := by
    apply Subtype.ext
    change (nu t x) ^ 2 = nu t (tInC t)
    rw [← map_pow, (actual_order_four_residual_and_square n hn S0 f0 hG t ht x hx).2]
  have hXsq : eta y ^ 2 = -1 := by
    rw [← map_pow, hysq, hetaz]
  refine ⟨eta y, ?_, ?_⟩
  · have h := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
        (X : Matrix (Fin 2) (Fin 2) F)) hXsq
    simpa only [pow_two, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] using h
  · change (rho (kappa t x)).val = _
    rw [Principal.coordinateGLAction_toGL]
    exact heta y

theorem fixed_point_card_conjugation {X : Type v} (g d : Equiv.Perm X) :
    Nat.card {x : X // (d * g * d⁻¹) x = x} = Nat.card {x : X // g x = x} := by
  symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv d
  intro x
  constructor
  · intro hx
    change d (g (d⁻¹ (d x))) = d x
    simpa only [Equiv.Perm.coe_inv, d.symm_apply_apply] using congrArg d hx
  · intro hx
    have h : d (g x) = d x := by
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, d.symm_apply_apply] using hx
    exact d.injective h

theorem cover_J_eq_principal_J
    (F : Type) [Field F] (a : Fˣ) :
    MatrixCoverData.J F a = Principal.jMatrix (a : F) a.ne_zero := by
  apply Units.ext
  rfl

theorem actual_noncentral_involution_projective_conjugate [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (p f : ℕ) (rho : Gamma t →* coordinateE F)
    (data : ActualMatrixData t n p f F A rho)
    (hF : IsOddPrimePower (Nat.card F)) (v : C t)
    (hv : orderOf v = 2) (hvt : v ≠ tInC t) (a : Fˣ) (ha : ¬IsSquare a) :
    ∃ d : coordinateD F,
      (d : Equiv.Perm (Omega F)) * localAction F rho v *
        (d : Equiv.Perm (Omega F))⁻¹ =
          coordinateGLAction F (Principal.jMatrix (a : F) a.ne_zero) := by
  classical
  have hout : v ∉ K t := actual_noncentral_involution_not_mem_K n hn S0 f0 hG t ht v hv hvt
  obtain ⟨hNZK, _, _, _, _, _, _⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hspecialout : rho (kappa t v) ∉ OddFieldLift.SpecialGamma F A := by
    intro h
    apply hout
    have hpre : (J t).comap (kappa t) = K t := by
      rw [J, Subgroup.comap_map_eq_self
        (by simpa only [QuotientGroup.ker_mk'] using hNZK)]
    rw [← hpre]
    change kappa t v ∈ J t
    rw [← data.residual_image] at h
    exact (Subgroup.mem_map_iff_mem data.faithful).mp h
  let g : OddFieldLift.Gamma F A :=
    ⟨rho (kappa t v), data.full_image ▸ ⟨kappa t v, rfl⟩⟩
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    change rho (kappa t v) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← hv, pow_orderOf_eq_one, map_one, map_one]
  have hvD : localAction F rho v ∈ coordinateD F :=
    MatrixCover.gamma_involution_mem_linear F A data.field_group_odd g hg2
  have hvG : localAction F rho v ∉ coordinateG F := by
    intro h
    apply hspecialout
    exact (le_sup_left : specialLayer F ≤ OddFieldLift.SpecialGamma F A) h
  let dv : coordinateD F := ⟨localAction F rho v, hvD⟩
  have hdv2 : dv ^ 2 = 1 := by
    apply Subtype.ext
    change localAction F rho v ^ 2 = 1
    rw [← map_pow, ← hv, pow_orderOf_eq_one, map_one]
  have hdvne : dv ≠ 1 := by
    intro h
    apply hvG
    have hval := congrArg Subtype.val h
    rw [show localAction F rho v = 1 from hval]
    exact (coordinateG F).one_mem
  have hdvorder : orderOf dv = 2 := orderOf_eq_prime hdv2 hdvne
  obtain ⟨d, hd⟩ :=
    ProjectiveNonsquareInvolutions.projective_nonsquare_involutions_are_conjugate
      F hF a ha dv hvG hdvorder
  refine ⟨d, ?_⟩
  have h := congrArg Subtype.val hd
  change (d : Equiv.Perm (Omega F)) * localAction F rho v *
      (d : Equiv.Perm (Omega F))⁻¹ =
        coordinateGLAction F (MatrixCoverData.J F a) at h
  rwa [cover_J_eq_principal_J F a] at h

theorem actual_scalar_sign_kernel {n p f : ℕ}
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (data : ActualMatrixData t n p f F A rho)
    (hNZK : NZ t ≤ K t) (hF : IsOddPrimePower (Nat.card F))
    (lam : C t →* ℂˣ) (hlam : ∀ c, (lam c : ℂ) = localDelta F rho c) :
    lam.ker = K t := by
  ext c
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, hlam]
  exact localDelta_eq_one_iff F A rho data.faithful data.full_image
    data.residual_image hNZK hF c

theorem actual_character_values_on_NZ {n p f : ℕ}
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* coordinateE F) (data : ActualMatrixData t n p f F A rho)
    (hNZK : NZ t ≤ K t) (hF : IsOddPrimePower (Nat.card F))
    (c : C t) (hc : c ∈ NZ t) :
    localPhi F rho c = p ^ f ∧ localDelta F rho c * localPhi F rho c = p ^ f := by
  have hd := (localDelta_eq_one_iff F A rho data.faithful data.full_image
    data.residual_image hNZK hF c).mpr (hNZK hc)
  have hp := localPhi_on_NZ F rho c hc
  rw [data.field_card, Nat.cast_pow] at hp
  exact ⟨hp, by rw [hd, one_mul, hp]⟩


structure ActualCharacterData [Fintype (C t)]
    (F : Type) [Field F] (rho : Gamma t →* coordinateE F) (q : ℕ)
    (basis : FiniteIrreducibleCharacterBasis (C t))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) : Prop where
  characters : ∃ ldelta lphi ldeltaPhi : basis.index,
    (∀ c, (basis.representation ldelta).character c = localDelta F rho c) ∧
    (∀ c, (basis.representation lphi).character c = localPhi F rho c) ∧
    (∀ c, (basis.representation ldeltaPhi).character c =
      localDelta F rho c * localPhi F rho c) ∧
    [principal, ldelta, lphi, ldeltaPhi].Nodup ∧
    (∀ l ∈ [principal, ldelta, lphi, ldeltaPhi],
      (basis.representation l).IsIrreducible ∧
      l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      ∀ c, ∃ z : ℤ, (basis.representation l).character c = z) ∧
    Module.finrank ℂ (basis.representation principal).vector = 1 ∧
    Module.finrank ℂ (basis.representation ldelta).vector = 1 ∧
    Module.finrank ℂ (basis.representation lphi).vector = q ∧
    Module.finrank ℂ (basis.representation ldeltaPhi).vector = q ∧
    MonoidHom.ker (basis.representation ldelta).representation = K t ∧
    MonoidHom.ker (basis.representation lphi).representation = NZ t ∧
    MonoidHom.ker (basis.representation ldeltaPhi).representation = NZ t
  kernel_values : ∀ c : C t, c ∈ NZ t →
    localPhi F rho c = q ∧ localDelta F rho c * localPhi F rho c = q
  order_four_values : ∀ u : C t, orderOf u = 4 →
    localPhi F rho u = localEpsilon F ∧
      localDelta F rho u * localPhi F rho u = localEpsilon F
  noncentral_involution_values : ∀ v : C t, orderOf v = 2 → v ≠ tInC t →
    localDelta F rho v = -1 ∧ localPhi F rho v = -localEpsilon F ∧
      localDelta F rho v * localPhi F rho v = localEpsilon F

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem actual_simple_layer_character_data [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    (F : Type) [Field F] [Fintype F] (A : Subgroup (F ≃+* F))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (rho : Gamma t →* coordinateE F) (data : ActualMatrixData t n p f F A rho)
    [Fintype (C t)] (basis : FiniteIrreducibleCharacterBasis (C t))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    ActualCharacterData F rho (p ^ f) basis ideal principal := by
  classical
  obtain ⟨hNZK, _, _, _, _, _, _⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hF : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, data.field_card⟩
  obtain ⟨⟨lam, hlam⟩, ⟨ld, lp, ldp, hd, hphi, hdp, hnodup, hP,
      hdeg1, hdegd, hdegp, hdegdp, hkerp, hkerdp⟩,
      _, _, hX, hJ⟩ :=
    actual_four_character_input F A rho data.faithful data.full_image
      p f hp hpodd hf data.field_card basis ideal principal hprincipal
  have hkerd : MonoidHom.ker (basis.representation ld).representation = K t :=
    (degree_one_character_kernel basis ld hdegd lam (fun c => (hd c).trans (hlam c).symm)).trans
      (actual_scalar_sign_kernel F A rho data hNZK hF lam hlam)
  refine
    { characters := ⟨ld, lp, ldp, hd, hphi, hdp, hnodup, hP,
        hdeg1, hdegd, hdegp, hdegdp, hkerd, hkerp, hkerdp⟩
      kernel_values := ?_
      order_four_values := ?_
      noncentral_involution_values := ?_ }
  · intro c hc
    simpa only [Nat.cast_pow] using actual_character_values_on_NZ F A rho data hNZK hF c hc
  · intro u hu
    obtain ⟨X, hXsq, hXact⟩ := actual_order_four_matrix n hn S0 f0 hG t ht
      F A p f rho data u hu
    exact hX u X hXsq hXact
  · intro v hv hvt
    have hout := actual_noncentral_involution_not_mem_K n hn S0 f0 hG t ht v hv hvt
    have hdv : localDelta F rho v = -1 :=
      localDelta_eq_neg_one_of_not_mem F rho v (fun h =>
        hout ((localDelta_eq_one_iff F A rho data.faithful data.full_image
          data.residual_image hNZK hF v).mp h))
    have hqodd : Odd (Nat.card F) := data.field_card ▸ hpodd.pow
    have hF2 : ringChar F ≠ 2 := by
      intro h
      have hcardEven := FiniteField.even_card_iff_char_two.mp h
      rw [← Nat.card_eq_fintype_card] at hcardEven
      obtain ⟨k, hk⟩ := hqodd
      omega
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF2
    have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
    let au : Fˣ := Units.mk0 a ha0
    have hau : ¬ IsSquare au := by
      intro h
      obtain ⟨b, hb⟩ := h
      exact ha ⟨(b : F), congrArg (fun x : Fˣ => (x : F)) hb⟩
    obtain ⟨d, hd⟩ := actual_noncentral_involution_projective_conjugate
      n hn S0 f0 hG t ht F A p f rho data hF v hv hvt au hau
    have hfix : Nat.card {x : Omega F // localAction F rho v x = x} =
        Nat.card {x : Omega F // coordinateGLAction F (Principal.jMatrix a ha0) x = x} := by
      rw [← fixed_point_card_conjugation (localAction F rho v) (d : Equiv.Perm (Omega F))]
      rw [hd]
      rfl
    have hjD : coordinateGLAction F (Principal.jMatrix a ha0) ∈ coordinateD F := by
      rw [← coordinateGLAction_range]
      exact ⟨Principal.jMatrix a ha0, rfl⟩
    obtain ⟨w, hw⟩ := permutationCover_surjective F A rho data.full_image
      ⟨coordinateGLAction F (Principal.jMatrix a ha0), permutationGamma_contains_D F A hjD⟩
    have hwact : localAction F rho w = coordinateGLAction F (Principal.jMatrix a ha0) :=
      (permutationCover_value F A rho data.full_image w).symm.trans (congrArg Subtype.val hw)
    have hphiw : localPhi F rho w = -localEpsilon F := (hJ w a ha0 ha hwact).2.1
    have hphiv : localPhi F rho v = -localEpsilon F := by
      calc
        localPhi F rho v = localPhi F rho w := by
          rw [localPhi, localPhi, hfix, hwact]
        _ = -localEpsilon F := hphiw
    exact ⟨hdv, hphiv, by rw [hdv, hphiv]; ring⟩

open scoped Classical in
theorem actual_simple_layer_involution_centralizer_local_package
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F))
      (rho : Gamma t →* coordinateE F),
      ActualMatrixData t n p f F A rho ∧
      ∀ (basis : FiniteIrreducibleCharacterBasis (C t))
        (ideal : Ideal ComplexAlgebraicIntegers) (_ : ideal.IsMaximal)
        (_ : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2)
        (principal : basis.index),
        (basis.representation principal).character = 1 →
        ActualCharacterData F rho (p ^ f) basis ideal principal := by
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S0 f0 hG t ht hnonab hcentral hnc
      p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  refine ⟨F, hfield, hfinite, A, rho, data, ?_⟩
  intro basis ideal hmax hchar principal hprincipal
  let : Fintype F := Fintype.ofFinite F
  exact actual_simple_layer_character_data n hn S0 f0 hG t ht F A p f hp hpodd hf
    rho data basis ideal principal hprincipal

end

end CFSG.Semidihedral.ActualSimpleLayerLocalPackage
