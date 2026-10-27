module

public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2LayerSylow
public import CFSG.CharacterTheory.Semidihedral.SemilinearLayerModel
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2Layer

public section

namespace CFSG.Semidihedral.CharacteristicSL2Layer

noncomputable section

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u v

theorem pslEquivCoordinateG_value (F : Type v) [Field F] (x : PSL2 F) :
    (pslEquivCoordinateG F x).val = coordinatePSLAction F x := by
  rfl

theorem projective_layer_characteristic_SL2
    {H : Type u} [Group H] [Finite H]
    {Γ : Type} [Group Γ] [Finite Γ]
    [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (z : H) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center H)
    (pi : H →* Γ) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (k : ℕ) (hk : 2 ≤ k)
    (S : Sylow 2 Γ) (eS : S ≃* DihedralGroup (2 ^ (k - 1)))
    (hnonab : ∃ a b : CFSG.generalizedFitting Γ, a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting Γ), ¬ IsCyclic U)
    (J : Subgroup Γ) (hJindex : J.index = 2)
    (hLJ : CFSG.generalizedFitting Γ ≤ J)
    (hunique : ∀ x : J.comap pi, orderOf x = 2 → (x : H) = z)
    {p f : ℕ} (hparameters : p.Prime ∧ p ≠ 2 ∧ 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting Γ) .PSL 2 p f) :
    3 ≤ k ∧
      ((CFSG.generalizedFitting Γ).comap pi).Characteristic ∧
      Subgroup.center H = Subgroup.zpowers z ∧
      Subgroup.centralizer ((CFSG.generalizedFitting Γ).comap pi : Set H) =
        Subgroup.zpowers z ∧
      Odd (((CFSG.generalizedFitting Γ).comap pi).relIndex (J.comap pi)) ∧
      ((CFSG.generalizedFitting Γ).comap pi).index.factorization 2 = 1 ∧
      2 ^ ((CFSG.generalizedFitting Γ).comap pi).index.factorization 2 = 2 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        ∃ (rho : Γ →* coordinateE F)
          (eta : (CFSG.generalizedFitting Γ).comap pi ≃*
            Matrix.SpecialLinearGroup (Fin 2) F),
          Function.Injective rho ∧
          (CFSG.generalizedFitting Γ).map rho =
            (coordinateG F).subgroupOf (coordinateE F) ∧
          eta ⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
            z pi hker (CFSG.generalizedFitting Γ)⟩ = -1 ∧
          (∀ x : (CFSG.generalizedFitting Γ).comap pi,
            (rho (pi x)).val =
              coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x))) ∧
          Nat.card ((CFSG.generalizedFitting Γ).comap pi) =
            Nat.card F * (Nat.card F ^ 2 - 1) ∧
          (Nat.card F ^ 2 - 1).factorization 2 = k ∧
          2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 ^ k := by
  let L := CFSG.generalizedFitting Γ
  have hLchar : L.Characteristic := SemilinearLayerModel.generalizedFitting_characteristic Γ
  have hLnormal : L.Normal := SemilinearLayerModel.generalizedFitting_normal Γ
  obtain ⟨hchar, hcenter, hcent⟩ :=
    characteristic_layer_preimage z hc pi hpi hker L hLchar hcentral
  let U : Sylow 2 L := Sylow.nonempty.some
  obtain ⟨hk3, hoddindex, hindex, hindexpow⟩ :=
    central_cover_dihedral_index pi hpi k hk S eS L hLnormal J hJindex hLJ U (hnc U)
  have hLtwo :=
    original_layer_two_part z hz pi hpi hker k hk S eS L hLnormal J hJindex hLJ U (hnc U)
  obtain ⟨F, hfield, hfinite, hcard, theta, rho, hrho, hextends, hmap, _, _⟩ :=
    SemilinearLayerModel.generalizedFitting_semilinear_model hnonab hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  have hodd : Odd (Nat.card F) := hcard ▸ (hparameters.1.odd_of_ne_two hparameters.2.1).pow
  have htwo : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hF : ringChar F ≠ 2 := by
    intro heq
    apply htwo
    have hcast : (ringChar F : F) = 0 := ringChar.Nat.cast_ringChar
    simpa only [heq, Nat.cast_ofNat] using hcast
  let zL : L.comap pi :=
    ⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage z pi hker L⟩
  have hzL : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hz
  have hcL : zL ∈ Subgroup.center (L.comap pi) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (Subgroup.mem_center_iff.mp hc x)
  let q := QuaternionDoubleCoverUniqueness.preimageProjection pi L
  let thetaP : L ≃* PSL2 F := theta.trans (pslEquivCoordinateG F).symm
  let psi : L.comap pi →* PSL2 F := thetaP.toMonoidHom.comp q
  have hpsi : Function.Surjective psi := thetaP.surjective.comp
    (QuaternionDoubleCoverUniqueness.preimageProjection_surjective pi hpi L)
  have hpsiker : psi.ker = Subgroup.zpowers zL :=
    (MonoidHom.ker_mulEquiv_comp q thetaP).trans
      (preimageProjection_kernel_zpowers z pi hker L)
  let V : Sylow 2 (L.comap pi) := Sylow.nonempty.some
  obtain ⟨n, hn, ⟨eV⟩⟩ :=
    original_preimage_sylow_quaternion z hz pi hpi hker L J hLJ hunique hnc V
  obtain ⟨eta, heta, hetaz⟩ :=
    ProjectiveSL2Cover.quaternion_central_double_cover_native F hF zL hzL hcL
      psi hpsi hpsiker V n hn eV
  have hprojective : ∀ x : L.comap pi,
      (rho (pi x)).val =
        coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x)) := by
    intro x
    have hquot := DFunLike.congr_fun heta x
    change ProjectiveSL2Cover.nativeQuotient F (eta x) = thetaP (q x) at hquot
    calc
      (rho (pi x)).val = (theta (q x)).val := hextends (q x)
      _ = (pslEquivCoordinateG F (ProjectiveSL2Cover.nativeQuotient F (eta x))).val := by
        rw [hquot]
        simp only [thetaP, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      _ = coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x)) :=
        pslEquivCoordinateG_value F _
  obtain ⟨hcardL, htwoL, hpowL⟩ :=
    original_layer_field_card_and_two_part hodd (L.comap pi) eta k hLtwo
  refine ⟨hk3, hchar, hcenter, hcent, hoddindex, hindex, hindexpow,
    F, hfield, hfinite, hcard, rho, eta, hrho, hmap, ?_, hprojective, hcardL, htwoL, hpowL⟩
  exact hetaz.trans (ProjectiveSL2Cover.minusIdentity_eq_neg_one F)

theorem projective_layer_characteristic_SL2_int
    {H : Type u} [Group H] [Finite H]
    {Γ : Type} [Group Γ] [Finite Γ]
    [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (z : H) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center H)
    (pi : H →* Γ) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (k : ℤ) (hk : 2 ≤ k)
    (S : Sylow 2 Γ) (eS : S ≃* DihedralGroup (2 ^ (k - 1).toNat))
    (hnonab : ∃ a b : CFSG.generalizedFitting Γ, a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting Γ), ¬ IsCyclic U)
    (J : Subgroup Γ) (hJindex : J.index = 2)
    (hLJ : CFSG.generalizedFitting Γ ≤ J)
    (hunique : ∀ x : J.comap pi, orderOf x = 2 → (x : H) = z)
    {p f : ℕ} (hparameters : p.Prime ∧ p ≠ 2 ∧ 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting Γ) .PSL 2 p f) :
    3 ≤ k ∧
      ((CFSG.generalizedFitting Γ).comap pi).Characteristic ∧
      Subgroup.center H = Subgroup.zpowers z ∧
      Subgroup.centralizer ((CFSG.generalizedFitting Γ).comap pi : Set H) =
        Subgroup.zpowers z ∧
      Odd (((CFSG.generalizedFitting Γ).comap pi).relIndex (J.comap pi)) ∧
      ((CFSG.generalizedFitting Γ).comap pi).index.factorization 2 = 1 ∧
      2 ^ ((CFSG.generalizedFitting Γ).comap pi).index.factorization 2 = 2 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        ∃ (rho : Γ →* coordinateE F)
          (eta : (CFSG.generalizedFitting Γ).comap pi ≃*
            Matrix.SpecialLinearGroup (Fin 2) F),
          Function.Injective rho ∧
          (CFSG.generalizedFitting Γ).map rho =
            (coordinateG F).subgroupOf (coordinateE F) ∧
          eta ⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
            z pi hker (CFSG.generalizedFitting Γ)⟩ = -1 ∧
          (∀ x : (CFSG.generalizedFitting Γ).comap pi,
            (rho (pi x)).val =
              coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x))) ∧
          Nat.card ((CFSG.generalizedFitting Γ).comap pi) =
            Nat.card F * (Nat.card F ^ 2 - 1) ∧
          ((Nat.card F ^ 2 - 1).factorization 2 : ℤ) = k ∧
          2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 ^ k.toNat := by
  have hexp : (k - 1).toNat = k.toNat - 1 := by omega
  obtain ⟨hk3, hchar, hcenter, hcent, hoddindex, hindex, hindexpow,
      F, hfield, hfinite, hcard, rho, eta, hrho, hmap, hetaz,
      hprojective, hcardL, htwoL, hpowL⟩ :=
    projective_layer_characteristic_SL2 z hz hc pi hpi hker k.toNat (by omega)
      S (by rw [← hexp]; exact eS) hnonab hcentral hnc J hJindex hLJ
      hunique hparameters hmodel
  refine ⟨by omega, hchar, hcenter, hcent, hoddindex, hindex, hindexpow,
    F, hfield, hfinite, hcard, rho, eta, hrho, hmap, hetaz, hprojective, hcardL, ?_, hpowL⟩
  rw [htwoL, Int.toNat_of_nonneg (by omega)]

end

end CFSG.Semidihedral.CharacteristicSL2Layer
