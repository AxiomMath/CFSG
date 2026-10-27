module

public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2LayerModel
public import CFSG.CharacterTheory.Semidihedral.SemilinearOddExtensions
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.Semidihedral.ActualLayerOddExtensions

noncomputable section

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions

universe u v w

instance actualLayer_normal (Γ : Type v) [Group Γ] :
    (CFSG.generalizedFitting Γ).Normal :=
  SemilinearLayerModel.generalizedFitting_normal Γ

@[expose] def quotientPreimageEquiv
    {H : Type u} {Γ : Type v} [Group H] [Group Γ]
    (pi : H →* Γ) (hpi : Function.Surjective pi)
    (N : Subgroup Γ) [N.Normal] : H ⧸ N.comap pi ≃* Γ ⧸ N := by
  let q := (QuotientGroup.mk' N).comp pi
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective N).comp hpi
  have hker : q.ker = N.comap pi := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact QuotientGroup.liftEquiv (N.comap pi) hq hker.symm

theorem quotientPreimageEquiv_mk
    {H : Type u} {Γ : Type v} [Group H] [Group Γ]
    (pi : H →* Γ) (hpi : Function.Surjective pi)
    (N : Subgroup Γ) [N.Normal] (x : H) :
    quotientPreimageEquiv pi hpi N (QuotientGroup.mk x) =
      QuotientGroup.mk (pi x) := rfl

theorem faithful_layer_index
    {Γ : Type v} [Group Γ] (F : Type w) [Field F] [Finite F]
    (L : Subgroup Γ) (rho : Γ →* coordinateE F) (hrho : Function.Injective rho)
    (hmap : L.map rho = specialLayer F) :
    (specialLayer F).relIndex rho.range = L.index := by
  rw [← hmap, ← Subgroup.map_top rho,
    Subgroup.relIndex_map_map_of_injective L ⊤ hrho, Subgroup.relIndex_top_right]

theorem index_two_subgroup_special_extension
    (F : Type w) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (Gamma K : Subgroup (coordinateE F))
    (hG : specialLayer F ≤ K) (hKG : K ≤ Gamma)
    (A : Subgroup (F ≃+* F)) (hA : Odd (Nat.card A))
    (hlinear : LinearExtension F Gamma A) (hindex : K.relIndex Gamma = 2) :
    SpecialExtension F K A := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have hfield : fieldImage F Gamma = A := linearExtension_fieldImage F Gamma A hlinear
  have hle : fieldImage F K ≤ A := by
    rw [← hfield]
    exact Subgroup.map_mono hKG
  have hodd : Odd (Nat.card (fieldImage F K)) :=
    hA.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hmul := Subgroup.relIndex_mul_relIndex (specialLayer F) K Gamma hG hKG
  rw [hindex, linearExtension_index F Gamma A hlinear] at hmul
  have hspecialindex : (specialLayer F).relIndex K = Nat.card A := by omega
  have hspecial : SpecialExtension F K (fieldImage F K) :=
    (gamma_index_odd_iff_specialExtension F hF K hG hodd).mp (hspecialindex ▸ hA)
  have hcard : Nat.card (fieldImage F K) = Nat.card A :=
    (specialExtension_index F K _ hspecial).symm.trans hspecialindex
  have heq : fieldImage F K = A :=
    Subgroup.eq_of_le_of_card_ge hle hcard.symm.le
  simpa only [heq] using hspecial

@[expose] def quotientFaithfulImageEquiv
    {Γ : Type v} [Group Γ] (F : Type w) [Field F] [Finite F]
    (L : Subgroup Γ) [L.Normal]
    (rho : Γ →* coordinateE F) (hrho : Function.Injective rho)
    (hmap : L.map rho = specialLayer F) : Γ ⧸ L ≃* GammaQuotient F rho.range := by
  let q := (QuotientGroup.mk' ((specialLayer F).subgroupOf rho.range)).comp rho.rangeRestrict
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp rho.rangeRestrict_surjective
  have hker : q.ker = L := by
    ext x
    change QuotientGroup.mk (rho.rangeRestrict x) = 1 ↔ x ∈ L
    rw [QuotientGroup.eq_one_iff]
    change rho x ∈ specialLayer F ↔ x ∈ L
    rw [← hmap]
    exact Subgroup.mem_map_iff_mem hrho
  exact QuotientGroup.liftEquiv L hq hker.symm

theorem quotientFaithfulImageEquiv_mk
    {Γ : Type v} [Group Γ] (F : Type w) [Field F] [Finite F]
    (L : Subgroup Γ) [L.Normal]
    (rho : Γ →* coordinateE F) (hrho : Function.Injective rho)
    (hmap : L.map rho = specialLayer F) (x : Γ) :
    quotientFaithfulImageEquiv F L rho hrho hmap (QuotientGroup.mk x) =
      QuotientGroup.mk (rho.rangeRestrict x) := rfl

@[expose] def restrictedQuotientImageEquiv
    {H : Type u} {Γ : Type v} [Group H] [Group Γ]
    (pi : H →* Γ) (hpi : Function.Surjective pi)
    (F : Type w) [Field F] [Finite F]
    (L : Subgroup Γ) [L.Normal] (J : Subgroup Γ)
    (rho : Γ →* coordinateE F) (hrho : Function.Injective rho)
    (hmap : L.map rho = specialLayer F) :
    (J.comap pi) ⧸ (L.comap pi).subgroupOf (J.comap pi) ≃*
      GammaQuotient F (J.map rho) := by
  let qJ := QuaternionDoubleCoverUniqueness.preimageProjection pi J
  let qK := (rho.subgroupMap J).comp qJ
  let q := (QuotientGroup.mk' ((specialLayer F).subgroupOf (J.map rho))).comp qK
  have hqK : Function.Surjective qK := (rho.subgroupMap_surjective J).comp
    (QuaternionDoubleCoverUniqueness.preimageProjection_surjective pi hpi J)
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hqK
  have hker : q.ker = (L.comap pi).subgroupOf (J.comap pi) := by
    ext x
    change QuotientGroup.mk (qK x) = 1 ↔ pi (x : H) ∈ L
    rw [QuotientGroup.eq_one_iff]
    change rho (pi (x : H)) ∈ specialLayer F ↔ pi (x : H) ∈ L
    rw [← hmap]
    exact Subgroup.mem_map_iff_mem hrho
  exact QuotientGroup.liftEquiv ((L.comap pi).subgroupOf (J.comap pi)) hq hker.symm

theorem actual_linear_two_local_layer_odd_field_extension
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
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        ∃ (A : Subgroup (F ≃+* F))
          (rho : Γ →* coordinateE F)
          (eta : (CFSG.generalizedFitting Γ).comap pi ≃*
            Matrix.SpecialLinearGroup (Fin 2) F),
          Odd (Nat.card A) ∧ Nat.card A ∣ f ∧ Function.Injective rho ∧
          (CFSG.generalizedFitting Γ).map rho = specialLayer F ∧
          rho.range = linearLayer F ⊔ liftedField F A ∧
          J.map rho = specialLayer F ⊔ liftedField F A ∧
          LinearExtension F rho.range A ∧ SpecialExtension F (J.map rho) A ∧
          eta ⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
            z pi hker (CFSG.generalizedFitting Γ)⟩ = -1 ∧
          (∀ x : (CFSG.generalizedFitting Γ).comap pi,
            (rho (pi x)).val =
              coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x))) ∧
          IsCyclic (H ⧸ (CFSG.generalizedFitting Γ).comap pi) ∧
          Nat.card (H ⧸ (CFSG.generalizedFitting Γ).comap pi) = 2 * Nat.card A ∧
          IsCyclic ((J.comap pi) ⧸
            ((CFSG.generalizedFitting Γ).comap pi).subgroupOf (J.comap pi)) ∧
          Nat.card ((J.comap pi) ⧸
            ((CFSG.generalizedFitting Γ).comap pi).subgroupOf (J.comap pi)) = Nat.card A ∧
          Nat.card ((CFSG.generalizedFitting Γ).comap pi) =
            Nat.card F * (Nat.card F ^ 2 - 1) ∧
          (Nat.card F ^ 2 - 1).factorization 2 = k ∧
          2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 ^ k ∧
          Nat.card (FixedPoints.subfield A F) = p ^ (f / Nat.card A) ∧
          Nat.card F = (p ^ (f / Nat.card A)) ^ Nat.card A ∧
          Nat.card F % 8 = p ^ (f / Nat.card A) % 8 ∧
          ((p ^ (f / Nat.card A)) ^ 2 - 1).factorization 2 = k ∧
          2 ^ ((p ^ (f / Nat.card A)) ^ 2 - 1).factorization 2 = 2 ^ k := by
  let L := CFSG.generalizedFitting Γ
  obtain ⟨hk3, hchar, hcenter, hcent, _, hindex, _,
      F, hfield, hfinite, hcard, rho, eta, hrho, hmap, hetaz,
      hprojective, hcardL, htwoL, hpowL⟩ :=
    CharacteristicSL2Layer.projective_layer_characteristic_SL2
      z hz hc pi hpi hker k hk S eS hnonab hcentral hnc J hJindex hLJ
      hunique hparameters hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  have hpodd : Odd p := hparameters.1.odd_of_ne_two hparameters.2.1
  let hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hparameters.1, hpodd, hparameters.2.2, hcard⟩
  have hG : specialLayer F ≤ rho.range := by
    change (coordinateG F).subgroupOf (coordinateE F) ≤ rho.range
    rw [← hmap]
    exact Subgroup.map_le_range rho L
  let S' : Sylow 2 rho.range := S.mapSurjective rho.rangeRestrict_surjective
  have hinj : Function.Injective rho.rangeRestrict :=
    MonoidHom.rangeRestrict_injective_iff.mpr hrho
  let eS' : S' ≃* DihedralGroup (2 ^ (k - 1)) :=
    ((S : Subgroup Γ).equivMapOfInjective rho.rangeRestrict hinj).symm.trans eS
  obtain ⟨_, hAodd, hAdvd, _, heven, _⟩ :=
    dihedral_projective_semilinear_overgroups_have_odd_field_part
      F hparameters.1 hpodd hparameters.2.2 hcard rho.range hG S' hk eS'
  let A := fieldImage F rho.range
  have hLindex : L.index.factorization 2 = 1 := by
    rw [← CharacteristicSL2Layer.preimage_index pi hpi L]
    exact hindex
  have hLeven : Even L.index := even_iff_two_dvd.mpr
    ((Nat.prime_two.dvd_iff_one_le_factorization
      (Subgroup.index_ne_zero_of_finite : L.index ≠ 0)).mpr (by rw [hLindex]))
  have hevenImage : Even ((specialLayer F).relIndex rho.range) := by
    rw [faithful_layer_index F L rho hrho hmap]
    exact hLeven
  have hlinear : LinearExtension F rho.range A := heven.mp hevenImage
  have hGJ : specialLayer F ≤ J.map rho := by
    change (coordinateG F).subgroupOf (coordinateE F) ≤ J.map rho
    rw [← hmap]
    exact Subgroup.map_mono hLJ
  have hJG : J.map rho ≤ rho.range := Subgroup.map_le_range rho J
  have hJtwo : (J.map rho).relIndex rho.range = 2 := by
    rw [← Subgroup.map_top rho,
      Subgroup.relIndex_map_map_of_injective J ⊤ hrho, Subgroup.relIndex_top_right,
      hJindex]
  have hspecial : SpecialExtension F (J.map rho) A :=
    index_two_subgroup_special_extension F hF rho.range (J.map rho)
      hGJ hJG A hAodd hlinear hJtwo
  obtain ⟨_, _, hGamma, _, _, _, _, hGammaCard, _, hGammaCyclic⟩ := hlinear.1
  obtain ⟨_, _, hJ, _, _, _, _, hJCard, _, hJCyclic⟩ := hspecial.1
  let eH := (quotientPreimageEquiv pi hpi L).trans
    (quotientFaithfulImageEquiv F L rho hrho hmap)
  have hHcyclic : IsCyclic (H ⧸ L.comap pi) := eH.isCyclic.mpr hGammaCyclic
  have hHcard : Nat.card (H ⧸ L.comap pi) = 2 * Nat.card A :=
    (Nat.card_congr eH.toEquiv).trans hGammaCard
  let eT := restrictedQuotientImageEquiv pi hpi F L J rho hrho hmap
  have hTcyclic : IsCyclic ((J.comap pi) ⧸
      (L.comap pi).subgroupOf (J.comap pi)) := eT.isCyclic.mpr hJCyclic
  have hTcard : Nat.card ((J.comap pi) ⧸
      (L.comap pi).subgroupOf (J.comap pi)) = Nat.card A := by
    simpa only [one_mul] using (Nat.card_congr eT.toEquiv).trans hJCard
  obtain ⟨_, _, _, _, _, hfixed, hpower, hmod, hfactor, hpowerTwo⟩ :=
    FixedFieldData.odd_fixed_field_data p f hparameters.1 hpodd hparameters.2.2 F hcard A hAodd
  refine ⟨hk3, hchar, hcenter, hcent, F, hfield, hfinite, hcard,
    A, rho, eta, hAodd, hAdvd, hrho, hmap, hGamma, hJ, hlinear, hspecial,
    hetaz, hprojective, hHcyclic, hHcard, hTcyclic, hTcard, hcardL, htwoL, hpowL,
    hfixed, hpower, hmod, hfactor.symm.trans htwoL, hpowerTwo.symm.trans hpowL⟩

theorem actual_linear_two_local_layer_odd_field_extension_int
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
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        ∃ (A : Subgroup (F ≃+* F))
          (rho : Γ →* coordinateE F)
          (eta : (CFSG.generalizedFitting Γ).comap pi ≃*
            Matrix.SpecialLinearGroup (Fin 2) F),
          Odd (Nat.card A) ∧ Nat.card A ∣ f ∧ Function.Injective rho ∧
          (CFSG.generalizedFitting Γ).map rho = specialLayer F ∧
          rho.range = linearLayer F ⊔ liftedField F A ∧
          J.map rho = specialLayer F ⊔ liftedField F A ∧
          LinearExtension F rho.range A ∧ SpecialExtension F (J.map rho) A ∧
          eta ⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
            z pi hker (CFSG.generalizedFitting Γ)⟩ = -1 ∧
          (∀ x : (CFSG.generalizedFitting Γ).comap pi,
            (rho (pi x)).val =
              coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x))) ∧
          IsCyclic (H ⧸ (CFSG.generalizedFitting Γ).comap pi) ∧
          Nat.card (H ⧸ (CFSG.generalizedFitting Γ).comap pi) = 2 * Nat.card A ∧
          IsCyclic ((J.comap pi) ⧸
            ((CFSG.generalizedFitting Γ).comap pi).subgroupOf (J.comap pi)) ∧
          Nat.card ((J.comap pi) ⧸
            ((CFSG.generalizedFitting Γ).comap pi).subgroupOf (J.comap pi)) = Nat.card A ∧
          Nat.card ((CFSG.generalizedFitting Γ).comap pi) =
            Nat.card F * (Nat.card F ^ 2 - 1) ∧
          ((Nat.card F ^ 2 - 1).factorization 2 : ℤ) = k ∧
          2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 ^ k.toNat ∧
          Nat.card (FixedPoints.subfield A F) = p ^ (f / Nat.card A) ∧
          Nat.card F = (p ^ (f / Nat.card A)) ^ Nat.card A ∧
          Nat.card F % 8 = p ^ (f / Nat.card A) % 8 ∧
          (((p ^ (f / Nat.card A)) ^ 2 - 1).factorization 2 : ℤ) = k ∧
          2 ^ ((p ^ (f / Nat.card A)) ^ 2 - 1).factorization 2 = 2 ^ k.toNat := by
  have hexp : (k - 1).toNat = k.toNat - 1 := by omega
  obtain ⟨hk3, hchar, hcenter, hcent, F, hfield, hfinite, hcard,
      A, rho, eta, hAodd, hAdvd, hrho, hmap, hGamma, hJ, hlinear, hspecial,
      hetaz, hprojective, hHcyclic, hHcard, hTcyclic, hTcard, hcardL, htwoL, hpowL,
      hfixed, hpower, hmod, htwoFixed, hpowFixed⟩ :=
    actual_linear_two_local_layer_odd_field_extension
      z hz hc pi hpi hker k.toNat (by omega)
      S (by rw [← hexp]; exact eS) hnonab hcentral hnc J hJindex hLJ
      hunique hparameters hmodel
  refine ⟨by omega, hchar, hcenter, hcent, F, hfield, hfinite, hcard,
    A, rho, eta, hAodd, hAdvd, hrho, hmap, hGamma, hJ, hlinear, hspecial,
    hetaz, hprojective, hHcyclic, hHcard, hTcyclic, hTcard, hcardL, ?_, hpowL,
    hfixed, hpower, hmod, ?_, hpowFixed⟩
  · rw [htwoL, Int.toNat_of_nonneg (by omega)]
  · rw [htwoFixed, Int.toNat_of_nonneg (by omega)]

end

end CFSG.Semidihedral.ActualLayerOddExtensions
