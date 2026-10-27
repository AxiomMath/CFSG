module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.GH74.Generic.S45.LSporM12Data
public import CFSG.GH74.Generic.S45.LSporJ2
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.Walter.J1Props.Facts
public import CFSG.Walter.Models
public import CFSG.RankThree.PartTwo.Census.Sporadic.J3
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.Sporadic.SmallOddCore.HeLocal

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint

theorem not_ind_of_not_three {B : Type*} [Group B] [Finite B] (h : ¬ 3 ∣ Nat.card B) :
    ¬ IndLieOrder (Nat.card (B ⧸ center B)) := fun hi =>
  h (hi.three_dvd.trans (Subgroup.card_quotient_dvd_card _))

theorem not_ind_of_dvd {B : Type*} [Group B] [Finite B] {a r : ℕ} (hr : r = 3 ∨ r = 15)
    (h : Nat.card B ∣ 2 ^ a * r) : ¬ IndLieOrder (Nat.card (B ⧸ center B)) := by
  intro hi
  obtain ⟨p, hp, hp2, hsq⟩ := hi.exists_sq_dvd Nat.card_pos.ne'
  have h1 : p ^ 2 ∣ 2 ^ a * r := hsq.trans ((Subgroup.card_quotient_dvd_card _).trans h)
  have hcop : Nat.Coprime (p ^ 2) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h2 : p ^ 2 ∣ r := hcop.dvd_of_dvd_mul_left h1
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hle : p ^ 2 ≤ 15 := (Nat.le_of_dvd (by omega) h2).trans (by omega)
  have hp4 : p < 4 := by
    by_contra hc
    have : 16 ≤ p ^ 2 := by nlinarith
    omega
  obtain rfl : p = 3 := by omega
  rcases hr with rfl | rfl <;> norm_num at h2

theorem selfCent_not_mem_of_simple {S : Type*} [Group S] {t : S} (ht : orderOf t = 2)
    {B : Subgroup ↥(centralizer ({t} : Set S))} (hs : IsSimpleGroup ↥B)
    (hna : ∃ a b : ↥B, a * b ≠ b * a) : selfCent t ∉ B := by
  intro htB
  have hZ : center ↥B = ⊥ := CatLeaf.center_eq_bot_of_simple hna
  have hc : (⟨selfCent t, htB⟩ : ↥B) ∈ center ↥B := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 (g : ↥(centralizer ({t} : Set S))).2
  rw [hZ, mem_bot] at hc
  have h1 : t = 1 := congrArg (fun x : ↥B => ((x : ↥(centralizer ({t} : Set S))) : S)) hc
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem isComponentOf_map {S : Type*} [Group S] {t : S}
    {B : Subgroup ↥(centralizer ({t} : Set S))} (hB : IsComponent B) :
    Assembly.IsComponentOf (B.map (centralizer ({t} : Set S)).subtype)
      (centralizer ({t} : Set S)) := by
  rw [LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    (map_subtype_le B)]
  have h : (B.map (centralizer ({t} : Set S)).subtype).subgroupOf (centralizer ({t} : Set S)) =
      B := Subgroup.comap_map_eq_self_of_injective (centralizer ({t} : Set S)).subtype_injective B
  rw [h]
  exact hB

theorem card_quotient_center_map {S : Type*} [Group S] {t : S}
    (B : Subgroup ↥(centralizer ({t} : Set S))) :
    Nat.card (↥(B.map (centralizer ({t} : Set S)).subtype) ⧸
      center ↥(B.map (centralizer ({t} : Set S)).subtype)) = Nat.card (↥B ⧸ center ↥B) :=
  (Nat.card_congr (QuotientGroup.congr _ _
    (B.equivMapOfInjective _ (centralizer ({t} : Set S)).subtype_injective)
    (Subgroup.map_center_eq _)).toEquiv).symm

theorem sporT1Data_M12
    : SporT1Data .M12 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_M12
  comps := fun S _ _ _ _ e t ht B _ _ => by
    let e' : S ≃* NativeSporadic.M12 := e
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv e' t).toEquiv] at hd
    rcases GH74.Generic.S45.LAlt.m12_involution_data (e' t)
        (by rw [MulEquiv.orderOf_eq]; exact ht) with h | ⟨h, -⟩ <;> rw [h] at hd
    · exact not_ind_of_dvd (a := 6) (r := 3) (Or.inl rfl) (hd.trans (by norm_num))
    · exact not_ind_of_dvd (a := 4) (r := 15) (Or.inr rfl) (hd.trans (by norm_num))

theorem sporT1Data_M22
    : SporT1Data .M22 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_M22
  comps := fun _ _ _ _ _ e t ht B hB _ =>
    not_ind_of_dvd (a := 7) (r := 3) (Or.inl rfl)
      ((RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
        (RestrictedStd.Spor.isoInvariant_card_dvd 384) RestrictedStd.Spor.m22_centralizerIn_comps
        e t ht B hB).trans (by norm_num))

theorem sporT1Data_M23
    : SporT1Data .M23 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_M23
  comps := fun _ _ _ _ _ e t ht B hB _ =>
    not_ind_of_not_three (RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
      RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.m23_centralizerIn_comps
      e t ht B hB)

theorem sporT1Data_M24
    : SporT1Data .M24 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_M24
  comps := fun _ _ _ _ _ e t ht B hB _ =>
    not_ind_of_not_three (RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
      RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.m24_centralizerIn_comps
      e t ht B hB)

theorem sporT1Data_J1
    : SporT1Data .J1 where
  oddCore := oddCore_of_free Foote5.sporadicOddCoreFree_J1
  comps := fun S _ _ _ _ e t ht B _ _ => by
    let φ : S ≃* Open.walterJ1 := e.trans Walter.walterJ1EquivNative.symm
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv φ t).toEquiv,
      Walter.J1Props.card_centralizer_of_orderOf_eq_two
        (by rw [MulEquiv.orderOf_eq]; exact ht)] at hd
    exact not_ind_of_dvd (a := 3) (r := 15) (Or.inr rfl) (hd.trans (by norm_num))

theorem sporT1Data_J2
    : SporT1Data .J2 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_J2
  comps := fun S _ _ _ _ e t ht B _ _ => by
    let φ : S ≃* J2Cover.P := e.trans J2Cover.nativeEquivP
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv φ t).toEquiv] at hd
    rcases GH74.Generic.S45.j2_involution_data (p := φ t)
        (by rw [MulEquiv.orderOf_eq]; exact ht) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hd
    · exact not_ind_of_dvd (a := 4) (r := 15) (Or.inr rfl) (hd.trans (by norm_num))
    · exact not_ind_of_dvd (a := 7) (r := 15) (Or.inr rfl) (hd.trans (by norm_num))

theorem sporT1Data_J3
    : SporT1Data .J3 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_J3
  comps := fun S _ _ _ _ e t ht B _ _ => by
    let φ : S ≃* ↥Sporadic.Schreier.j3P := e.trans Sporadic.Schreier.j3PermEquiv
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv φ t).toEquiv,
      RankThree.PartTwo.Census.card_centralizer_j3P (by rw [MulEquiv.orderOf_eq]; exact ht)] at hd
    exact not_ind_of_dvd (a := 7) (r := 15) (Or.inr rfl) (hd.trans (by norm_num))

theorem sporT1Data_HS
    : SporT1Data .HS where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_HS
  comps := fun S _ _ _ _ e t ht B hB htB => by
    obtain ⟨hs, ⟨a, b, hab⟩, -⟩ :=
      Sporadic.SmallOddCore.cti_hs_involution_local_components_simple_order_360 ⟨e⟩ ht
        (isComponentOf_map hB)
    let eB : ↥B ≃* ↥(B.map (centralizer ({t} : Set S)).subtype) :=
      B.equivMapOfInjective _ (centralizer ({t} : Set S)).subtype_injective
    have : IsSimpleGroup ↥(B.map (centralizer ({t} : Set S)).subtype) := hs
    have : IsSimpleGroup ↥B := eB.isSimpleGroup
    refine absurd htB (selfCent_not_mem_of_simple ht inferInstance
      ⟨eB.symm a, eB.symm b, fun h => hab ?_⟩)
    have := congrArg eB h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem sporT1Data_McL
    : SporT1Data .McL where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_McL
  comps := fun S _ _ _ _ e t ht B hB _ => by
    obtain ⟨θ⟩ := RestrictedStd.Spor.mcl_inner_comps e t ht B hB
    rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]
    exact fun h => not_oddLieOrder_L34 h.oddLieOrder

theorem sporT1Data_He
    : SporT1Data .He where
  oddCore := fun S _ _ _ _ e t ht => by
    let ψ : S ≃* Sporadic.HeldB.heP := e.trans Sporadic.HeldB.heEquivP
    rw [← BMCase.gmat_oddCore_eq_pPrimeCore_two]
    exact Sporadic.HeldB.oddCore_eq_bot_of_mulEquiv
      ((RestrictedStd.Spor.centralizerEquiv ψ t).trans
        (RestrictedStd.Spor.centralizerSubtypeEquiv _ (ψ t)))
      (Sporadic.HeldB.heP_centralizerIn_oddCore (ψ t).2
        (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]))
  comps := fun S _ _ _ _ e t ht B hB _ => by
    have h := Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
      ⟨e⟩ ht (isComponentOf_map hB)
    rw [card_quotient_center_map] at h
    rw [h]
    exact fun hi => not_oddLieOrder_L34 hi.oddLieOrder

theorem sporT1Data_Ru
    : SporT1Data .Ru where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_Ru
  comps := fun _ _ _ _ _ e t ht B hB _ =>
    not_ind_of_not_three (RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
      RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.ru_centralizerIn_comps
      (e.trans Sporadic.RuSchreier.ruEquivP) t ht B hB)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
