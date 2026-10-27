module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.SetupPhi
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.SporHoldsFree
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.SporHoldsHe
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Hom

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace KForm.Mod

theorem nonabelian_of_centralizer_eq_bot_of_simple {K : Type} [Group K] (S : Subgroup K)
    [IsSimpleGroup ↥S] (hC : centralizer (S : Set K) = ⊥) : ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hS : S = ⊥ := by
    rw [eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥S)
  have : (a : K) ∈ (⊥ : Subgroup K) := hS ▸ a.2
  exact ha (Subtype.ext (by simpa using this))

theorem sporadic_nonHe_false
    {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal] (hS : IsSimpleGroup ↥S)
    (hC : centralizer (S : Set K) = ⊥) (hna : ∃ a b : ↥S, a * b ≠ b * a)
    (hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S))
    {s : TauCeti.SporadicName} (es : ↥S ≃* NativeSporadic.Carrier s)
    (hfree : CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree s) (hs : s ≠ .He)
    {z : K} (hz : orderOf z = 2) (ψ : ↥(centralizer ({z} : Set K)) →* Z2S6)
    (hψs : Function.Surjective ψ) (hψo : Odd (Nat.card ψ.ker)) : False := by
  have hσ : orderOf (MulAut.conjNormal (H := S) z) = 2 := orderOf_conjNormal_eq_two S hC hz
  set σ : MulAut ↥S := MulAut.conjNormal (H := S) z with hσdef
  have hcore : CFSG.oddCore ↥(fixedSubgroup σ) = ⊥ :=
    CFSG.ComponentClassification.CatLeaf.oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (CFSG.ComponentClassification.CatLeaf.mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree
        hna es) hσ
  set Φ : ↥(fixedSubgroup σ) →* Z2S6 := fixedPhi S z ψ with hΦ
  have hΦo : Odd (Nat.card Φ.ker) := odd_ker_fixedPhi hψo
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hcore]
    exact CFSG.EvenSporadicStandard.M23Std.le_fusionOddCore_of_odd (N := Φ.ker) hΦo
  have hA : a6Factor ≤ Φ.range := a6Factor_le_range_fixedPhi hC hsolv hψs hψo
  obtain ⟨D, hDn, ⟨eD⟩, -, hdvd, -, -, -⟩ := z2s6_data_of_injective Φ hΦinj hA
  haveI := hDn
  have hD : CFSG.IsComponent D := CFSG.ComponentClassification.CatFC.isComponent_of_alt6 D eD
  have hcard : Nat.card (↥D ⧸ center ↥D) = 360 :=
    CFSG.ComponentClassification.CatFC.card_quotient_center_alt6 eD
  have hle : Nat.card ↥(fixedSubgroup σ) ≤ 1440 := Nat.le_of_dvd (by norm_num) hdvd
  rcases CFSG.ComponentClassification.CatFC.sporadic_comp_360 hS hna es hσ hD hcard with
    ⟨rfl, hin⟩ | ⟨rfl, -⟩
  · obtain ⟨u, hu⟩ := hin
    have hI : Function.Injective (MulAut.conj : ↥S →* MulAut ↥S) :=
      CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
    have hu2 : orderOf u = 2 := by
      have h1 := orderOf_injective (MulAut.conj : ↥S →* MulAut ↥S) hI u
      rw [h1.symm]
      simpa [hu] using hσ
    have hfix : fixedSubgroup σ = centralizer ({u} : Set ↥S) := by
      rw [← hu]
      exact CFSG.SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf u
    have hc := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs
      ⟨es⟩ u hu2
    rw [← hfix] at hc
    omega
  · exact absurd rfl hs

end KForm.Mod

theorem sporadicZ2S6Leaf_holds :
    SporadicZ2S6Leaf := by
  intro K _ _ S hSn hSs hC hrep z hz hζ
  obtain ⟨ζ⟩ := hζ
  haveI := hSn
  haveI := hSs
  have hna : ∃ a b : ↥S, a * b ≠ b * a :=
    KForm.Mod.nonabelian_of_centralizer_eq_bot_of_simple S hC
  let ψ : ↥(centralizer ({z} : Set K)) →* KForm.Z2S6 :=
    ζ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.fusionOddCore ↥(centralizer ({z} : Set K))))
  have hψs : Function.Surjective ψ := ζ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψo : Odd (Nat.card ψ.ker) := by
    change Odd (Nat.card (ζ.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.Open.fusionOddCore ↥(centralizer ({z} : Set K))))).ker)
    rw [MonoidHom.ker_comp_of_injective _ _ ζ.injective, QuotientGroup.ker_mk']
    exact CFSG.EvenSporadicStandard.M23Std.natCard_fusionOddCore_odd _
  obtain ⟨s, ⟨es⟩⟩ := hrep
  by_cases hs : s = .He
  · subst hs
    have hσ : orderOf (MulAut.conjNormal (H := S) z) = 2 :=
      KForm.orderOf_conjNormal_eq_two S hC hz
    haveI : (KForm.Mod.fixedPhi S z ψ).ker.Normal := MonoidHom.normal_ker _
    exact KForm.Mod.he_false_of_odd_normal hSs hna es hσ
      (N := (KForm.Mod.fixedPhi S z ψ).ker) (KForm.Mod.odd_ker_fixedPhi hψo)
      (KForm.Mod.natCard_quotient_ker_dvd _)
  · have hcat : Catalog ↥S := Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ⟨es⟩⟩)))
    have hsolv := CFSG.RankThree.PartOne.SPOR.schreierFor_catalog ↥S hna hcat
    exact KForm.Mod.sporadic_nonHe_false S hSs hC hna hsolv es
      (KForm.Mod.sporadicOddCoreFree_of_ne_he s hs) hs hz ψ hψs hψo

end CFSG.EvenSporadicStandard.M24Std
