module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanInnerFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.ClassicalInvolution.Balance (TwoBalancedWrt)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem not_mem_of_orderOf_two_of_isSporadic_on
    {t : G} {P : Subgroup G}
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) : t ∉ P := by
  intro htP
  let t' : ↥P := ⟨t, htP⟩
  have ht'ord : orderOf t' = 2 := (Subgroup.orderOf_mk t htP).trans ht
  have hcentral : ∀ p : ↥P, p * t' = t' * p := by
    intro p
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPt p.2)
  have ht'center : QuotientGroup.mk' (pPrimeCore 2 ↥P) t' ∈
      Subgroup.center (↥P ⧸ pPrimeCore 2 ↥P) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥P) q
    rw [← map_mul, ← map_mul, hcentral p]
  have hcenter : Subgroup.center (↥P ⧸ pPrimeCore 2 ↥P) = ⊥ :=
    CFSG.EvenSporadicStandard.Solomon78.center_eq_bot_of_isSporadic_on hON
  rw [hcenter, Subgroup.mem_bot] at ht'center
  have ht'mem : t' ∈ pPrimeCore 2 ↥P := (QuotientGroup.eq_one_iff t').mp ht'center
  have hdvd : orderOf t' ∣ Nat.card (pPrimeCore 2 ↥P) :=
    Subgroup.orderOf_dvd_natCard _ ht'mem
  rw [ht'ord] at hdvd
  exact (Nat.coprime_two_left.mp
    (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥P))).not_two_dvd_nat hdvd

theorem le_normalizer_wGroup_of_odd_of_twoBalanced {A V : Subgroup G}
    (hB : TwoBalancedWrt A) (hA : IsElemTwo A) (h16 : 16 ≤ Nat.card A)
    (hAV : A ≤ normalizer (V : Set G)) (hV : Odd (Nat.card V)) :
    V ≤ normalizer (wGroup A : Set G) := by
  have hlarge : 2 ^ (3 + 1) ≤ Nat.card A := by
    have h : 2 ^ (3 + 1) = 16 := by norm_num
    rw [h]
    exact h16
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 3
    Nat.prime_two A V hA.isElemAbelian hlarge hAV (Nat.coprime_two_left.mpr hV)
  rw [← hgen]
  refine iSup₂_le fun H hH => ?_
  have hle := CFSG.ClassicalInvolution.Balance.centralizer_le_normalizer_completion
    (A := A) (A₀ := H) hA.isElemAbelian h16 hB hH
  rw [← wGroup_eq_completion hA] at hle
  exact inf_le_right.trans hle

theorem le_normalizer_wGroup_of_odd (hGW : GWTwoBalanced G) {A V : Subgroup G}
    (hA : IsElemTwo A) (h16 : 16 ≤ Nat.card A) (hAV : A ≤ normalizer (V : Set G))
    (hV : Odd (Nat.card V)) :
    V ≤ normalizer (wGroup A : Set G) :=
  le_normalizer_wGroup_of_odd_of_twoBalanced
    (twoBalancedWrt_of_gwTwoBalanced hGW hA) hA h16 hAV hV

theorem card_sup_zpowers_of_on {t : G} {P E : Subgroup G}
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) (hEP : E ≤ P) (hE : IsElemTwo E)
    (hE8 : Nat.card E = 8) :
    IsElemTwo (E ⊔ zpowers t) ∧ Nat.card ↥(E ⊔ zpowers t) = 16 := by
  have htP : t ∉ P := not_mem_of_orderOf_two_of_isSporadic_on ht hPt hON
  have htE : t ∉ E := fun h => htP (hEP h)
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hcomm : ∀ y ∈ E, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hPt (hEP hy))).symm
  obtain ⟨helem, hcard⟩ := GrS5.elemTwo_zpowers_sup ht2 hE hcomm htE
  rw [sup_comm E (zpowers t)]
  exact ⟨helem, by rw [hcard, hE8]⟩

theorem inner_le_wGroup_of_on
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hK : Assembly.KProper Blueprint.Catalog G) {t x : G} {P E : Subgroup G} (ht : orderOf t = 2)
    (hPt : P ≤ centralizer ({t} : Set G))
    (hP : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan)
    (hbad : ¬ ∀ u ∈ oddIn P, ∀ l ∈ P, u * l = l * u) (hEP : E ≤ P) (hxE : x ∈ E)
    (hx : orderOf x = 2)
    (hx1 : centralizer ({x} : Set G) ≠ ⊤) (hxt1 : centralizer ({x * t} : Set G) ≠ ⊤) :
    ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≠ ⊥ ∧
      ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
        ⁅oddIn P, P⁆ ⊓ wGroup (E ⊔ zpowers t) ∧
      wGroup (E ⊔ zpowers t) ≠ ⊥ := by
  obtain ⟨hne, hle⟩ := commutator_inner_ne_bot_le_wGroup_of_on (hS := hS) (hU := hU)
    (hheld := hheld) (hK := hK) ht hPt hP hON hbad (hEP hxE) hx hx1 hxt1
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers t ≤ E ⊔ Subgroup.zpowers t :=
    sup_le ((Subgroup.zpowers_le.mpr hxE).trans le_sup_left) le_sup_right
  have hD : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤ ⁅oddIn P, P⁆ :=
    hle.trans inf_le_left
  have hW : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      wGroup (E ⊔ zpowers t) := (hle.trans inf_le_right).trans (wGroup_mono hsup)
  refine ⟨hne, le_inf hD hW, fun hbot => ?_⟩
  exact hne (le_bot_iff.mp (hW.trans (le_of_eq hbot)))

theorem oddIn_le_normalizer_wGroup_of_on_of_twoBalanced
    {t : G} {P E : Subgroup G} (hB : TwoBalancedWrt (E ⊔ zpowers t))
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan) (hEP : E ≤ P) (hE : IsElemTwo E)
    (hE8 : Nat.card E = 8) :
    oddIn P ≤ normalizer (wGroup (E ⊔ zpowers t) : Set G) := by
  obtain ⟨hA, hcard⟩ := card_sup_zpowers_of_on ht hPt hON hEP hE hE8
  have h16 : 16 ≤ Nat.card ↥(E ⊔ zpowers t) := by rw [hcard]
  have hPnorm : P ≤ normalizer (oddIn P : Set G) := by
    have hnorm : Subgroup.normalizer (pPrimeCore 2 ↥P : Set ↥P) = ⊤ :=
      @Subgroup.normalizer_eq_top ↥P _ (pPrimeCore 2 ↥P) CFSG.pPrimeCore_normal
    have h := Subgroup.le_normalizer_map (H := pPrimeCore 2 ↥P) (f := P.subtype)
    rwa [hnorm, Subgroup.map_top, Subgroup.range_subtype] at h
  have hEnorm : E ≤ normalizer (oddIn P : Set G) := hEP.trans hPnorm
  have htnorm : Subgroup.zpowers t ≤ normalizer (oddIn P : Set G) := by
    rw [Subgroup.zpowers_le]
    refine GrS5.mem_normalizer_of_commute fun y hy => ?_
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hPt u.2)).symm
  refine le_normalizer_wGroup_of_odd_of_twoBalanced hB hA h16 (sup_le hEnorm htnorm) ?_
  rw [oddIn, Subgroup.card_map_of_injective P.subtype_injective]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥P))

end CFSG.ComponentClassification.GrSLit.L34Sec5S
