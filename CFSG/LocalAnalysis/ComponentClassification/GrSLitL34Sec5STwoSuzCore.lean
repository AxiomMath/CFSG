module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzActive
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzModule
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzConfig
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzSteps
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

section

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

section Certified


theorem l34TwoSuzCoreOfSignalizer_of_parts (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (h6a : TwoSuzAutTwoRank)
    (h6b : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound)
    (h6c : TwoSuzCentralizerFacts) : L34TwoSuzCoreOfSignalizer := by
  intro G _ _ t P hset hZ hvan
  obtain ⟨hbase, ht, hPt, hPc, hPn, -, hτ⟩ := hset
  by_contra hD
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hperf : Group.IsPerfect ↥P := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hPc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPt).toMonoidHom)
      (subgroupOfEquivOfLe hPt).surjective
  obtain ⟨p, hpf, hp2, V, _, _, _, ρ, hirr, hker, hU1, hlift⟩ :=
    exists_chiefModule (C := centralizer ({t} : Set G)) ⟨hPt, hPc⟩ hD
  have hrank : pRank 2 ↥(centralizer ({t} : Set G)) ≤ 8 :=
    pRank_centralizer_le_of_zStarAutRank hS hU hheld hbase ht hPt hPc hPn (h6a _ hτ) hvan hD
  have hr : 3 ≤ pRank 2 ↥P := three_le_pRank_of_sporadic_suz_fusionZStar hτ
  obtain ⟨z, A, hz, hzZ, hZeq, hA, hzA, hA8, hAZ⟩ := exists_twoSuz_testConfig h6b hperf hτ hr hZ
  have hUo : Odd (Nat.card (pPrimeCore 2 ↥P)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hZc : ∀ y ∈ Open.fusionZStar ↥P, ∀ g : ↥P, ⁅y, g⁆ ∈ pPrimeCore 2 ↥P := by
    intro y hy g
    rw [GrS4.fusionZStar_eq_comap_pPrimeCore] at hy
    have hy' : QuotientGroup.mk' (pPrimeCore 2 ↥P) y ∈ center (↥P ⧸ pPrimeCore 2 ↥P) := hy
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥P) ⁅y, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp hy' _).symm
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  refine false_of_twoSuz_parity hperf (pPrimeCore 2 ↥P) (Open.fusionZStar ↥P) hUo z hz hZeq hZc
    hp2 ρ hirr hker hU1 A hA hzA hA8 hAZ ?_
  intro u huA hu1 huz
  have hu2 : u * u = 1 := hA.2 u huA
  have huz' : u * z = z * u := hA.1 u huA z hzA
  have huZ : u ∉ Open.fusionZStar ↥P := fun h => by
    rcases hAZ u huA h with h' | h'
    · exact hu1 h'
    · exact huz h'
  obtain ⟨H, hHc, hHp, hH3, hHgen⟩ :=
    exists_doubleCentralizer_subgroup h6b h6c hperf hτ hZ hu2 hz huz' hzZ huZ
  refine ⟨H, hHc, hHgen, ?_⟩
  intro v hv w hw k hk
  have hvA : v ∈ A := by
    rcases hv with rfl | rfl
    · exact huA
    · exact mul_mem huA hzA
  have hv2 : v * v = 1 := hA.2 v hvA
  have hvZ : v ∉ Open.fusionZStar ↥P := by
    rcases hv with rfl | rfl
    · exact huZ
    · intro h
      apply huZ
      have h' := mul_mem h (inv_mem hzZ)
      rwa [mul_inv_cancel_right] at h'
  have hHv : ∀ k ∈ H, k * v = v * k := by
    intro k hk
    obtain ⟨hku, hkz⟩ := hHc k hk
    rcases hv with rfl | rfl
    · exact hku
    · rw [← mul_assoc, hku, mul_assoc, hkz, mul_assoc]
  obtain ⟨u', hu'U, hu'v, hfix⟩ := hlift v hv2 w hw
  apply hfix k
  set vG : G := (v : G) with hvG
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ one_mem _)
  have hvG2 : orderOf vG = 2 := by
    rw [hvG, Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two, hv2]) hv1
  have htvG : t * vG = vG * t := (mem_centralizer_singleton_iff.mp (hPt v.2)).symm
  have hne : t ≠ vG := by
    intro h
    apply hvZ
    have htP : t ∈ P := h ▸ v.2
    have hcen : (⟨t, htP⟩ : ↥P) ∈ center ↥P := mem_center_iff.mpr fun g =>
      Subtype.ext (mem_centralizer_singleton_iff.mp (hPt g.2))
    have hvt : v = ⟨t, htP⟩ := Subtype.ext h.symm
    rw [hvt, GrS4.fusionZStar_eq_comap_pPrimeCore]
    exact mem_center_iff.mpr fun g => by
      obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥P) g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hcen g']
  set AG : Subgroup G := A.map P.subtype with hAG
  have hAG2 : IsElemTwo AG := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hA.1 a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (hA.2 a ha)
  have htAG : ∀ y ∈ AG, t * y = y * t := by
    rintro _ ⟨a, -, rfl⟩
    exact (mem_centralizer_singleton_iff.mp (hPt a.2)).symm
  set B : Subgroup G := zpowers t ⊔ AG with hBdef
  have hB2 : IsElemTwo B := (isElemTwo_zpowers htt).sup hAG2 fun x hx y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (htAG y hy) i).eq
  have hBt : B ≤ centralizer ({t} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) ((map_subtype_le A).trans hPt)
  have hB8 : 8 ≤ Nat.card B := by
    have h1 : Nat.card AG = Nat.card A := card_map_of_injective P.subtype_injective
    have h2 : Nat.card AG ≤ Nat.card B := Subgroup.card_le_of_le le_sup_right
    omega
  have hBab : Open.IsElemAbelian 2 B :=
    ⟨isMulCommutative_iff_of_setLike.mpr hB2.1, fun x hx => by rw [pow_two]; exact hB2.2 x hx⟩
  have hWB : wGroup B = ⊥ := hvan B hBt hBab hB8
  have htB : t ∈ B := mem_sup_left (mem_zpowers t)
  have hvB : vG ∈ B := mem_sup_right ⟨v, hvA, rfl⟩
  set HG : Subgroup G := H.map P.subtype with hHG
  have hHGt : HG ≤ centralizer ({t} : Set G) := (map_subtype_le H).trans hPt
  have hHGv : HG ≤ centralizer ({vG} : Set G) := by
    rintro _ ⟨h, hh, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hHv h hh))
  have hHGp : ⁅HG, HG⁆ = HG := by rw [hHG, ← Subgroup.map_commutator, hHp]
  have hHG3 : HasSimpleQuotient3Quart ↥HG :=
    HasSimpleQuotient3Quart.of_mulEquiv (Subgroup.equivMapOfInjective H P.subtype
      P.subtype_injective) hH3
  have hcomm := commutator_eq_bot_of_perfect_twoInvolutions hbase ht hvG2 htvG hne htB hvB hWB
    hrank hHGt hHGv hHGp hHG3
  have hu'Y : (u' : G) ∈ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({vG} : Set G) := by
    refine mem_inf.mpr ⟨GSLit.map_pPrimeCore_le_of_isPComponent hPt hPc ⟨u', hu'U, rfl⟩, ?_⟩
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hu'v)
  have h1 := commutator_mem_commutator (mem_map_of_mem P.subtype hk) hu'Y
  rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact Subtype.ext h1

end Certified

end

section

section Certified


theorem l34TwoSuzCoreOfSignalizer_holds : L34TwoSuzCoreOfSignalizer :=
  l34TwoSuzCoreOfSignalizer_of_parts RankThree.PartOne.SPOR.schreierFor_catalog
    FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds KProperRelativeB.heldInput
    twoSuzAutTwoRank_holds suzCentralTwoGroupOrderBound_holds twoSuzCentralizerFacts_holds

end Certified

end

end CFSG.ComponentClassification.GrSLit.L34Sec5S
