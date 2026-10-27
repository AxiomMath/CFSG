module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourExceptionTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientTwoGroupNotNormalizerContainsCPrime
public import CFSG.Dihedral.PrimeNormalizerQuotientAlternatives
public import CFSG.Assembly.OddCoreBalance
import all CFSG.Dihedral.BlueprintDefs
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

variable {G : Type} [Group G]

theorem cycles_top_iff_normalizerContainsCPrime (V : Subgroup G)
    (hV : IsKleinFour V) :
    Cycles (⊤ : Subgroup G) V ↔ NormalizerContainsCPrime V := by
  let : IsKleinFour V := hV
  rw [normalizerContainsCPrime_iff_exists]
  constructor
  · rintro ⟨x, _, hxN, hxmove⟩
    refine ⟨x, hxN, ?_⟩
    intro hx2
    let xn : Subgroup.normalizer (V : Set G) := ⟨x, hxN⟩
    let a : MulAut V := V.normalizerMonoidHom xn
    have ha : ∀ v : V, v ≠ 1 → a v ≠ v := by
      intro v hv hfix
      exact hxmove v v.property (fun h => hv (Subtype.ext h))
        (congrArg Subtype.val hfix)
    have ha2 : a ^ 2 = 1 := by
      have hker : xn ^ 2 ∈ V.normalizerMonoidHom.ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact hx2
      simpa only [MonoidHom.mem_ker, map_pow] using hker
    have hVne : V ≠ ⊥ := by
      intro h
      have hc := hV.card_four
      rw [h, Subgroup.card_bot] at hc
      omega
    obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
    have hav : a v ≠ v := ha v hv
    have hprod : v * a v ≠ 1 := by
      intro h
      have heq := mul_eq_one_iff_eq_inv.mp h
      exact hav (by simpa only [IsKleinFour.inv_eq_self] using heq.symm)
    have haav : a (a v) = v := by
      exact DFunLike.congr_fun ha2 v
    have hfix : a (v * a v) = v * a v := by
      rw [map_mul, haav]
      exact IsKleinFour.isMulCommutative.is_comm.comm _ _
    exact ha (v * a v) hprod hfix
  · rintro ⟨x, hxN, hx2⟩
    refine ⟨x, Subgroup.mem_top x, hxN, ?_⟩
    intro v hv hv1 hfix
    let xn : Subgroup.normalizer (V : Set G) := ⟨x, hxN⟩
    let a : MulAut V := V.normalizerMonoidHom xn
    have hv1' : (⟨v, hv⟩ : V) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
    have hafix : a (⟨v, hv⟩ : V) = ⟨v, hv⟩ := Subtype.ext hfix
    have ha2 : a ^ 2 = 1 := mulAut_sq_eq_one_of_fixed_ne_one a hv1' hafix
    have hker : xn ^ 2 ∈ V.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact ha2
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    exact hx2 hker

theorem cycles_iff_cycles_subgroupOf (H V : Subgroup G) (hVH : V ≤ H) :
    Cycles H V ↔ Cycles (⊤ : Subgroup H) (V.subgroupOf H) := by
  have hnorm : (Subgroup.normalizer (V : Set G)).comap H.subtype =
      Subgroup.normalizer (V.subgroupOf H : Set H) :=
    Subgroup.comap_normalizer_eq_of_le_range (by simpa using hVH)
  constructor
  · rintro ⟨x, hxH, hxN, hxmove⟩
    have hxN' : (⟨x, hxH⟩ : H) ∈
        Subgroup.normalizer (V.subgroupOf H : Set H) := by
      rw [← hnorm]
      exact hxN
    refine ⟨⟨x, hxH⟩, Subgroup.mem_top _, hxN', ?_⟩
    intro v hv hv1 hfix
    exact hxmove v hv (fun h => hv1 (Subtype.ext h)) (congrArg Subtype.val hfix)
  · rintro ⟨x, _, hxN, hxmove⟩
    have hxN' : (x : G) ∈ Subgroup.normalizer (V : Set G) := by
      change x ∈ (Subgroup.normalizer (V : Set G)).comap H.subtype
      rwa [hnorm]
    refine ⟨x, x.property, hxN', ?_⟩
    intro v hv hv1 hfix
    exact hxmove (⟨v, hVH hv⟩ : H) hv
      (fun h => hv1 (congrArg Subtype.val h)) (Subtype.ext hfix)

theorem cycles_iff_normalizerContainsCPrime (H V : Subgroup G)
    (hVH : V ≤ H) (hV : IsKleinFour V) :
    Cycles H V ↔ NormalizerContainsCPrime (V.subgroupOf H) :=
  (cycles_iff_cycles_subgroupOf H V hVH).trans
    (cycles_top_iff_normalizerContainsCPrime _ (isKleinFour_subgroupOf hVH hV))

variable [Finite G]

theorem not_two_quotient_of_cycles (H V : Subgroup G)
    (hVH : V ≤ H) (hV : IsKleinFour V) (hc : Cycles H V) :
    ¬ IsPGroup 2 (H ⧸ Assembly.oddCore H) := by
  intro htwo
  have hQ : IsPGroup 2 (H ⧸ CFSG.pPrimeCore 2 H) := by
    exact htwo.of_equiv (QuotientGroup.quotientMulEquivOfEq
      (Assembly.Dichotomy.oddCore_eq_pPrimeCore H))
  exact quotientTwoGroup_not_normalizerContainsCPrime hQ (V.subgroupOf H)
    (isKleinFour_subgroupOf hVH hV)
    ((cycles_iff_normalizerContainsCPrime H V hVH hV).mp hc)

theorem not_sylowTwoQuotient_of_cycles (H V : Subgroup G)
    (hVH : V ≤ H) (hV : IsKleinFour V) (hc : Cycles H V) :
    ¬ HasSylowTwoQuotient H := fun h =>
  not_two_quotient_of_cycles H V hVH hV hc
    (quotient_isPGroup_of_hasSylowTwoQuotient H h)

end CFSG.DihedralBlueprint
