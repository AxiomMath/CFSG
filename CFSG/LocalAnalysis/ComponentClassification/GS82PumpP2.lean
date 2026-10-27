module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP5Basic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.Sporadic.Recognition.J3MultiplierCert
public import CFSG.GH74.E2.ComponentsBasic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf

theorem chevOddCentralPumpInput_of_leaf
    (hleaf : ChevOddPumpLeaf) :
    ChevOddCentralPumpInput := by
  intro H _ _ hK M hM x hx hxN T hTM hTC hTpc r hr hr2 hTY hTY2 w hw2 hwT hwZ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ {Y : Type} [Group Y], (↥T ⧸ Open.fusionZStar ↥T ≃* Y) →
      HarrisLit.IsSimpleChevalleyOver r Y ∧ ¬ GH74.GLS.InChev2 Y := fun e => by
    obtain ⟨τ, n, f, h⟩ := hTY
    exact ⟨⟨τ, n, f, Blueprint.LieModel.of_mulEquiv e h⟩,
      fun h => hTY2 (GH74.E2.inChev2_of_mulEquiv e.symm h)⟩
  have hMx : conjugate M x = M := mem_normalizer_iff_map_conj_eq.mp (inv_mem hxN)
  have hTC' : T ≤ (M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H) := by
    rw [hMx, sup_idem]
    exact le_inf hTM hTC
  have hTpc' : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTC' inf_le_right hTpc
  obtain ⟨hle, -, heq⟩ := UnbalancedGS.involution_orbit_fixed_component_quotient_comparison hx M
    hM _ rfl _ rfl T hTC' hTpc'
  have : Group.IsPerfect T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hTpc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
      (subgroupOfEquivOfLe hTC).surjective
  have hTq : IsQuasisimple (T ⧸ pPrimeCore 2 T) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hTC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hTpc)
  obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
  rcases hle.lt_or_eq with hlt | hidx
  swap
  ·
    obtain ⟨e⟩ := stable_case_type hM hTM hTq ((heq hidx).2 hMx.symm)
    exact key e
  have hTM' : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
  have hTp' : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTM' inf_le_right hTpc
  obtain ⟨σ, hPF, ⟨eP⟩⟩ := exists_properFixedComponent_of_stable_image hx hM hMx hTM' hTp' hlt
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  have hna := hMq.2.2
  have hcat : Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK M
      ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hP1, hP2⟩ := key eP
  rcases hleaf _ inferInstance hna hcat σ _ hPF r hr hr2 hP1 hP2 with ⟨⟨τ, n, f, hS1⟩, hS2⟩ |
      ⟨⟨eJ⟩, -⟩
  · exact ⟨⟨τ, n, f, Blueprint.LieModel.of_mulEquiv eMS hS1⟩,
      fun h => hS2 (GH74.E2.inChev2_of_mulEquiv eMS.symm h)⟩
  ·
    exfalso
    obtain ⟨wm, hwm, rfl⟩ := hwZ
    have hw2' : orderOf wm = 2 := by
      rw [← hw2]
      exact (orderOf_injective M.subtype M.subtype_injective wm).symm
    obtain ⟨hc, hne⟩ := mk_mem_center_ne_one hwm hw2'
    have hodd := RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
      Sporadic.Recognition.J3Multiplier.noPerfectDoubleCover_nativeJ3_of_certificate
      (↥M ⧸ pPrimeCore 2 ↥M) hMq.1.commutator_eq_top ⟨eJ⟩
    have h2 : orderOf (⟨_, hc⟩ : center (↥M ⧸ pPrimeCore 2 ↥M)) = 2 := by
      rw [Subgroup.orderOf_mk]
      refine orderOf_eq_prime ?_ hne
      rw [← map_pow, ← hw2', pow_orderOf_eq_one, map_one]
    have hdvd := orderOf_dvd_natCard (⟨_, hc⟩ : center (↥M ⧸ pPrimeCore 2 ↥M))
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end CFSG.ComponentClassification.GS82PumpInputs
