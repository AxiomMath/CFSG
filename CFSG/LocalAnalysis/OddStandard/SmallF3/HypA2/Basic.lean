module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BProperty
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem centralizer_pair_eq_inf {G : Type} [Group G] (a b : G) :
    centralizer ({a, b} : Set G) = centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    Set.mem_insert_iff, forall_eq_or_imp, forall_eq]

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] : oddCore X = pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]

@[expose] noncomputable def conjAut {G : Type} [Group G] (K : Subgroup G) (x : G)
    (hx : K.map (MulAut.conj x).toMonoidHom = K) : MulAut ↥K :=
  ((MulAut.conj x).subgroupMap K).trans (MulEquiv.subgroupCongr hx)

theorem coe_conjAut_apply {G : Type} [Group G] (K : Subgroup G) (x : G)
    (hx : K.map (MulAut.conj x).toMonoidHom = K) (k : ↥K) :
    ((conjAut K x hx k : ↥K) : G) = x * k * x⁻¹ := by
  rfl

theorem isComponentIn_of_isPComponent {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hH : oddCore H = ⊥) (hKH : K ≤ H) (hK : IsPComponent 2 (K.subgroupOf H)) :
    Omega.IsComponentIn K H := by
  refine ⟨hKH, ?_⟩
  exact Omega.isComponent_of_isPComponent_two_of_oddCore_eq_bot hH hK

theorem oddCore_eq_bot_of_isComponentIn {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hH : oddCore H = ⊥) (hK : Omega.IsComponentIn K H) : oddCore ↥K = ⊥ := by
  have hG : pPrimeCore 2 ↥H = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two ↥H]
    exact hH
  have hcore : pPrimeCore 2 ↥(K.subgroupOf H) = ⊥ :=
    CFSG.ComponentClassification.HarrisLit.pPrimeCore_eq_bot_of_isSubnormal hG hK.2.2
  have hmap := CFSG.pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hK.1)
  rw [hcore, Subgroup.map_bot] at hmap
  rw [oddCore_eq_pPrimeCore_two ↥K]
  exact hmap.symm

theorem isPGroup_two_center_of_isComponentIn {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hH : oddCore H = ⊥) (hK : Omega.IsComponentIn K H) : IsPGroup 2 ↥(center ↥K) := by
  have hO : pPrimeCore 2 ↥K = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two ↥K]
    exact oddCore_eq_bot_of_isComponentIn hH hK
  exact CFSG.ComponentClassification.Sol78.center_isPGroup_two hO

theorem catalog_quotient_center_of_isComponentIn {G : Type} [Group G] [Finite G]
    (hG : Assembly.KProper Catalog G) {H K : Subgroup G} (hH : H ≠ ⊤)
    (hK : Omega.IsComponentIn K H) : Catalog (↥K ⧸ center ↥K) := by
  have hKtop : K ≠ ⊤ := fun h => hH (top_unique (h ▸ hK.1))
  have hsimple : IsSimpleGroup (↥K ⧸ center ↥K) := by
    haveI : IsSimpleGroup (↥(K.subgroupOf H) ⧸ center ↥(K.subgroupOf H)) := hK.2.1.2.1
    exact (CFSG.ComponentClassification.Sol78.centerQuotCongr
      (Subgroup.subgroupOfEquivOfLe hK.1)).symm.isSimpleGroup
  haveI : IsSimpleGroup (↥K ⧸ center ↥K) := hsimple
  have hnonab : ∃ a b : ↥K ⧸ center ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK.2.1.2.2
    refine ⟨CFSG.ComponentClassification.Sol78.centerQuotCongr
        (Subgroup.subgroupOfEquivOfLe hK.1) a,
      CFSG.ComponentClassification.Sol78.centerQuotCongr
        (Subgroup.subgroupOfEquivOfLe hK.1) b, fun hc => hab ?_⟩
    have hcongr : CFSG.ComponentClassification.Sol78.centerQuotCongr
          (Subgroup.subgroupOfEquivOfLe hK.1) (a * b) =
        CFSG.ComponentClassification.Sol78.centerQuotCongr
          (Subgroup.subgroupOfEquivOfLe hK.1) (b * a) := by
      rw [map_mul, map_mul, hc]
    exact (CFSG.ComponentClassification.Sol78.centerQuotCongr
      (Subgroup.subgroupOfEquivOfLe hK.1)).injective hcongr
  have hG' : CFSG.KCore.KProperNonab Catalog G := hG
  exact CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.SectionRank.catalog_isoInvariant
    hG' K hKtop hnonab (QuotientGroup.mk' (center ↥K)) (QuotientGroup.mk'_surjective _)

end CFSG.OddStandard.SmallF3.HypA2
