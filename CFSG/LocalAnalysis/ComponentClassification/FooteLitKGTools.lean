module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGBase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdReduction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdSporadic

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.RestrictedStd

theorem smallCentralQuotient_of_footeFamilyType {G : Type} [Group G] {L : Subgroup G}
    (hO : pPrimeCore 2 L = ⊥) (h : FooteFamilyType L) : SmallCentralQuotient L := by
  have hZ := HarrisLit.fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  let f : (L ⧸ center L) ≃* (L ⧸ Open.fusionZStar L) := QuotientGroup.quotientMulEquivOfEq hZ.symm
  rcases h with he7 | ⟨p, n, hp, hp2, hn, h5, hm⟩
  · obtain ⟨e7⟩ := he7
    exact Or.inr (Or.inl ⟨f.trans e7⟩)
  · exact Or.inl ⟨p, n, hp, hp2, hn, h5, LieType.CurtisTits.lieModel_of_mulEquiv f.symm hm⟩

theorem noFooteComponent_of_comps {G : Type} [Group G] [Finite G]
    (hodd : ∀ t : G, orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥)
    (hcomp : ∀ t : G, orderOf t = 2 → Spor.CompsSatisfy (centralizer ({t} : Set G))
      fun Y _ => ¬ SmallCentralQuotient Y) :
    NoFooteComponent G := by
  rintro L ⟨⟨t, ht2, hLC, hLp⟩, htype, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := L.subgroupOf (centralizer ({t} : Set G)) with hMdef
  apply hcomp t ht2 M (isComponent_of_isPComponent_two (hodd t ht2) hLp)
  have hOM : pPrimeCore 2 ↥M = ⊥ := by
    obtain ⟨hs, -, -⟩ :=
      (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).1 hLp
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs
    rw [hodd t ht2, inf_bot_eq] at h1
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp h1
  let e₀ : ↥L ≃* ↥M := (subgroupOfEquivOfLe hLC).symm
  have hOL : pPrimeCore 2 ↥L = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 e₀
    rw [hOM] at h1
    exact (map_eq_bot_iff_of_injective _ e₀.injective).mp h1
  exact smallCentralQuotient_of_mulEquiv e₀.symm (smallCentralQuotient_of_footeFamilyType hOL htype)

theorem exists_mul_ne_mul_of_isFooteComponent {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsFooteComponent L) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨⟨t, -, hLt, hLpc⟩, -, -⟩ := hL
  obtain ⟨u, v, huv⟩ :=
    exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hLt hLpc)
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  refine ⟨u', v', fun h => huv ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, show u' * v' = v' * u' from Subtype.ext h]

theorem noFooteComponent_of_comps' {G : Type} [Group G] [Finite G]
    (hodd : (∃ a b : G, a * b ≠ b * a) → ∀ t : G, orderOf t = 2 →
      pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥)
    (hcomp : ∀ t : G, orderOf t = 2 → Spor.CompsSatisfy (centralizer ({t} : Set G))
      fun Y _ => ¬ SmallCentralQuotient Y) :
    NoFooteComponent G := fun L hL =>
  noFooteComponent_of_comps (hodd (exists_mul_ne_mul_of_isFooteComponent hL)) hcomp L hL

theorem pPrimeCore_eq_bot_of_sporadicOddCoreFree {s : TauCeti.SporadicName}
    (h : CatalogueU.SporadicOddCoreFree s) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) (hG : Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s))
    (t : G) (ht : orderOf t = 2) : pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ := by
  have hF : CFSG.generalizedFitting G = ⊤ := by
    rw [generalizedFitting_eq_componentClassification]
    exact GSLit.generalizedFitting_eq_top_of_simple
  obtain ⟨e⟩ := hG
  have hs : IsSimpleGroup ↥(CFSG.generalizedFitting G) := by
    rw [hF]
    exact Subgroup.topEquiv.isSimpleGroup
  have hnc : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a := by
    rw [hF]
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun h' => hab (congrArg Subtype.val h')⟩
  have hiso : Nonempty (↥(CFSG.generalizedFitting G) ≃* Blueprint.NativeSporadic.Carrier s) := by
    rw [hF]
    exact ⟨Subgroup.topEquiv.trans e⟩
  have h1 := h G hs hnc hiso t ht
  rwa [(CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm] at h1

end CFSG.ComponentClassification.FooteLit.KG
