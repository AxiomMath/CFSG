module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoreAt

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open scoped commutatorElement

theorem l34ONanSignalizerVanishing_of_inputs (hcat : SuzONanNotProperFixedCatalog)
    (hGold : GoldschmidtStronglyClosedInput) (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) :
    L34SignalizerVanishingAt (fun X _ => IsSporadic X .ONan) := by
  intro G _ _ t P hset E hEt hEab hE8
  classical
  obtain ⟨hbase, ht2, hPt, hPp, hPn, -, hPON⟩ := id hset
  have hCP : centralizer ({t} : Set G) ≤ normalizer (P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hPt).mp hPn
  have hperf : Group.IsPerfect ↥P := by
    have := CatalogueBAlternating.pComponent_perfect hPp
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPt).toMonoidHom)
      (subgroupOfEquivOfLe hPt).surjective
  have hON := isSporadic_pPrimeCore_of_fusionZStar_on hperf hPON
  obtain ⟨W, hWodd, hPW, hW⟩ :=
    exists_wGroup_of_on (gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput
      hbase.2.2.2.2.2.1) ht2 hPt hCP hON
  have hEe : IsElemTwo E :=
    ⟨fun x hx y hy => congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
      fun x hx => by rw [← pow_two]; exact hEab.2 x hx⟩
  rw [hW E hEt hEe hE8]
  by_contra hW1
  obtain ⟨-, -, -, -, -, hML, -⟩ := hset
  exact false_of_onanWConfig hcat hGold hS hCI hGA h13
    ⟨hbase, ht2, hPt, hPp, hPn, hML, hPON, hWodd, hW1, hPW, fun E hE hEe hE8 => hW E hE hEe hE8⟩

theorem centralizes_oddIn_of_signalizer
    {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G)
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CFSG.ComponentClassification.CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : CFSG.ComponentClassification.KProperRelativeB.HeldInput)
    {t : G} {P : Subgroup G} (ht : orderOf t = 2)
    (hPt : P ≤ Subgroup.centralizer ({t} : Set G))
    (hP : IsPComponent 2 (P.subgroupOf (Subgroup.centralizer ({t} : Set G))))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan)
    (hWv : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({t} : Set G) →
      IsElemTwo E → 8 ≤ Nat.card E → wGroup E = ⊥) :
    ⁅oddIn P, P⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hbad : ¬ ∀ u ∈ oddIn P, ∀ l ∈ P, u * l = l * u := by
    intro hall
    apply hne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu l hl
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hall u hu l hl
  obtain ⟨R₀⟩ : Nonempty (Sylow 2 ↥P) := inferInstance
  have hR : IsSylowTwoIn ((R₀ : Subgroup ↥P).map P.subtype) P :=
    ⟨Subgroup.map_subtype_le _, R₀,
      (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm⟩
  let E : Subgroup G := omSub (sqSub ((R₀ : Subgroup ↥P).map P.subtype))
  obtain ⟨hEe, hE8⟩ := omSub_sqSub_of_on hON hR
  have hEP : E ≤ P := (omSub_sqSub_le _).trans hR.1
  obtain ⟨x, hxE, hx1, hxt⟩ : ∃ x ∈ E, x ≠ 1 ∧ x ≠ t := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers t := fun x hx => by
      by_cases h1 : x = 1
      · rw [h1]; exact one_mem _
      · rw [hno x hx h1]; exact Subgroup.mem_zpowers t
    have h := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, ht, hE8] at h
    omega
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hEe.2 x hxE) hx1
  have hcen : ∀ y : G, y ≠ 1 → Subgroup.centralizer ({y} : Set G) ≠ ⊤ := by
    intro y hy htop
    have hyZ : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({y} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h] at hyZ
      exact hy (Subgroup.mem_bot.mp hyZ)
    · obtain ⟨g, k, hgk⟩ := hnonab
      have hg : g ∈ Subgroup.center G := h ▸ Subgroup.mem_top g
      exact hgk (Subgroup.mem_center_iff.mp hg k).symm
  have hxt1 : x * t ≠ 1 := fun h => hxt (by
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, pow_two] at this
    calc x = x * t * t := by rw [mul_assoc, htt, mul_one]
      _ = t := by rw [h, one_mul])
  obtain ⟨-, -, hWne⟩ := inner_le_wGroup_of_on hS hU hheld hKP ht hPt hP hON hbad hEP
    hxE hx2 (hcen x hx1) (hcen (x * t) hxt1)
  obtain ⟨hEte, hEt16⟩ := card_sup_zpowers_of_on ht hPt hON hEP hEe hE8
  have hEtC : E ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer ({t} : Set G) :=
    sup_le (hEP.trans hPt) (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  exact hWne (hWv _ hEtC hEte (by rw [hEt16]; norm_num))

theorem l34ONanCoreOfSignalizer_of_catalog
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) :
    L34CoreOfSignalizerAt (fun X _ => IsSporadic X .ONan) := by
  intro G _ _ t P hset hWv
  classical
  obtain ⟨hbase, ht2, hPt, hPp, -, -, hPON⟩ := hset
  have hperf : Group.IsPerfect ↥P := by
    have := CatalogueBAlternating.pComponent_perfect hPp
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPt).toMonoidHom)
      (subgroupOfEquivOfLe hPt).surjective
  have hON := isSporadic_pPrimeCore_of_fusionZStar_on hperf hPON
  exact centralizes_oddIn_of_signalizer hbase.1 hbase.2.1 hbase.2.2.1 hS hU hheld ht2 hPt hPp hON
    (fun E hE hEe hE8 => hWv E hE hEe.isElemAbelian hE8)

theorem l34ONanCoreStepMirror_of_signalizer
    (hS : SchreierFor Blueprint.Catalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple)
    (hS0 : L34SignalizerVanishingAt fun X _ => IsSporadic X .ONan) (hS1 : L34CoreOfSignalizerAt fun X _ => IsSporadic X .ONan) :
    L34ONanCoreStepMirror :=
  l34CoreStepMirrorAt_of_signalizer (fun _ _ h => Or.inr (Or.inl h))
    (fun _ _ _ _ e h => by
      obtain ⟨f⟩ := h
      exact ⟨e.symm.trans f⟩)
    (fun _ _ _ _ h => three_le_pRank_of_sporadic_onan_fusionZStar h) hS hCI hGA h13 hS0 hS1

end CFSG.ComponentClassification.GrSLit.L34Sec5S
