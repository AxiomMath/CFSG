module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Step
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ComponentClassification.AS81.Sec3

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.RankTwoSporadic

variable {G : Type} [Group G]

theorem sec3Coords_of
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {A A₁ : Subgroup G} {x : G} (hA₁A : A₁ ≤ A) (hxA : x ∈ A) (hx3 : orderOf x = 3)
    {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hinj : ∀ {a b : G} (ha : a ∈ A) (hb : b ∈ A),
      ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩ → a = b)
    (hx : ∃ t : Kˣ, ψ ⟨x, le_normalizer hxA⟩ = MulAut.conj ⟨torusElt .G2 K g2ir t,
      g2RankOne_le_adjointGroup g2ir (torusElt_mem_g2RankOne g2ir t)⟩)
    (hL1 : ∀ (l : G) (hl : l ∈ A₁), ψ ⟨l, le_normalizer (hA₁A hl)⟩ ∈ g2Inn K (g2LongA2 K))
    (hL2 : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2LongA2 K →
      ∃ (l : G) (hl : l ∈ A₁), ψ ⟨l, le_normalizer (hA₁A hl)⟩ = MulAut.conj y) :
    Sec3Coords A A₁ x := by
  have hconj : Function.Injective
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) :=
    RankTwoHypIIY.conj_injective_of_center_eq_bot LieType.Chevalley.center_adjointGroup_eq_bot
  set e := MonoidHom.ofInjective hconj
  set ψA : ↥A →* ↥(MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range :=
    (ψ.comp (inclusion le_normalizer)).codRestrict _ (fun a => hψ.map_mem a.1 a.2)
  set f : ↥A →* ↥(adjointGroup .G2 K) := e.symm.toMonoidHom.comp ψA
  have hf : ∀ a : ↥A, MulAut.conj (f a) = ψ ⟨a, le_normalizer a.2⟩ := by
    intro a
    have h1 : e (f a) = ψA a := by
      show e (e.symm (ψA a)) = ψA a
      exact e.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 := hf a
    rw [hab, hf b] at h1
    exact Subtype.ext (hinj a.2 b.2 h1.symm)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, hay⟩ := hψ.exists_eq _ ⟨y, rfl⟩
    refine ⟨⟨a, ha⟩, hconj ?_⟩
    rw [hf]
    exact hay
  let φ : ↥A ≃* ↥(adjointGroup .G2 K) := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hφ : ∀ a : ↥A, MulAut.conj (φ a) = ψ ⟨a, le_normalizer a.2⟩ := hf
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, φ, ?_, ?_⟩
  ·
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := hL1 a (mem_subgroupOf.mp ha)
      rw [← hφ a] at h1
      exact mem_subgroupOf.mpr (coe_mem_of_conj_mem_g2Inn h1)
    · intro hy
      obtain ⟨l, hl, hly⟩ := hL2 y (mem_subgroupOf.mp hy)
      refine ⟨⟨l, hA₁A hl⟩, mem_subgroupOf.mpr hl, hconj ?_⟩
      rw [MulEquiv.coe_toMonoidHom, hφ]
      exact hly
  ·
    obtain ⟨t, ht⟩ := hx
    have hφx : φ ⟨x, hxA⟩ = ⟨torusElt .G2 K g2ir t,
        g2RankOne_le_adjointGroup g2ir (torusElt_mem_g2RankOne g2ir t)⟩ :=
      hconj ((hφ _).trans ht)
    have hz : ((zpowers x).subgroupOf A).map φ.toMonoidHom = zpowers (φ ⟨x, hxA⟩) := by
      have : (zpowers x).subgroupOf A = zpowers (⟨x, hxA⟩ : ↥A) := by
        ext a
        rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk)⟩
        · rintro ⟨k, hk⟩
          exact ⟨k, by rw [← hk, SubgroupClass.coe_zpow]⟩
      rw [this, MonoidHom.map_zpowers]
      rfl
    rw [hz]
    have hle : zpowers (φ ⟨x, hxA⟩) ≤ (g2TorusR K).subgroupOf (adjointGroup .G2 K) := by
      rw [zpowers_le, hφx, mem_subgroupOf]
      exact ⟨t, rfl⟩
    refine eq_of_le_of_card_ge hle ?_
    have h3 : Nat.card (zpowers (φ ⟨x, hxA⟩)) = 3 := by
      rw [Nat.card_zpowers, MulEquiv.orderOf_eq φ, Subgroup.orderOf_mk, hx3]
    have hHC : g2TorusR K ≤ adjointGroup .G2 K := by
      rintro _ ⟨s, rfl⟩
      exact g2RankOne_le_adjointGroup g2ir (torusElt_mem_g2RankOne g2ir s)
    rw [h3, Nat.card_congr (subgroupOfEquivOfLe hHC).toEquiv]
    calc Nat.card (g2TorusR K) ≤ Nat.card Kˣ :=
        Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
      _ = 3 := by rw [Nat.card_units, hK]

end CFSG.ComponentClassification.AS81.Sec3
