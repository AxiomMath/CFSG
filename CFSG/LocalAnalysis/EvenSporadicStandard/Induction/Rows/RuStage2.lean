module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Part12
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThree
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseM10
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveRuP
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuTwoBRuP
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
  CFSG.EvenSporadicStandard.RuStd.S2

theorem factorization_two_ruOrder : (145926144000 : ℕ).factorization 2 = 14 := by
  have h : (145926144000 : ℕ) = 2 ^ 14 * 8906625 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Components

variable {H : Type} [Group H] [Finite H]

theorem ru_comp_unique {X M₁ M₂ : Subgroup H} (h₁ : IsCompIn M₁ X) (h₂ : IsCompIn M₂ X)
    (hs₂ : IsSporadic ↥M₂ .Ru)
    (hC : ∀ P : Sylow 2 (centralizer (M₁ : Set H)), Nat.card P = 2) : M₁ = M₂ := by
  by_contra hne
  have hcomm := h₁.commute_of_ne h₂ hne
  have hle : M₂ ≤ centralizer (M₁ : Set H) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
  have h1 := twoAdic_mono hle
  have hcard : Nat.card ↥M₂ = 145926144000 := (ruFacts_of_isSporadic hs₂).card_eq
  have hP : twoAdic (centralizer (M₁ : Set H)) = 1 := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer (M₁ : Set H))) := inferInstance
    have h := hC P
    rw [Sylow.card_eq_multiplicity] at h
    have : 2 ^ (Nat.card ↥(centralizer (M₁ : Set H))).factorization 2 = 2 ^ 1 := by
      rw [pow_one]; exact h
    exact Nat.pow_right_injective (le_refl 2) this
  unfold twoAdic at h1 hP
  rw [hcard, factorization_two_ruOrder] at h1
  omega

end Components

theorem isKGroupCat_centralizer_of_fStarSimple {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (hN : FStarSimple N) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {y : ↥N}
    (hy : y ≠ 1) : CFSG.SectionRank.IsKGroupCat ↥(centralizer ({y} : Set ↥N)) := by
  have := hN.isSimpleGroup
  have hkpN : CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥N :=
    CFSG.KCore.KProperNonab.subgroup CFSG.SectionRank.catalog_isoInvariant hkp N
  refine CFSG.QuasithinUnique.isKGroupCat_of_kProper hkpN fun htop => hy ?_
  have hyc : y ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({y} : Set ↥N) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.1 hg
  have hcen : center ↥N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥N) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hN.nonabelian
      exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)
  rwa [hcen, mem_bot] at hyc

theorem ruStage2_of_configs
    (hGH1 : GHLemma53_1) (hOut : OutU43TwoGroup) {G : Type} [Group G] [Finite G]
    (hKG : ∀ y : G, y ≠ 1 → CFSG.SectionRank.IsKGroupCat ↥(centralizer ({y} : Set G)))
    {L L₁ : Subgroup G} {z : G} (hz : Config G L z) (hRu : IsSporadic ↥L .Ru)
    (u : ↥L) (hu2 : orderOf u = 2) (hcard : Nat.card ↥(centralizer ({u} : Set ↥L)) = 116480)
    (hRu₁ : IsSporadic ↥L₁ .Ru) (hK : kComponent L u ≤ L₁) (hc₁ : Config G L₁ (u : G)) :
    False := by
  have hRF : RuFacts L := ruFacts_of_isSporadic hRu
  have h2B : RuTwoBFacts L := ruTwoBFacts_of_isSporadic hRu
  have h5L : RuFiveFacts L := ruFiveFacts_of_isSporadic hRu
  have h5L₁ : RuFiveFacts L₁ := ruFiveFacts_of_isSporadic hRu₁
  have h3 : RuThreeFacts L := ruThreeFacts_of_isSporadic hRu
  have hu2' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
  obtain ⟨d⟩ := partThreeData_of_stage2' hz hc₁ u.2 hu2' hcard hK h2B h5L h5L₁
  have hr1 : d.r ≠ 1 := fun h => by
    have := d.r_ord
    rw [h, orderOf_one] at this
    omega
  obtain ⟨dd⟩ := threeLocalData_of_partThree center_M10_eq_bot hRF h3 h5L d
  exact closing_abstract_cert hGH1 hOut (hKG d.r hr1) dd

@[expose] def RuNoOther : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), FStarSimple N →
    N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Ru L →
    RuPair H L K u → SolStd L → (∃ P : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥P) →
    (∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) → t ∈ centralizer (L : Set H) →
    orderOf t = 2 → BTheoremAt u → ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      K ≤ M ⊔ CFSG.conjugate M t → M ≠ K → (∃ s' ∈ [TauCeti.SporadicName.Ru], OddCover s' M) →
      (∀ P : Sylow 2 (centralizer (M : Set H)), Nat.card P = 2) → False

@[expose] def RuNoOtherAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), FStarSimple N →
    N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Ru L →
    RuPair H L K u → SolStd L → (∃ P : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥P) →
    (∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) → t ∈ centralizer (L : Set H) →
    orderOf t = 2 → BTheoremAt u → ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      K ≤ M ⊔ CFSG.conjugate M t → M ≠ K → (∃ s' ∈ [TauCeti.SporadicName.Ru], OddCover s' M) →
      (∀ P : Sylow 2 (centralizer (M : Set H)), Nat.card P = 2) → False

@[expose] def RuNoOtherHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → RuNoOtherAt H

end CFSG.EvenSporadicStandard.Induction
