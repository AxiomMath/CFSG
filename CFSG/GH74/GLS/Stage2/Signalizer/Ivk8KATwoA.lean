module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAOdd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotTools
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Bender
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.Timmesfeld.Orders.Classical
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem oddCoreAut_of_fitting {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a)
    (hY : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup (CFSG.generalizedFitting X)],
      (∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting X ≃* Y) → ∀ t : X, orderOf t = 2 →
        CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥) : OddCoreAut Y := by
  intro X _ _ S _ hSY hC t ht
  obtain ⟨ψ⟩ := hSY
  have hSs : IsSimpleGroup S := by
    have := hs
    exact MulEquiv.isSimpleGroup ψ
  have hSna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨ψ.symm a, ψ.symm b, fun h => hab (by simpa using congrArg ψ h)⟩
  have hF : CFSG.generalizedFitting X = S :=
    Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot S
      hSna hC
  have : IsSimpleGroup (CFSG.generalizedFitting X) := by rw [hF]; exact hSs
  refine hY X ?_ ⟨(MulEquiv.subgroupCongr hF).trans ψ⟩ t ht
  obtain ⟨a, b, hab⟩ := hSna
  refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b, fun h => hab ?_⟩
  simpa using congrArg (MulEquiv.subgroupCongr hF) h

theorem kaAll_of_oddCore_outer_le_four {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) (hY : OddCoreAut Y) (hc4 : Nat.card (Outer Y) ≤ 4)
    {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  have hfin : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  have hOfin : Finite (Outer Y) := inferInstance
  exact kaAll_of_oddCore_aut hs hna hY (kaOutCyc_of_card_outer_le_four hc4)
    (outAbelian_of_outer_comm
      (CFSG.ComponentClassification.CatalogueSchreierAlternating.commutative_of_card_le_four hc4))
    hα2 hα1

theorem oddCoreAut_linear_two {Y : Type} [Group Y] [Finite Y]
    (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a) {f : ℕ} (hf : 3 ≤ f)
    (h : LieModel Y .PSL 2 2 f) : OddCoreAut Y := by
  refine oddCoreAut_of_fitting hs hna fun X _ _ _ hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  have hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSL 2 2 f :=
    LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
  obtain ⟨-, hiff, -⟩ :=
    ComponentClassification.UnbalancedCatalog.even_linear_two_almost_simple_unbalanced_outcome
      hnonab hmodel
  by_contra hne
  have := ((hiff t ht).mp hne).1
  omega

theorem oddCoreAut_unitary_three_four {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) (h : LieModel Y .PSU 3 2 2) : OddCoreAut Y := by
  refine oddCoreAut_of_fitting hs hna fun X _ _ _ hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  have hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSU 3 2 2 :=
    LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
  exact (ComponentClassification.UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing
    hnonab hmodel).2 t ht

theorem suzukiModel_of_lieModel {Y : Type} [Group Y] (h : LieModel Y .twistedB2 0 2 3) :
    SuzukiModel Y 2 3 :=
  (CFSG.Blueprint.LieModel.suzukiModel h).2

theorem oddCoreAut_suzuki_eight {Y : Type} [Group Y] [Finite Y]
    (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a) (h : LieModel Y .twistedB2 0 2 3) :
    OddCoreAut Y := by
  refine oddCoreAut_of_fitting hs hna fun X _ _ hsF hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  have hSz : SuzukiModel Y 2 3 := suzukiModel_of_lieModel h
  have hSzF : SuzukiModel (CFSG.generalizedFitting X) 2 3 := by
    obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := hSz
    exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.trans e'⟩⟩
  exact (ComponentClassification.UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing
    hsF hnonab hSzF t ht).2.2

theorem kaAll_of_linear_two
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y) {f : ℕ} (hf3 : 3 ≤ f) (hf4 : f ≤ 4)
    (h : LieModel Y .PSL 2 2 f) {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := Y) (f := f) (by omega) h
  have hB : BenderType Y f 1 1 := .linear f (by omega) e
  have hc : Nat.card Y = (2 ^ f + 1) * (2 ^ f * (2 ^ f - 1)) := by
    simpa using hB.card_eq
  have hna : ∃ a b : Y, a * b ≠ b * a := by
    refine exists_noncomm_of_simple_of_not_prime hs ?_
    rw [hc]
    interval_cases f <;> norm_num
  have hout : Nat.card (Outer Y) ≤ 4 := by rw [hB.outer_linear.2]; exact hf4
  exact kaAll_of_oddCore_outer_le_four hs hna (oddCoreAut_linear_two hs hna hf3 h) hout hα2 hα1

theorem kaAll_of_Sz8 {Y : Type} [Group Y] [Finite Y]
    (hs : IsSimpleGroup Y) (h : LieModel Y .twistedB2 0 2 3) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.Proofs2.ivk93m12_szModel_equiv (suzukiModel_of_lieModel h)
  have hB : BenderType Y (2 * 1 + 1) 2 1 := .suzuki 1 le_rfl e
  have hc : Nat.card Y = 29120 := by
    have := hB.card_eq
    norm_num at this
    exact this
  have hna : ∃ a b : Y, a * b ≠ b * a :=
    exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num)
  have hout : Nat.card (Outer Y) ≤ 4 :=
    (Nat.le_of_dvd (by norm_num) hB.outer_suzuki.2.1).trans (by norm_num)
  exact kaAll_of_oddCore_outer_le_four hs hna (oddCoreAut_suzuki_eight hs hna h) hout hα2 hα1

theorem kaAll_of_U34 {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (h : LieModel Y .PSU 3 2 2) {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := KGroups.equiv_psu3_of_lieModel_even (S := Y) (f := 2) le_rfl h
  have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [CFSG.Theory.Comparator.PSU3Model, CFSG.Open.PSU3]
  have hB := BenderType.unitary 2 le_rfl (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  have hc : Nat.card Y = 62400 := by
    have hst : StatedClassicalModel Y .PSU 3 2 2 := by
      rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · exact h
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hst).2.1 rfl
    rw [h1]
    decide
  have hna : ∃ a b : Y, a * b ≠ b * a :=
    exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num)
  have hout : Nat.card (Outer Y) ≤ 4 := by
    obtain ⟨Dd, hn, -, hDcard, -, hqcard⟩ := hB.outer_unitary
    have h1 := Dd.card_eq_card_quotient_mul_card_subgroup
    rw [hqcard, hDcard] at h1
    norm_num at h1
    omega
  exact kaAll_of_oddCore_outer_le_four hs hna (oddCoreAut_unitary_three_four hs hna h) hout hα2 hα1

theorem kay_TwoBender :
    KAY CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.FTwoNL34 := by
  refine kay_of_kaAll ?_
  intro Y _ _ hF hs α hα2 hα1
  rcases hF with h | h | h | h
  · exact kaAll_of_linear_two hs (f := 3) le_rfl (by norm_num) h hα2 hα1
  · exact kaAll_of_linear_two hs (f := 4) (by norm_num) le_rfl h hα2 hα1
  · exact kaAll_of_U34 hs h hα2 hα1
  · exact kaAll_of_Sz8 hs h hα2 hα1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
