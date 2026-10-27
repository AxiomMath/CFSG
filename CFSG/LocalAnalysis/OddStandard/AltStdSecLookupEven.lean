module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupOdd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
  CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem fixed_lookup_evenLie (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S)
    {σ : MulAut S} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) {B : Subgroup (fixedSubgroup σ)}
    (hB : IsComponent B) (hAlt : IsLargeAlt B) :
    ∃ N : ℕ, Nonempty (S ≃* alternatingGroup (Fin N)) := by
  have hσ2' : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  obtain ⟨m, hm, ⟨e⟩⟩ := hAlt
  have hdvd := dvd_card_of_isLargeAlt (Y := B) ⟨m, hm, ⟨e⟩⟩
  have hBS : Nat.card B ∣ Nat.card S := lookup_card_dvd_of_fixed B
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · have ht2 := lookup_orderOf_eq_two_of_conj hna hσ2 hσ1 ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      obtain ⟨B', hB', -⟩ := isComponent_map_fixedSubgroup_conj ht hB
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 B' hB'
    · rcases hU with hodd | ⟨n, -, h7, ⟨eA⟩⟩ | hL | hH
      · exact absurd ⟨m, hm, ⟨e⟩⟩ (not_largeAlt_of_oddLieType hGLS hO hodd hσ2' hB)
      · exact ⟨n, ⟨eA⟩⟩
      · exfalso
        have hadm : StatedLieAdmissible .PSL 3 2 2 :=
          ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
        obtain ⟨-, hord, -⟩ := hO S .PSL 3 2 2 hadm hL
        have h1 : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide
        have h2 : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by decide
        rw [h1, h2] at hord
        have hS : Nat.card S = 20160 := by omega
        rw [hS] at hBS
        exact absurd (hdvd.trans hBS) (by norm_num)
      · exfalso
        obtain ⟨eH⟩ := hH
        have hS : Nat.card S = 4030387200 := by
          rw [Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
        rw [hS] at hBS
        exact absurd (hdvd.trans hBS) (by norm_num)
  · exfalso
    obtain ⟨τ, n, f, hadm, hmod⟩ := heven
    have hPc : IsPComponent 2 B :=
      LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hB
    have : IsSimpleGroup (alternatingGroup (Fin m)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hPc e
    rcases hEO S τ n f hadm hmod σ hσ2' hout B hPc with ⟨τ', n', f', hadm', hmod'⟩ | hA | hU
    · exact false_of_lieModel_alt hO hm eZ hadm' hmod'
    · obtain ⟨eA⟩ := hA
      have h1 := card_eq_of_equiv_alt (Y := alternatingGroup (Fin m)) (m := 6) (by norm_num)
        (eZ.symm.trans eA)
      have h2 := dvd_card_of_isLargeAlt (Y := alternatingGroup (Fin m))
        ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
      rw [h1] at h2
      exact absurd h2 (by norm_num [Nat.factorial])
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      exact false_of_lieModel_alt hO hm eZ hadm3 hU

end CFSG.OddStandard.AltStdSec
