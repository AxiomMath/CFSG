module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Conf
import CFSG.Adapters.LieModelSimple

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof.X10Lin

theorem isSimpleGroup_of_lieModel_psp4_three {X : Type} [Group X]
    (h : LieModel X .PSp 2 3 1) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem eq_one_of_psp4_three_component {N : Type} [Group N] [Finite N] {τ : StatedLieTag}
    {f : ℕ} (hτ : τ = .PSL ∨ τ = .PSU) (hadm : StatedLieAdmissible τ 4 3 f)
    (hN : LieModel N τ 4 3 f) {β : MulAut N} (hβ2 : β * β = 1) (hβ1 : β ≠ 1)
    {L : Subgroup (fixedSubgroup β)} (hL : IsPComponent 2 L)
    (hX : LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 3 1) : f = 1 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_lin hp2 hτ hadm hN β hβ2 hβ1 L hL
  have hsub : L.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hL
    exact h
  have hZO := GSThmB.X10Rec.center_eq_pPrimeCore hq (isSimpleGroup_of_lieModel_psp4_three hX)
  have hY : LieModel (L ⧸ center L) .PSp 2 3 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO).symm hX
  have hα : orderOf β = 2 := orderOf_eq_prime (by rw [pow_two]; exact hβ2) hβ1
  have hcases : ∃ T : Set (StatedLieTag × ℕ × ℕ), ComponentCases 3 T L ∧
      (∀ {t m e}, (t, m, e) ∈ T → IsClassicalTag t) ∧
      (∀ {e}, (StatedLieTag.PSp, 2, e) ∈ T → (4 = 4 ∧ f = e) ∨ 4 = 5) := by
    rcases hτ with rfl | rfl
    · exact ⟨linTuples 4 f, psl_component_cases hp hp2 hadm hN hα ⟨hq, hsub⟩,
        isClassicalTag_of_mem_linTuples, psp_mem_linTuples⟩
    · exact ⟨linUTuples 4 f, psu_component_cases hp2 hadm hN hα ⟨hq, hsub⟩,
        isClassicalTag_of_mem_linUTuples, psp_mem_linUTuples⟩
  obtain ⟨T, hC, hcl, hpsp⟩ := hcases
  rcases hC with ⟨z, hzL, hzc, hzz, hz1⟩ | ⟨t, m, e, hT, hadm', hm'⟩
  · exact (hz1 (congrArg Subtype.val (X10Sp.eq_one_of_mem_center hZO (z := ⟨z, hzL⟩)
      (mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm) (Subtype.ext hzz)))).elim
  · obtain ⟨rfl, rfl, rfl⟩ := eq_psp4_of_two_lieModels hp hp2 le_rfl (hcl hT) hadm' hm' hY
    rcases hpsp hT with ⟨-, h⟩ | h
    · exact h
    · omega

theorem eq_one_of_conf_lin {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hconf : GSThmB.X11.Conf G N) {τ : StatedLieTag} (hτ : τ = .PSL ∨ τ = .PSU) {f : ℕ}
    (hM : LieModel ↥N τ 4 3 f) : f = 1 := by
  obtain ⟨hNn, hC, -, -, b, -, K, -, hb, -, -, -, -, -, -, -, hKN, hKC, hKp, hKm⟩ := hconf
  have : N.Normal := hNn
  obtain ⟨hβ2, hβ1⟩ := GSThmB.X10Rec.conjNormal_involutive hC hb
  obtain ⟨L, hL, ⟨eL⟩⟩ := GSThmB.X10Rec.fixed_pComponent hKN hKC hKp
  have hadm : StatedLieAdmissible τ 4 3 f := by
    rcases hτ with rfl | rfl
    · obtain ⟨-, hf, -⟩ := GH74.Generic.lieModel_psl_data hM
      exact ⟨Nat.prime_three, hf, by norm_num, by simp, by simp⟩
    · obtain ⟨-, hf, -⟩ := GH74.Generic.lieModel_psu_data hM
      exact ⟨Nat.prime_three, hf, by norm_num, by simp⟩
  exact eq_one_of_psp4_three_component hτ hadm hM hβ2 hβ1 hL
    (LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eL.symm (pPrimeCore_map_iso 2 eL.symm)) hKm)

end CFSG.ComponentClassification.CatLeafProof.X11Char
