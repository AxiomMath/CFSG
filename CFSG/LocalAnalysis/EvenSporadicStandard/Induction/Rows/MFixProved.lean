module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyElem
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MRow

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Monster.Existence CFSG.Monster.Existence.Compat

section Fix

theorem mFixesElem_proved (hmult : OddMultTrivial .M) : MFixesElem := by
  intro H _ _ L K u hcov hPP
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hPP
  have hMf := monsterFacts_of_isSporadic (hcov.isSporadic_of_mult hmult)
  obtain ⟨-, hKeq', hA, -, -⟩ := m_pair_data hMf huL hu2 hKL hKu hcard
  let u' : ↥L := ⟨u, huL⟩
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  let ε : ↥K ≃* ↥(centralizer ({u'} : Set ↥L)) :=
    (Subgroup.subgroupOfEquivOfLe hKL).symm.trans (MulEquiv.subgroupCongr hKeq')
  obtain ⟨hperf, hZ, ⟨e⟩⟩ := hA
  have hZcard : Nat.card ↥(center ↥(centralizer ({u'} : Set ↥L))) = 2 := by
    rw [← Subgroup.card_map_of_injective (centralizer ({u'} : Set ↥L)).subtype_injective, hZ,
      Nat.card_zpowers, hu'2]
  have hinn : ∀ α : MulAut (↥(centralizer ({u'} : Set ↥L)) ⧸
      center ↥(centralizer ({u'} : Set ↥L))), ∃ g, α = MulAut.conj g := by
    have e2 : Nonempty ((↥(centralizer ({u'} : Set ↥L)) ⧸
        center ↥(centralizer ({u'} : Set ↥L))) ≃* NativeSporadic.Carrier .B) := ⟨e⟩
    obtain ⟨e'⟩ := e2
    exact AllInner.of_mulEquiv e'.symm CFSG.RankThree.PartOne.SPOR.allInner_B
  exact fixes_of_mulEquiv ε (involutionFixes_of_cover hperf hZcard.le hinn
    fun s hs1 hs2 => babyElem6_of_equiv e hs1 hs2)

end Fix

end CFSG.EvenSporadicStandard.Induction
