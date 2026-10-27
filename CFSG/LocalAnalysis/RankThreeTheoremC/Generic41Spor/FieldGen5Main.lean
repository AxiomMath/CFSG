module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Classical
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Linear
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Chevalley
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5ChevalleyTw
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Ree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.Blueprint CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Main


theorem fieldAutData_five_of_lieModel {L : Type} [Group L] [Finite L] {t : StatedLieTag}
    {n ℓ f : ℕ} (hM : LieModel L t n ℓ f) (hℓ : ℓ ≠ 5) (hnS : ¬ IsoLie L (.suzuki 2))
    (hcyc : ∀ S : Sylow 5 L, IsCyclic (S : Subgroup L)) : FieldAutData L 5 := by
  rcases hM with ⟨ht, hM⟩ | ⟨-, ht, hM⟩ | ⟨-, ht, hM⟩ | ⟨-, rfl, hM⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fieldAutData_five_psl hM hℓ hcyc
    · exact fieldAutData_five_psu hM hℓ hcyc
    · exact fieldAutData_five_psp hM
    · exact fieldAutData_five_pomega (Or.inl rfl) hM hℓ
    · exact fieldAutData_five_pomega (Or.inr (Or.inl rfl)) hM hℓ
    · exact fieldAutData_five_pomega (Or.inr (Or.inr rfl)) hM hℓ
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fieldAutData_five_chevalley_untwisted (Or.inl rfl) hM hℓ
    · exact fieldAutData_five_chevalley_untwisted (Or.inr (Or.inl rfl)) hM hℓ
    · exact fieldAutData_five_chevalley_untwisted (Or.inr (Or.inr (Or.inl rfl))) hM hℓ
    · exact fieldAutData_five_chevalley_untwisted (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hM hℓ
    · exact fieldAutData_five_chevalley_untwisted (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hM hℓ
    · exact fieldAutData_five_chevalley_twisted (Or.inl rfl) hM hℓ
    · exact fieldAutData_five_chevalley_twisted (Or.inr rfl) hM hℓ
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact fieldAutData_five_reeG2 hM
    · exact fieldAutData_five_reeF4 hM
    · exact fieldAutData_five_tits hM
  · exact fieldAutData_five_suzuki hM hnS

theorem kFactFieldGeneration5_holds : KFactFieldGeneration5 := by
  intro Y _ _ L hLn _ _ _ hC hnS hlie hcyc B x hB hBc hxB hxL hx1 hBL
  obtain ⟨t, n, ℓ, f, hℓ, hM⟩ := hlie
  haveI := hLn
  exact le_iSup_centralizer_of_fieldAutData_of_card hC
    (fieldAutData_five_of_lieModel hM hℓ hnS hcyc) hB hBc hxB hxL hx1 hBL

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
