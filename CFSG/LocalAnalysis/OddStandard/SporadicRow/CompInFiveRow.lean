module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.SL25Component
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.CompInFive

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.HardMathSupport.Foote.FamilyReduction

theorem center_ne_bot_of_selfCent_mem {S : Type*} [Group S] {t : S} (ht : orderOf t = 2)
    {B : Subgroup ↥(centralizer ({t} : Set S))} (htB : selfCent t ∈ B) : center ↥B ≠ ⊥ := by
  intro hZ
  have hc : (⟨selfCent t, htB⟩ : ↥B) ∈ center ↥B := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 (g : ↥(centralizer ({t} : Set S))).2
  rw [hZ, mem_bot] at hc
  have h1 : t = 1 := congrArg (fun x : ↥B => ((x : ↥(centralizer ({t} : Set S))) : S)) hc
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem not_oddLieOrder_of_not_compIn5 {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x) (hS : ¬ CompIn5 S) {t : S}
    (ht : orderOf t = 2) {B : Subgroup ↥(centralizer ({t} : Set S))} (hB : IsComponent B)
    (htB : selfCent t ∈ B) {a : ℕ} (hd : Nat.card ↥B ∣ 2 ^ a * 15) :
    ¬ OddLieOrder (Nat.card (↥B ⧸ center ↥B)) := fun hodd => by
  obtain ⟨eB⟩ := nonempty_mulEquiv_sl2_five_of_oddLieOrder hB.1 hd
    (center_ne_bot_of_selfCent_mem ht htB) hodd
  exact hS (compIn5_of_isComponent_sl2_five hna ht hB htB eB)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
