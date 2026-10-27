module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Plus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem exists_quaternion_quotient_of_le [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y) {u : G}
    (hu : IsI4PlusIn X u) :
    ∃ huY : u ∈ Y, ∃ f : QuaternionGroup 2 →* ↥Y ⧸ oddCore ↥Y, Function.Injective f ∧
      f (QuaternionGroup.a 2) = QuotientGroup.mk (⟨u, huY⟩ : ↥Y) := by
  obtain ⟨hord, K, huK, hKle, -, hKSL⟩ := hu
  obtain ⟨f, hf, hfu, hfK⟩ := exists_quaternion_of_isSL23Mod hKSL huK hord
  have hfY : f.range ≤ Y := hfK.trans (hKle.trans (inf_le_left.trans hXY))
  have huY : u ∈ Y := hfu ▸ hfY ⟨QuaternionGroup.a 2, rfl⟩
  obtain ⟨f', hf', hf'mk⟩ := exists_injective_quotient_oddCore hf hfY
  refine ⟨huY, f', hf', ?_⟩
  rw [hf'mk]
  congr 1
  exact Subtype.ext hfu

theorem isI4PlusIn_of_le_of_lieModel_plus [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y)
    (hY : LieModel (↥Y ⧸ oddCore ↥Y) .POmegaPlus 4 3 1) {u : G} (hu : IsI4PlusIn X u) :
    IsI4PlusIn Y u := by
  obtain ⟨huY, f, hf, hfu⟩ := exists_quaternion_quotient_of_le hXY hu
  have h := asc82Omega8PlusPocket_holds _ hY f hf
  rw [hfu] at h
  have hord : orderOf (⟨u, huY⟩ : ↥Y) = 2 := (Subgroup.orderOf_mk u huY).trans hu.1
  exact isI4PlusIn_of_top huY (isI4PlusIn_top_of_quotient hord h)

theorem asc82OmegaPlusPocketLift_holds : Asc82OmegaPlusPocketLift := by
  intro G _ _ Y hY a _ _ X hX u hu
  exact isI4PlusIn_of_le_of_lieModel_plus (hX.1.trans inf_le_left) hY.2 hu

end CFSG.OddStandard.SmallF3.Omega
