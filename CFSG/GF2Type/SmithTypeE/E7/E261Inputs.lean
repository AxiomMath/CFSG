module

public import CFSG.GF2Type.SmithTypeE.E7.E261
public import CFSG.GF2Type.SmithTypeE.E7.CompatOf
public import CFSG.GF2Type.SmithTypeE.E7.ModCert
public import CFSG.GF2Type.SmithTypeE.E7.E23FourCert
public import CFSG.GF2Type.SmithTypeE.E7.Fusion
public import CFSG.GF2Type.SmithTypeE.E7.UwInput

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)

theorem smithE7_steps_of_inputs (hTI : WeaklyClosedTITransitive.{0}) (I : Inputs10)
    (hAS : AschbacherSmithWideInput)
    (hrank : ∀ E : Subgroup ↥DMod.TD6, CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15) :
    SmithE7Compat ∧ SmithE7E33 ∧ SmithE7E34a ∧ SmithE7E34b ∧ SmithE7E25 ∧ SmithE7LocalInput := by
  have hrankS : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
      S.width = 16 → Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) → TwoRankMbar S :=
    fun _ _ _ _ _ _ hO => twoRankMbar_of_TD6 hO hrank
  have hC : SmithE7Compat := smithE7Compat_of hTI I hAS uwInput hrankS
  have hM : SmithE7Module := smithE7Module_of_model (smithE7Model_of_compat hC)
  have h33 : SmithE7E33 := smithE7E33_of hTI I hAS hrankS
  obtain ⟨h34a, h34b⟩ := smithE7E34_of h33 (smithE7E34Q_of_module hM)
  have h24 := smithE7E24_of_module hM
  have h25 := smithE7E25_of_module hM
  have h23 := smithE7E23_of_module hM
  have h23f := smithE7E23Four_of_model (smithE7Model_of_compat hC) h33 h34a h34b h24
  exact ⟨hC, h33, h34a, h34b, h25, smithE7LocalInput_of h34a h34b h23 h24 h25 h23f⟩

theorem smithE7E261_of_inputs (hTI : WeaklyClosedTITransitive.{0}) (I : Inputs10)
    (hAS : AschbacherSmithWideInput)
    (hrank : ∀ E : Subgroup ↥DMod.TD6, CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15) :
    SmithE7E261 := by
  obtain ⟨hC, h33, h34a, h34b, h25, hLoc⟩ := smithE7_steps_of_inputs hTI I hAS hrank
  exact smithE7E261_of h34a h34b hLoc (smithE7E23a_of h25 h34a h34b hLoc hC) hC h33
    e23FourFacts7

end CFSG.GF2Type.SmithTypeE.E7
