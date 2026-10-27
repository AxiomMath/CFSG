module

public import CFSG.GF2Type.SmithTypeE.E7.GH74
public import CFSG.GF2Type.SmithTypeE.E7.E261Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup CFSG CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

theorem partC_of_gh74_e261 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models)
    (hTI : WeaklyClosedTITransitive.{0})
    (hrank : ∀ E : Subgroup ↥DMod.TD6, CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15)
    (h261 : E7.SmithE7E261) : PartC := by
  obtain ⟨hAS, -, -, I⟩ := smithTypeEInputs_of_gh74 hgh
  have hrankS : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
      S.width = 16 → Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) → E7.TwoRankMbar S :=
    fun _ _ _ _ _ _ hO => E7.twoRankMbar_of_TD6 hO hrank
  have hModel := E7.smithE7Model_of_compat (E7.smithE7Compat_of hTI I hAS E7.uwInput hrankS)
  have hMod := E7.smithE7Module_of_model hModel
  have h33 := E7.smithE7E33_of hTI I hAS hrankS
  have h34Q := E7.smithE7E34Q_of_module hMod
  obtain ⟨h34a, h34b⟩ := E7.smithE7E34_of h33 h34Q
  have h24 := E7.smithE7E24_of_module hMod
  exact partC_of_chain_gh74 hgh h33 h34Q (E7.smithE7E23_of_module hMod) h24
    (E7.smithE7E24Line_of_module hMod) (E7.smithE7E25_of_module hMod)
    (E7.smithE7E23Four_of_model hModel h33 h34a h34b h24) h261

theorem partC_of_gh74 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models)
    (hTI : WeaklyClosedTITransitive.{0})
    (hrank : ∀ E : Subgroup ↥DMod.TD6, CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15) :
    PartC := by
  obtain ⟨hAS, -, -, I⟩ := smithTypeEInputs_of_gh74 hgh
  exact partC_of_gh74_e261 hgh hTI hrank (E7.smithE7E261_of_inputs hTI I hAS hrank)

theorem partC_of_gh74_only (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) : PartC :=
  partC_of_gh74 hgh
    (TI75.weaklyClosedTITransitive_of_inputs
      (TI75Bridge.simpleCaseStmt_of_rest ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩)
      CFSG.CGT.Timmesfeld75.lemma215)
    fun E hE => E7.card_le_of_isElementaryAbelian_TD6 E hE

open CFSG.GF2Type.SmithTypeE.E7 in
theorem smithE7Input_of_gh74_only (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) :
    SmithE7Input := by
  have hTI : WeaklyClosedTITransitive.{0} :=
    TI75.weaklyClosedTITransitive_of_inputs
      (TI75Bridge.simpleCaseStmt_of_rest ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩)
      CFSG.CGT.Timmesfeld75.lemma215
  obtain ⟨hAS, hDW, hHolt, I⟩ := smithTypeEInputs_of_gh74 hgh
  have hrank : ∀ E : Subgroup ↥DMod.TD6, CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15 :=
    fun E hE => E7.card_le_of_isElementaryAbelian_TD6 E hE
  have hrankS : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
      S.width = 16 → Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) → E7.TwoRankMbar S :=
    fun _ _ _ _ _ _ hO => E7.twoRankMbar_of_TD6 hO hrank
  have hModel := E7.smithE7Model_of_compat (E7.smithE7Compat_of hTI I hAS E7.uwInput hrankS)
  have hMod := E7.smithE7Module_of_model hModel
  have h33 := E7.smithE7E33_of hTI I hAS hrankS
  have h34Q := E7.smithE7E34Q_of_module hMod
  obtain ⟨h34a, h34b⟩ := E7.smithE7E34_of h33 h34Q
  have h24 := E7.smithE7E24_of_module hMod
  have h23 := E7.smithE7E23_of_module hMod
  have h25 := E7.smithE7E25_of_module hMod
  have h23f := E7.smithE7E23Four_of_model hModel h33 h34a h34b h24
  exact smithE7Input_of_threeFour (smithE7ThreeFourInput_of hAS hDW hHolt
    (smithE7LocalInput_of h34a h34b h23 h24 h25 h23f)
    (smithE7PathInput_of h34a h34b h23 h24 h25 h23f (E7.smithE7E24Line_of_module hMod)
      (smithE7E421Three_of h34a (E7.smithE7E261_of_inputs hTI I hAS hrank))))

end CFSG.GF2Type.SmithTypeE
