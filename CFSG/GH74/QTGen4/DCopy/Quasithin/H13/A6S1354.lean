module

public import CFSG.Quasithin.H13.A6S1354
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem lemma13_5_4_F4 (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4) (X : Subgroup G)
    (hX₁ : IsHatA6 L → X = oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆) (hX₂ : ¬ IsHatA6 L → X = L₁Of L S.V2) :
    let I₂ := conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G))
    Subgroup.normalizer (S.V2 : Set G) ≤ Subgroup.normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (g1 T V) ∧ I₂ ⊓ Subgroup.centralizer (S.V2 : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pRank 3 (Subgroup.centralizer (S.V2 : Set G)) ≤ 1 ∧
      Subgroup.centralizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      ⁅V, Subgroup.centralizer (S.V3 : Set G)⁆ ≤ fsuV1 T V ∧
      ¬ pCoreOf 2 (g1 T V) ≤ Subgroup.centralizer (S.V2 : Set G) := by
  intro I₂
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9⟩ :=
    h13315 G T L V S.V2 X I₂ S.h13 S.irr S.zv S.isV2 S.not_iso_a5 hX₁ hX₂ rfl
  obtain ⟨h9', h10'⟩ := h9 S.V3 S.V2_le_V3 S.V3_le_V S.T_le_normalizer_V3 S.card_V3
  exact ⟨h1, h2, h3, h4, h5, h8, h9', h10' S.not_lieModel_psu33,
    h13314 G T L V S.V2 S.h13 S.irr S.zv S.isV2 S.not_iso_a5⟩

end Setting4

end CFSG.Quasithin.H13.A6
