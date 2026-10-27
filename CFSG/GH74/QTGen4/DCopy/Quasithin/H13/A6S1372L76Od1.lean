module

public import CFSG.Quasithin.H13.A6S1372L76Od1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1355
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13812

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Tilde

variable {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
  {K : Subgroup G} (hK : K ∈ cComp H)
  {Kt : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))}
  (hKt : Kt = autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
  {X : Subgroup G} (hXH : X ≤ H)
include hH hK hKt

theorem false_of_trivial_on_UK_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4)
    (hXn : ∀ x (hx : x ∈ X), ∀ y ∈ Kt, A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩ * y * (A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
        (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩)⁻¹ ∈ Kt)
    (hV3 : S.V3 ≤ ⁅S.V3, X⁆)
    (hfaith : ∀ y ∈ Kt, (∀ u ∈ commV Kt, y u * u⁻¹ ∈ fixV Kt) → y = 1)
    (hX : ∀ x (hx : x ∈ X), ∀ u ∈ commV Kt, A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) ⟨x, hXH hx⟩ u * u⁻¹ ∈ fixV Kt) : False := by
  have hKG : K ≤ S.G1 := (le_of_mem_cComp hK).trans hH.2.1
  have hKC := le_centralizer_V3_of_mem_V1 (perfect_of_mem_cComp hK) hKG
    (conj_mem_V1_of_trivial hH hK hKt hXH hXn hV3 hfaith hX)
  exact (S.lem13812_one_F4 h139 h37 h38 hH hK).1
    (hKC.trans ((S.centralizer_V3_le_F4 h13315).trans S.NV_le_M))

end Tilde

end Setting4

end CFSG.Quasithin.H13.A6
