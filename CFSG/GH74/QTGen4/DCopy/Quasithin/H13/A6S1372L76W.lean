module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenTilde
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_quotEquiv_tilde_F4 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  let κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : Function.Surjective κ := by
    intro x
    obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 x.2
    exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩
  have hker : κ.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, mem_pCore_iff, ← GoldS146R.inf_pCoreOf_eq_of_mem_cComp hK,
      Subgroup.mem_inf, and_iff_right k.2, S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH (hKH k.2)]
    exact Subtype.ext_iff.trans (A6Mod.secAct_eq_one_iff hHU hHV ⟨k, hKH k.2⟩)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective κ hκ)⟩

theorem exists_quotEquiv_of_realizes_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G}
    (hK : K ∈ cComp H) {D : FFModel} (hD : D.Faithful)
    {U Z : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hR : D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) U Z) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* D.Gam) := by
  obtain ⟨e₀⟩ := S.exists_quotEquiv_tilde_F4 hNS h13315 h1356two hH hK
  obtain ⟨π, hπ⟩ := hR
  exact ⟨e₀.trans (MulEquiv.ofBijective π ⟨FFC.injective_of_faithful_sec hD hπ, hπ.1⟩).symm⟩

end Setting4

end CFSG.Quasithin.H13.A6
