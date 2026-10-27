module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem10
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open Lem10

theorem stmt12_2_10_of_F4 (h1222 : Stmt12_2_2_F4) (hOut : Out1222Fact) (hEnd : End1222Fact) :
    Stmt12_2_10_F4 := by
  intro G _ _ T L V h
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.sylow
  obtain ⟨-, -, hall⟩ := ((h1222 G T h.simple h.nonabelian h.qtke h.sylow).resolve_left
    h.notAlt) L h.maximal h.faithful h.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hcomm, hmod⟩ := hall V h.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.irrPlus.2.2.1
  have hc : ⁅V, L⁆ = V := h.irrPlus.2.2.2.1
  have hirr := h.irrPlus.2.2.2.2.2.1
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have := hred.2.1
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
    have hE : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      (sup_le Subgroup.le_normalizer h.normalizes).trans
        (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Subgroup.map_subtype_le _).trans le_sup_left) hE
        (LieType.BorelTits.pCoreOf_isPGroup 2 L)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    have hy' : y ∈ CFSG.pCore 2 ↥(L ⊔ T) := by rwa [CFSG.pCore_eq_open]
    have hyc := pCore_le_centralizer_of_isPrimeReduced hred hy'
    rw [Subgroup.mem_centralizer_iff] at hyc ⊢
    intro v hv
    exact congrArg Subtype.val (hyc ⟨v, hVLT hv⟩ hv)
  have hLM : L ≤ h.MV := le_inf Subgroup.le_normalizer hLV
  have hTM : T ≤ h.MV := le_inf h.normalizes hTV
  have hLb : autOn L V ≤ h.MVbar := A4.autOn_mono hLM
  have hTb : autOn T V ≤ h.MVbar := A4.autOn_mono hTM

  have h1 : h.MVbar ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) =
      autOn L V ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) := by
    refine le_antisymm (fun x hx => ⟨?_, hx.2⟩) (inf_le_inf_right _ hLb)
    refine hEnd G L V hV2 hLV hc hirr hO2 hmod x fun y hy => ?_
    exact ((Subgroup.mem_centralizer_iff.mp hx.2) y hy).symm

  have hMN : h.MVbar ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    Lem10.autOn_le_normalizer_autOn_of_le inf_le_left
  have hLperf : autOn L V = oTwoUpper (autOn L V) := by
    rw [A4.oTwoUpper_autOn hLV,
      ← eq_oTwoUpper_of_perfect (perfect_of_mem_cComp h.faithful.1.2.1)]
  have h2 : oTwoUpper h.MVbar = autOn L V := by
    refine le_antisymm (oTwoUpper_le_of_pow_mem fun x hx => ?_)
      (hLperf ▸ oTwoUpper_mono hLb)
    obtain ⟨k, hk⟩ := hOut G L V hV2 hLV hc hirr hO2 hmod x (hMN hx)
    refine ⟨k, ?_⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (autOn L V)
      (Subgroup.centralizer (autOn L V : Set (MulAut ↥V)))
      (Subgroup.centralizer_le_normalizer _)] at hk
    obtain ⟨l, hl, c, hc', hlc⟩ := hk
    have hcM : c ∈ h.MVbar := by
      have : c = l⁻¹ * x ^ 2 ^ k := by rw [← hlc]; group
      rw [this]
      exact h.MVbar.mul_mem (h.MVbar.inv_mem (hLb hl)) (h.MVbar.pow_mem hx _)
    have hcL : c ∈ autOn L V := ((h1 ▸ ⟨hcM, hc'⟩ :
      c ∈ autOn L V ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)))).1
    rw [← hlc]
    exact (autOn L V).mul_mem hl hcL

  have hsup : oTwoUpper h.MV ⊔ T = h.MV := by
    have hSM : (S : Subgroup G) ≤ h.MV := hS ▸ hTM
    have := A7.eq_oTwoUpper_sup_sylow (H := h.MV) S hSM
    rwa [hS] at this
  have hMVN : h.MV ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  refine ⟨h1, h2, ?_⟩
  calc h.MVbar = autOn (oTwoUpper h.MV ⊔ T) V := by rw [hsup]
    _ = autOn (oTwoUpper h.MV) V ⊔ autOn T V := by
      unfold autOn
      rw [Subgroup.subgroupOf_sup ((oTwoUpper_le _).trans hMVN) (hTM.trans hMVN),
        Subgroup.map_sup]
    _ = autOn L V ⊔ autOn T V := by rw [← A4.oTwoUpper_autOn hMVN, h2]

end CFSG.Quasithin.H13
