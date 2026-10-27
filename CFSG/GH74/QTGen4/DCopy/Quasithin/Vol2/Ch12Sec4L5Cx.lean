module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Cx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Lemma5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem Cx5Facts.of_F4 (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
    (hcx : Cx1242 G T L V)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :
    ∃ z : G, Cx5Facts G T L V z := by
  have hyp := hcx.hyp
  have h9 := card_quot_of_sl_five h5
  have hcard : Nat.card V = 2 ^ 10 := by
    rcases hcx.cx with ⟨h3 | hU, -⟩ | ⟨-, hc, -⟩
    · rw [card_quot_of_sl_three h3] at h9
      norm_num at h9
    · rw [card_of_lieModel_psu_three_three hU] at h9
      norm_num at h9
    · exact hc
  obtain ⟨z, hz, hz2, hGz, -, hzZ⟩ := hpre G T L V hcx
  obtain ⟨hc, hcases⟩ := modules_cases_of_hyp1223_F4 h1222 hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hcomm : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h1 := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  refine ⟨z, hc, hsq, hyp.irrPlus.2.2.1, hcomm,
    pCoreOf_le_centralizer_of_isPrimeReduced_sup hyp.normalizes hVLT hred, fun h => ?_, hVT, hTV,
    hcard, hcases.2.2 h5 hcard, hz, hz2, hzZ h5, hGz⟩
  apply hV1
  rw [← hcomm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)

namespace Cx5Facts

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {z : G}

theorem normalizer_le_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (hcx : Cx1242 G T L V)
    (hf : Cx5Facts G T L V z) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have h := (stmt12_2_6_of_F4 h1222 h323 G T L V hcx.hyp).2 V (Subgroup.normalizer (V : Set G))
    hf.ne_bot le_rfl le_rfl
  rw [inf_idem] at h
  rw [← h]
  exact inf_le_right

theorem centralizer_le_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (hcx : Cx1242 G T L V)
    (hf : Cx5Facts G T L V z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hzV : z ∈ V := hf.mem.1
  have hU : Subgroup.zpowers z ≠ ⊥ := fun h => hf.ne_one (by
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h] at this
    exact this)
  have hCN : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    have h1 : Subgroup.centralizer ({z} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h1]
    exact Subgroup.centralizer_le_normalizer _
  have h := (stmt12_2_6_of_F4 h1222 h323 G T L V hcx.hyp).2 (Subgroup.zpowers z)
    (Subgroup.centralizer ({z} : Set G)) hU (Subgroup.zpowers_le.2 hzV) hCN
  rw [inf_eq_left.2 hf.Gz] at h
  rw [h]
  exact inf_le_right

theorem b4Hyp_F4 [IsMulCommutative ↥V] (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight)
    (h12210 : Stmt12_2_10_F4) (hcx : Cx1242 G T L V) (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :
    B4Hyp (autOn (L ⊔ T) V) (autOn L V) := by
  have hyp := hcx.hyp
  have := hyp.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hf.normalizes hf.T_le

  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hQ := pCoreOf_sup_eq_of_hyp1223_F4 h1222 h3228 hyp
  have hQne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := by
    rw [hQ]
    intro hb
    apply hf.ne_bot
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ T ⊓ Subgroup.centralizer (V : Set G) := ⟨hf.le_T hv, hf.le_centralizer hv⟩
    rw [hb] at h1
    exact h1
  have hSLT : SQTKGroup ↥(L ⊔ T) := InternalSec.sqtkGroup_of_localSQTK hloc hQne
  have hSX : SQTKGroup ↥(autOn (L ⊔ T) V) :=
    InternalSec.sqtkGroup_autOn hLTV hSLT (hf.isPGroup_inf_centralizer hcx h5)

  have hLX : autOn L V ≤ autOn (L ⊔ T) V := autOn_mono le_sup_left
  have hn : ∀ y ∈ autOn (L ⊔ T) V, ∀ l ∈ autOn L V, y * l * y⁻¹ ∈ autOn L V :=
    InternalSec.autOn_normal_of (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hq : CFSG.IsQuasisimple ↥(autOn L V) :=
    isQuasisimple_autOn_of_pCoreOf_le hf.normalizes hyp.quasisimple hf.pCore hf.notCent
  have h2 : ∀ y ∈ autOn (L ⊔ T) V, ∃ e : ℕ, y ^ 2 ^ e ∈ autOn L V :=
    InternalSec.autOn_two_of hf.normalizes fun y hy => by
      obtain ⟨k, hk⟩ := exists_two_pow_mem_L hcx hy
      exact ⟨k, le_sup_left (b := Subgroup.centralizer (V : Set G)) hk⟩

  have hO2 : pCoreOf 2 (autOn (L ⊔ T) V) = ⊥ := by
    set X := autOn (L ⊔ T) V with hXdef
    set P := pCoreOf 2 X with hPdef
    have hPX : P ≤ X := LieType.BorelTits.pCoreOf_le 2 X
    have hXP : X ≤ Subgroup.normalizer (P : Set (MulAut ↥V)) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 X
    have hPp : IsPGroup 2 ↥P := LieType.BorelTits.pCoreOf_isPGroup 2 X
    have hs := hf.simple_lbar h5
    have hnab := hf.nonabelian_lbar h5

    have hPL : P ⊓ autOn L V = ⊥ := by
      have hnorm : ((P ⊓ autOn L V).subgroupOf (autOn L V)).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        refine ⟨?_, (autOn L V).mul_mem ((autOn L V).mul_mem g.2 hx.2) ((autOn L V).inv_mem g.2)⟩
        exact (Subgroup.mem_normalizer_iff.1 (hXP (hLX g.2)) _).1 hx.1
      have hp : IsPGroup 2 ↥((P ⊓ autOn L V).subgroupOf (autOn L V)) :=
        (hPp.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have hb := eq_bot_of_normal_of_isPGroup hnab _ hp
      rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : P ⊓ autOn L V ≤ autOn L V), hb,
        Subgroup.map_bot]

    have hPC : P ≤ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : p * l * p⁻¹ * l⁻¹ ∈ P ⊓ autOn L V := by
        refine ⟨?_, (autOn L V).mul_mem (hn p (hPX hp) l hl) ((autOn L V).inv_mem hl)⟩
        rw [show p * l * p⁻¹ * l⁻¹ = p * (l * p⁻¹ * l⁻¹) by group]
        exact P.mul_mem hp ((Subgroup.mem_normalizer_iff.1 (hXP (hLX hl)) _).1 (P.inv_mem hp))
      rw [hPL, Subgroup.mem_bot] at h1
      calc l * p = (p * l * p⁻¹ * l⁻¹)⁻¹ * (p * l) := by group
        _ = p * l := by rw [h1, inv_one, one_mul]
    have hMV : hyp.MVbar = X := by
      rw [(h12210 G T L V hyp).2.2, hXdef, hf.autOn_sup]
    have hZ := (h12210 G T L V hyp).1
    rw [hMV, inf_centralizer_eq_bot_of_simple hs hnab] at hZ
    rw [eq_bot_iff]
    intro p hp
    have h1 : p ∈ X ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) := ⟨hPX hp, hPC hp⟩
    rw [hZ] at h1
    exact h1
  have hF : autOn L V = quasithinGenFitting (autOn (L ⊔ T) V) :=
    (InternalSec.quasithinGenFitting_eq_of_two_pow hLX hn (B1Red.isQuasisimple_to_open hq) h2
      hO2).symm

  have hirr := hf.irr_lbar
  refine ⟨hSX, hF, hq, ⟨?_, fun J hJ _ _ => hirr J fun a ha w hw => hJ ⟨a, ha⟩ w hw⟩⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  apply hf.ne_bot
  have h1 : Nat.card ↥(⊤ : Subgroup ↥V) = 1 := by rw [h, Subgroup.card_bot]
  rw [Subgroup.card_top, Nat.card_eq_one_iff_unique] at h1
  rw [eq_bot_iff]
  intro v hv
  have h2 : (⟨v, hv⟩ : ↥V) = 1 := h1.1.elim _ _
  exact congrArg Subtype.val h2

end Cx5Facts

end CFSG.Quasithin.H13
