module

public import CFSG.Quasithin.H13.L32NLem14413g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14413f

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6
open CFSG.Quasithin.H13.L32A
open scoped IsMulCommutative

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

namespace XCtx_F4
open CFSG.Quasithin.H13.L14413.XCtx_F4

variable {T L V V₂ X : Subgroup G} {g : G}

section Basic

variable (C : XCtx_F4 G T L V V₂ X g)
include C

theorem VX_le_H3_F4 : ⁅V₂, X⁆ ≤ lOne L V₂ ⊔ X ⊔ T := C.VXU_F4.trans C.U_le_H3_F4

theorem pCoreOf_H3_ne_bot_F4 : pCoreOf 2 (lOne L V₂ ⊔ X ⊔ T) ≠ ⊥ := by
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 C.VX_le_H3_F4
    C.H3_le_normalizer_F4 (C.hyp.fsu.sylow.1.to_le (C.VXU_F4.trans C.UT_F4))
  intro hb
  rw [hb, le_bot_iff] at hle
  have := C.Y.2.2.2.2.1
  rw [hle, Subgroup.card_bot] at this
  omega

theorem sylow_H3_F4 : IsSylowTwoOf T (lOne L V₂ ⊔ X ⊔ T) :=
  isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow XCtx.T_le_H3

theorem T_le_normalizer_L2_F4 : T ≤ Subgroup.normalizer (lOne L V₂ : Set G) := by
  intro t ht
  have htN : t ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₂ : Set G) : Subgroup G) :
      Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨C.s1282.hyp.hyp.normalizes ht,
      Subgroup.le_normalizer (C.TV₂_F4 ht)⟩
  exact Subgroup.mem_normalizer_fintype fun y hy => conj_mem_oTwoUpper htN hy

end Basic

variable {C : XCtx_F4 G T L V V₂ X g} (K : C.Coords_F4)

theorem Coords_F4.φ_eq_one_iff_F4 (h : ↥(lOne L V₂ ⊔ X ⊔ T)) :
    K.φ_F4 h = 1 ↔ (h : G) ∈ Subgroup.centralizer ((⁅V₂, X⁆ : Subgroup G) : Set G) := by
  rw [← MonoidHom.mem_ker, show K.φ_F4.ker = _ from repV_ker C.H3_le_normalizer_F4 K.e,
    Subgroup.mem_subgroupOf]

theorem Coords_F4.exists_Lp_F4 (h39 : A39ForSQTK) :
    ∃ Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T), (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ_F4 = ⊤ :=
  exists_cComp_map_eq_top K.φ_F4 K.range_eq_top_F4
    (lemma_1_2_1_one C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h39
      C.pCoreOf_H3_ne_bot_F4)

theorem Coords_F4.normal_Lp_F4 (h37 : A37ForSQTK) {Lp : Subgroup G}
    (hLp : Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T))
    (hφ : (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ_F4 = ⊤) :
    lOne L V₂ ⊔ X ⊔ T ≤ Subgroup.normalizer (Lp : Set G) :=
  le_normalizer_of_map_eq_top K.φ_F4 (h37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot C.hyp.fsu.qtke
    C.hyp.fsu.simple C.hyp.fsu.nonabelian C.pCoreOf_H3_ne_bot_F4)) hLp hφ

end XCtx_F4

end CFSG.Quasithin.H13.L14413
