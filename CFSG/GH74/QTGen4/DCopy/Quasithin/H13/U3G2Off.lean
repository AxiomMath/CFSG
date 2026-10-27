module

public import CFSG.Quasithin.H13.U3G2Off
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3G2Img
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3X10U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G]

namespace HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting_F4

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem L₁_le_F4
    (S : HullSetting_F4 G T L V z) : L₁Of L S.V₁_F4 ≤ L :=
  (oTwoRes_le _).trans inf_le_left

theorem V_le_R₁_F4
    (S : HullSetting_F4 G T L V z) : V ≤ pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (S.hVT_F4.trans le_sup_right)
    (sup_le (S.L₁_le_F4.trans S.hLV_F4) S.hTV_F4)
    (B2F.isPGroup_of_isElemAbelian (isElemAbelian_of_isElementaryAbelian' V))

theorem R₁_le_T_F4
    (S : HullSetting_F4 G T L V z) : pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T) ≤ T :=
  F7.isSylowTwoOf_pCoreOf_le (A5.isSylowTwoOf_of_le S.hH.sylow le_sup_right)

theorem le_normalizer_R₁_F4
    (S : HullSetting_F4 G T L V z) :
    L₁Of L S.V₁_F4 ⊔ T ≤ normalizer (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T) : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem l₁_mem_L₁T_F4
    (S : HullSetting_F4 G T L V z) : S.l₁ ∈ L₁Of L S.V₁_F4 ⊔ T := by
  have hl₁N : S.l₁ ∈ L ⊓ normalizer (S.V₁_F4 : Set G) := by
    rw [S.normalizer_V₁_F4]
    exact ⟨S.l₁_mem_F4, S.l₁_H_F4⟩
  exact S.inf_normalizer_V₁_le_F4 hl₁N

theorem imgL_eq_bot_iff_F4
    (S : HullSetting_F4 G T L V z) {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) :
    S.imgL_F4 X = ⊥ ↔ X ≤ centralizer (V : Set G) := by
  constructor
  · intro h x hx
    have h1 := S.glLin_rho_mem_imgL_F4 hx (hXN hx)
    rw [h, mem_bot, MulEquiv.map_eq_one_iff] at h1
    exact (mem_centralizer_V_iff (hXN hx) (S.rho_spec_F4 _)).2 h1
  · intro h
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL_F4.1 hg
    rw [mem_bot, (mem_centralizer_V_iff hxN (S.rho_spec_F4 _)).1 (h hxX), map_one]

theorem offender_eq_F4
    (S : HullSetting_F4 G T L V z) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) A) :
    (A ⊓ centralizer (V : Set G)).relIndex A * Nat.card ↥(V ⊓ centralizer (A : Set G)) = 64 :=
  le_antisymm (S.card_mul_card_le_F4 (hA.1.trans S.R₁_le_T_F4) hA.2.1)
    (S.hV64_F4 ▸ card_le_relIndex_mul_card (isElemAbelian_of_isElementaryAbelian' V) S.V_le_R₁_F4 hA)

theorem imgL_A_F4
    (S : HullSetting_F4 G T L V z) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) A) :
    S.imgL_F4 A = ⊥ ∨ IsA1 (S.imgL_F4 A) := by
  have hAT : A ≤ T := hA.1.trans S.R₁_le_T_F4
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans S.hTV_F4
  by_cases hbot : S.imgL_F4 A = ⊥
  · exact Or.inl hbot
  right
  refine isA1_of_xStable (S.imgL_le_S0L_F4 hAT) (S.isElementaryAbelian_imgL_F4 hA.2.1) ?_ hbot ?_
  · rw [S.card_imgL_F4 hAN, ← S.card_inf_centralizer_F4 hAN]
    exact S.offender_eq_F4 hA
  · intro e he
    obtain ⟨a, haN, haA, rfl⟩ := S.mem_imgL_F4.1 he
    have hl₁ : S.l₁ ∈ normalizer (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T) : Set G) :=
      S.le_normalizer_R₁_F4 S.l₁_mem_L₁T_F4
    have hc : S.l₁ * a * S.l₁⁻¹ ∈ T :=
      S.R₁_le_T_F4 ((mem_normalizer_iff.1 hl₁ a).1 (hA.1 haA))
    have hρ : S.rho_F4 ⟨S.l₁, S.l₁_N_F4⟩ = xGL := S.rho_eq_of_spec_F4 S.l₁_N_F4 S.l₁_spec_F4
    have e : (⟨S.l₁ * a * S.l₁⁻¹, S.hTV_F4 hc⟩ : normalizer (V : Set G)) =
        ⟨S.l₁, S.l₁_N_F4⟩ * ⟨a, haN⟩ * ⟨S.l₁, S.l₁_N_F4⟩⁻¹ := rfl
    have h1 := S.rho_T_mem_F4 hc
    rw [e, map_mul, map_mul, map_inv, hρ] at h1
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]

theorem V₃_le_A_F4
    (S : HullSetting_F4 G T L V z) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) A) : S.V₃_F4 ≤ A := by
  have hAN : A ≤ normalizer (V : Set G) := (hA.1.trans S.R₁_le_T_F4).trans S.hTV_F4
  rcases S.imgL_A_F4 hA with h | h
  · have hAC := (S.imgL_eq_bot_iff_F4 hAN).1 h
    have hsup := (B24_three (isElemAbelian_of_isElementaryAbelian' V) S.V_le_R₁_F4 hA (S.hV64_F4.trans
      (S.offender_eq_F4 hA).symm)).1
    rw [inf_eq_left.2 hAC] at hsup
    have heq : A = A ⊔ V := Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hsup.1 hsup.2.1)
    exact S.le3_F4.trans (heq ▸ le_sup_right)
  · have h1 := S.inf_centralizer_eq_F4 hAN
    rw [h.linFix_eq, ← S.V₃_eq_pullSub_F4] at h1
    rw [← h1]
    exact inf_centralizer_le_of_isMaxElemAbelian (isElemAbelian_of_isElementaryAbelian' V)
      S.V_le_R₁_F4 hA

theorem B_le_F4
    (S : HullSetting_F4 G T L V z) :
    baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) ≤ centralizer (S.V₃_F4 : Set G) := by
  have h : S.V₃_F4 ≤ omegaOneCenterOf (thompsonJ (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T))) := by
    rw [(omegaOne_centralizer_thompsonJ _).2]
    exact le_iInf₂ fun A hA => S.V₃_le_A_F4 hA
  exact inf_le_right.trans (centralizer_le h)

theorem V_le_B_F4
    (S : HullSetting_F4 G T L V z) : V ≤ baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T))
  have hsup := (B24_three (isElemAbelian_of_isElementaryAbelian' V) S.V_le_R₁_F4 hA (S.hV64_F4.trans
    (S.offender_eq_F4 hA).symm)).1
  exact le_sup_right.trans (isMaxElemAbelian_le_baum hsup)

theorem B_le_T_F4
    (S : HullSetting_F4 G T L V z) : baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) ≤ T :=
  inf_le_left.trans S.R₁_le_T_F4

theorem T_le_normalizer_B_F4
    (S : HullSetting_F4 G T L V z) :
    T ≤ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G) :=
  (le_sup_right.trans S.le_normalizer_R₁_F4).trans (normalizer_le_normalizer_baum _)

theorem imgL_B_fix_F4
    (S : HullSetting_F4 G T L V z) :
    ∀ e ∈ S.imgL_F4 (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T))), ∀ w ∈ V3sub, e w = w := by
  intro e he w hw
  obtain ⟨b, hbN, hbB, rfl⟩ := S.mem_imgL_F4.1 he
  have h1 : b ∈ centralizer (pullSub S.Φ V3sub : Set G) := by
    rw [← S.V₃_eq_pullSub_F4]
    exact S.B_le_F4 hbB
  exact (mem_centralizer_pullSub_iff hbN (S.rho_spec_F4 _) V3sub).1 h1 w hw

theorem card_B_le_F4
    (S : HullSetting_F4 G T L V z) :
    (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) ⊓ centralizer (V : Set G)).relIndex
      (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T))) ≤ 8 := by
  rw [← S.card_imgL_F4 (S.B_le_T_F4.trans S.hTV_F4)]
  exact card_le_eight_of_fix (S.imgL_le_S0L_F4 S.B_le_T_F4) S.imgL_B_fix_F4

end HullSetting_F4

end CFSG.Quasithin.H13.U3
