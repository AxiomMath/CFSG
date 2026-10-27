module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3G2Off
public import CFSG.Quasithin.H13.U3G2Blk

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

theorem V_ne_bot_F4
    (S : HullSetting_F4 G T L V z) : V ≠ ⊥ := fun h => by
  have := S.hV64_F4
  rw [h, card_bot] at this
  omega

theorem blockU_le_F4
    (S : HullSetting_F4 G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) : blockU L ≤ V :=
  blockU_le_of_irr hL S.hLV_F4
    (le_blockQ_of (B2F.isPGroup_of_isElemAbelian (isElemAbelian_of_isElementaryAbelian' V))
      (S.hVT_F4.trans S.hTL_F4) S.hLV_F4 hVL)
    hVL (inf_centralizer_L_eq_bot S.hF) S.V_ne_bot_F4

theorem blockU_eq_F4
    (S : HullSetting_F4 G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) : blockU L = V := by
  refine le_antisymm (S.blockU_le_F4 hL hVL) ?_
  rw [← hVL]
  exact commutator_mono (le_blockQ_of (B2F.isPGroup_of_isElemAbelian
    (isElemAbelian_of_isElementaryAbelian' V)) (S.hVT_F4.trans S.hTL_F4) S.hLV_F4 hVL) le_rfl

theorem normalizer_L_le_F4
    (S : HullSetting_F4 G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) :
    normalizer (L : Set G) ≤ normalizer (V : Set G) := fun g hg => by
  have := C1.mem_normalizer_blockU hg
  rwa [S.blockU_eq_F4 hL hVL] at this

theorem comm_mem_V_F4
    (S : HullSetting_F4 G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {y : G} (hyT : y ∈ T)
    (hyV : y ∈ centralizer (V : Set G)) : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ V :=
  commutator_mem_of_centralizer hL S.hLV_F4 (S.blockU_le_F4 hL hVL) S.inf_centralizer_le_F4 (S.hTL_F4 hyT)
    hyV

theorem le_normalizer_of_F4
    (S : HullSetting_F4 G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {W : Subgroup G}
    (hVW : V ≤ W) (hWT : W ≤ T) (hWC : W ≤ centralizer (V : Set G)) :
    L ≤ normalizer (W : Set G) := by
  have key : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
    intro l hl w hw
    have h1 := S.comm_mem_V_F4 hL hVL (hWT hw) (hWC hw) l hl
    have e : l * w * l⁻¹ = (w * l * w⁻¹ * l⁻¹)⁻¹ * w := by group
    rw [e]
    exact mul_mem (inv_mem (hVW h1)) hw
  intro l hl
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key l hl w, fun hw => ?_⟩
  have := key l⁻¹ (inv_mem hl) _ hw
  simpa [mul_assoc] using this

theorem normalizer_le_of_F4
    (S : HullSetting_F4 G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {W : Subgroup G}
    (hVW : V ≤ W) (hWT : W ≤ T) (hWC : W ≤ centralizer (V : Set G))
    (hTW : T ≤ normalizer (W : Set G)) : normalizer (W : Set G) ≤ normalizer (L : Set G) :=
  normalizer_le_of_isUniqueM S.uniqueM_F4 (S.hH.sylow.1.to_le hWT)
    (fun h => S.V_ne_bot_F4 (le_bot_iff.1 (h ▸ hVW)))
    (sup_le (S.le_normalizer_of_F4 hL hVL hVW hWT hWC) hTW)

theorem normalizer_B_le_of_comm_F4
    (S : HullSetting_F4 G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V)
    (h : ∀ g ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G),
      cjSub g V ≤ centralizer (V : Set G)) :
    normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G) ≤ normalizer (L : Set G) := by
  set NB := normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G) with hNB
  have hWB : conjClosure V NB ≤ baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) :=
    conjClosure_le fun g hg v hv => (mem_normalizer_iff.1 hg v).1 (S.V_le_B_F4 hv)
  have hWC : conjClosure V NB ≤ centralizer (V : Set G) :=
    conjClosure_le fun g hg v hv => h g hg (mem_cjSub.2 (by simpa [mul_assoc] using hv))
  have hle := S.normalizer_le_of_F4 hL hVL (le_conjClosure V NB) (hWB.trans S.B_le_T_F4) hWC
    (S.T_le_normalizer_B_F4.trans (le_normalizer_conjClosure V NB))
  exact (le_normalizer_conjClosure V NB).trans hle

theorem B_le_normalizer_cjSub_F4
    (S : HullSetting_F4 G T L V z) {g : G}
    (hg : g ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G)) :
    baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) ≤ normalizer (cjSub g V : Set G) := by
  intro b hb
  have hb' : g⁻¹ * b * g ∈ baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) := by
    have := (mem_normalizer_iff.1 (inv_mem hg) b).1 hb
    simpa using this
  have hbN : g⁻¹ * b * g ∈ normalizer (V : Set G) := S.hTV_F4 (S.B_le_T_F4 hb')
  rw [mem_normalizer_iff]
  intro y
  rw [mem_cjSub, mem_cjSub]
  have e : g⁻¹ * (b * y * b⁻¹) * g = (g⁻¹ * b * g) * (g⁻¹ * y * g) * (g⁻¹ * b * g)⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 hbN _

theorem card_inf_le_F4
    (S : HullSetting_F4 G T L V z) {g : G}
    (hg : g ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G)) :
    Nat.card ↥(V ⊓ centralizer (cjSub g V : Set G)) ≤
      Nat.card ↥(cjSub g V ⊓ centralizer (V : Set G)) := by
  have hXT : cjSub g V ≤ T := (cjSub_le hg S.V_le_B_F4).trans S.B_le_T_F4
  have h1 := S.card_mul_card_le_F4 hXT (isElemAbelian_cjSub (isElemAbelian_of_isElementaryAbelian' V))
  have h2 := relIndex_mul_card (cjSub g V ⊓ centralizer (V : Set G)) (cjSub g V)
  rw [inf_eq_left.2 (inf_le_left : cjSub g V ⊓ centralizer (V : Set G) ≤ cjSub g V),
    card_cjSub, S.hV64_F4] at h2
  have hpos : 0 < (cjSub g V ⊓ centralizer (V : Set G)).relIndex (cjSub g V) :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at h2; omega
  exact Nat.le_of_mul_le_mul_left (h1.trans h2.symm.le) hpos

theorem card_inf_eq_F4
    (S : HullSetting_F4 G T L V z) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G)) :
    Nat.card ↥(V ⊓ centralizer (cjSub x V : Set G)) =
      Nat.card ↥(cjSub x V ⊓ centralizer (V : Set G)) := by
  have h1 := S.card_inf_le_F4 hx
  have h2 := S.card_inf_le_F4 (inv_mem hx)
  have h3 := card_inf_centralizer_cjSub V x
  have h4 := card_inf_centralizer_cjSub V x⁻¹
  rw [inv_inv] at h4
  omega

theorem isA1_imgL_F4
    (S : HullSetting_F4 G T L V z) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) : IsA1 (S.imgL_F4 (cjSub x V)) := by
  have hXB : cjSub x V ≤ baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) := cjSub_le hx S.V_le_B_F4
  have hXT : cjSub x V ≤ T := hXB.trans S.B_le_T_F4
  have hXN : cjSub x V ≤ normalizer (V : Set G) := hXT.trans S.hTV_F4
  have hab := isElemAbelian_cjSub (g := x) (isElemAbelian_of_isElementaryAbelian' V)
  refine isA1_of_fix (S.imgL_le_S0L_F4 hXT) (S.isElementaryAbelian_imgL_F4 hab) ?_ ?_ ?_
  · rw [S.card_imgL_F4 hXN, ← S.card_inf_centralizer_F4 hXN, S.card_inf_eq_F4 hx]
    have h2 := relIndex_mul_card (cjSub x V ⊓ centralizer (V : Set G)) (cjSub x V)
    rw [inf_eq_left.2 (inf_le_left : cjSub x V ⊓ centralizer (V : Set G) ≤ cjSub x V),
      card_cjSub, S.hV64_F4] at h2
    exact h2
  · exact fun h => hxV ((S.imgL_eq_bot_iff_F4 hXN).1 h)
  · exact fun e he => S.imgL_B_fix_F4 e (S.imgL_mono_F4 hXB he)

theorem inf_centralizer_cjSub_eq_F4
    (S : HullSetting_F4 G T L V z) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) :
    V ⊓ centralizer (cjSub x V : Set G) = S.V₃_F4 := by
  have hXN : cjSub x V ≤ normalizer (V : Set G) :=
    ((cjSub_le hx S.V_le_B_F4).trans S.B_le_T_F4).trans S.hTV_F4
  rw [S.inf_centralizer_eq_F4 hXN, (S.isA1_imgL_F4 hx hxV).linFix_eq, S.V₃_eq_pullSub_F4]

theorem V₃_le_cjSub_F4
    (S : HullSetting_F4 G T L V z) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) : S.V₃_F4 ≤ cjSub x V := by
  intro c hc
  rw [S.V₃_eq_pullSub_F4] at hc
  obtain ⟨hcV, hcP⟩ := mem_pullSub.1 hc
  obtain ⟨e, he, w, hew⟩ := (S.isA1_imgL_F4 hx hxV).exists_sub_eq hcP
  obtain ⟨n, hnN, hnX, rfl⟩ := S.mem_imgL_F4.1 he
  set v := elOf S.Φ w with hv
  have hvV : v ∈ V := elOf_mem w
  have h1 := S.phi_comm_F4 hnN hvV
  rw [show S.Φ (Additive.ofMul (⟨v, hvV⟩ : V)) = w from phi_elOf w, hew] at h1
  have h2 : n * v * n⁻¹ * v⁻¹ = c := phi_injective' _ hcV h1
  rw [← h2]
  have hvX : v ∈ normalizer (cjSub x V : Set G) := S.B_le_normalizer_cjSub_F4 hx (S.V_le_B_F4 hvV)
  have h3 : v * n⁻¹ * v⁻¹ ∈ cjSub x V := (mem_normalizer_iff.1 hvX _).1 (inv_mem hnX)
  have e : n * v * n⁻¹ * v⁻¹ = n * (v * n⁻¹ * v⁻¹) := by group
  rw [e]
  exact mul_mem hnX h3

theorem cjSub_inf_centralizer_eq_F4
    (S : HullSetting_F4 G T L V z) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) :
    cjSub x V ⊓ centralizer (V : Set G) = S.V₃_F4 := by
  have hle : S.V₃_F4 ≤ cjSub x V ⊓ centralizer (V : Set G) :=
    le_inf (S.V₃_le_cjSub_F4 hx hxV)
      (S.le3_F4.trans (B2F.le_centralizer_self (isElemAbelian_of_isElementaryAbelian' V)))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [S.card_V₃_F4, ← S.card_inf_eq_F4 hx, S.inf_centralizer_cjSub_eq_F4 hx hxV, S.card_V₃_F4]

end HullSetting_F4

end CFSG.Quasithin.H13.U3
