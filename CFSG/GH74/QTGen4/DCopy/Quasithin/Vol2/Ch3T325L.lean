module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch3T325L

public section
namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

namespace Ctx

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem eq_commutator_thompsonJ_F4 (h6 : Vol2.Ch11.TmpL6_3_2_2_six_F4)
    (hC : V₀ ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : L = ⁅L, thompsonJ T⁆ := by
  have hne : fsuCVM T L V₀ ≠ ⊥ := by
    rw [c.fsuCVM_eq]
    intro h
    exact hC (le_bot_iff.mp (h ▸ inf_le_inf_right _ ((V₀_le_V T V₀).trans (V_le_VM T L V₀))))
  have hU : IsUniqueM (fsuL0 T L ⊔ T) (fsuM T L) := by
    show IsUniqueM (conjClosure L T ⊔ T) (Subgroup.normalizer (conjClosure L T : Set G))
    rw [c.eqL]
    exact c.uniq
  have h := (h6 G T L V₀ c.fsu hne hU).1
  change conjClosure L T = ⁅conjClosure L T, thompsonJ T⁆ at h
  rwa [c.eqL] at h

theorem case_one_F4 (h56 : AsB56) (h6 : Vol2.Ch11.TmpL6_3_2_2_six_F4)
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))]
    (hC : V₀ ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    V₀ = conjClosure V₀ T ∧
      conjClosure V₀ T = conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set VM := conjClosure (conjClosure V₀ T) M with hVMdef
  have hV₀VM : V₀ ≤ VM := (V₀_le_V T V₀).trans (V_le_VM T L V₀)
  have hLW : L ≤ Subgroup.normalizer (VM : Set G) := Subgroup.le_normalizer.trans (M_le_NVM T L V₀)
  obtain ⟨A, -, hA, hLA⟩ := c.exists_offender (c.eq_commutator_thompsonJ_F4 h6 hC)
  obtain ⟨hKJ, hn, -, -, hcases⟩ := b56Cases_ffJ_autOn h56 c.elemVM.2 (M_le_NVM T L V₀)
    Subgroup.le_normalizer le_rfl c.sqtkM (Setup.pCoreOf_autOn_eq_bot c.redVM) hA hLA
  set K := autOn L VM with hKdef
  set I := V₀.subgroupOf VM with hIdef
  have hcommK : commV K = ⊤ := commV_autOn_eq_top hLW c.comm_VM
  have h1 := b56Case1_of_commV hKJ hn c.quasi_LVM hcommK hcases
  have hF := eq_of_le_quasisimple hKJ hn c.quasi_LVM h1.1
  have h51 := h1.2.1
  rw [hF] at h51
  have hP2 : B51Part2 K := h51.2.1
  have hfix : fixV K ⊓ commV K ≠ ⊥ := by
    rw [hcommK, inf_top_eq]
    obtain ⟨⟨x, hxV, hxC⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC
    intro hbot
    have hmem : (⟨x, hV₀VM hxV⟩ : ↥VM) ∈ fixV K := by
      intro k hk
      obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hk
      apply Subtype.ext
      rw [coe_conjAct_apply]
      show (g : G) * x * (g : G)⁻¹ = x
      rw [Subgroup.mem_centralizer_iff.mp hxC (g : G) hgL, mul_inv_cancel_right]
    rw [hbot, Subgroup.mem_bot] at hmem
    have hx : x = 1 := congrArg Subtype.val hmem
    exact hx1 (Subtype.ext hx)
  have hirr : commV K ∈ IrrPlus K ⊤ := (hP2.2 (hP2.1.mpr (Or.inl hfix))).1
  rw [hcommK] at hirr
  have hIinv : XMod.IsInv ↥K I := fun a v hv => autOn_inv_subgroupOf c.L_le_NV₀ a a.2 v hv
  have hVMI : VM ≤ V₀ := by
    rcases hirr.2.2.2.2 _ (hIinv.sup (XMod.isInv_fixed ⊤)) le_sup_right le_top with h | h
    · exfalso
      have hne : ¬ V₀ ≤ Subgroup.centralizer (L : Set G) := by
        intro hle
        apply c.V₀_ne_bot
        rw [← c.comm_V₀, eq_bot_iff, Subgroup.commutator_le]
        intro v hv l hl
        rw [Subgroup.mem_bot, commutatorElement_def,
          ← Subgroup.mem_centralizer_iff.1 (hle hv) l hl]
        group
      refine not_le_fixV_subgroupOf hV₀VM hLW hne fun v hv k hk => ?_
      have hvf : v ∈ XMod.fixed ↥K ⊤ := by
        rw [← h]
        exact (le_sup_left : I ≤ I ⊔ XMod.fixed ↥K ⊤) hv
      exact hvf.2 ⟨k, hk⟩
    · have hle : XMod.commOf ↥K (⊤ : Subgroup ↥VM) ≤ I := by
        rw [← h, XMod.commOf_sup_eq_of_le_fixed le_rfl]
        exact XMod.commOf_le_of_isInv hIinv
      rw [hirr.2.2.1] at hle
      exact fun v hv => hle (Subgroup.mem_top ⟨v, hv⟩)
  exact ⟨le_antisymm (V₀_le_V T V₀) ((V_le_VM T L V₀).trans hVMI),
    le_antisymm (V_le_VM T L V₀) (hVMI.trans (V₀_le_V T V₀))⟩

end Ctx

end CFSG.Quasithin.H13.T325
