module

public import CFSG.Sporadic.SuzOddCore.SylowFusion
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore
open CFSG.RankThree.PartTwo.Census

section Certified

theorem card_centralizer_suz_involution {u : NativeSporadic.Suz} (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Suz)) = 161280 ∨
      Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Suz)) = 3317760 := by
  have hcard : Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Suz)) =
      Nat.card ↥(suzM ⊓ Subgroup.centralizer
        ({((suzEquivM u : suzM) : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782)))) := by
    rw [@card_centralizer_mulEquiv NativeSporadic.Suz suzM Units.instGroup (Subgroup.toGroup _)
      suzEquivM u, card_centralizer_subgroup]
  have hg : orderOf ((suzEquivM u : suzM) : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe, @MulEquiv.orderOf_eq NativeSporadic.Suz Units.instMonoid suzM _
      suzEquivM u, hu]
  have hcM : ∀ i < 4, Nat.card ↥(suzM ⊓ Subgroup.centralizer
      ({suzInv i} : Set (Equiv.Perm (Fin 1782)))) = invInnerOrders.getD i 0 := fun i hi => by
    rw [inf_comm, ← card_invE hi, invE_eq_centM hi]
    rfl
  obtain ⟨c, hc, h | h⟩ := suzM_involution_class (suzEquivM u).2 hg
  all_goals
    rw [← h, card_inf_centralizer_conj suzM (fun m hm => suzT_conj_mem_suzM hc hm)
      (fun m hm => by simpa only [inv_inv] using suzT_conj_mem_suzM (suzT.inv_mem hc) hm)] at hcard
  · left
    rw [hcard, hcM 0 (by norm_num)]
    rfl
  · right
    rw [hcard, hcM 1 (by norm_num)]
    rfl

theorem card_centralizer_of_isSporadic_suz {G : Type} [Group G] (hG : IsSporadic G .Suz) {t : G}
    (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 161280 ∨
      Nat.card (Subgroup.centralizer ({t} : Set G)) = 3317760 := by
  obtain ⟨e⟩ := hG
  have hcard := @card_centralizer_mulEquiv G NativeSporadic.Suz _ Units.instGroup e t
  rw [hcard]
  exact card_centralizer_suz_involution (by
    rw [@MulEquiv.orderOf_eq G _ NativeSporadic.Suz Units.instMonoid e t, ht])

end Certified

end CFSG.EvenSporadicStandard.M12Std
