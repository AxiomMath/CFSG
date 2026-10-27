module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Sub

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G]

theorem eq_bot_or_eq_of_isSubnormal {H K : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hKH : IsSubnormal K H) : K = ⊥ ∨ K = H :=
  hKH.eq_bot_or_eq_of_isSimpleGroup hH

variable [Finite G]

theorem eq_bot_of_isSubnormal_of_charTwo {H K : Subgroup G} (hH : CharTwo H) (hKH : IsSubnormal K H)
    (hK1 : ∀ N : Subgroup ↥K, N.Normal → IsPGroup 2 ↥N → N = ⊥)
    (hK2 : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → N = ⊤) : K = ⊥ := by
  have hKH' : K ≤ H := A3.subnormal_le hKH
  have hQH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hQN
  have hcomm : ⁅K, pCoreOf 2 H⁆ ≤ K ⊓ pCoreOf 2 H :=
    commutator_le_inf_of_isSubnormal hKH hQH hQn hQ2 (le_closure_oddPPow hK2)
  have hDK : K ⊓ pCoreOf 2 H = ⊥ := by
    set D : Subgroup ↥K := (K ⊓ pCoreOf 2 H).subgroupOf K with hD
    have hDn : D.Normal := by
      refine ⟨fun d hd g => ?_⟩
      rw [hD, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hd ⊢
      refine ⟨K.mul_mem (K.mul_mem g.2 hd.1) (K.inv_mem g.2), ?_⟩
      have := (Subgroup.mem_normalizer_iff.1 (hQN (hKH' g.2)) (d : G)).1 hd.2
      simpa using this
    have hD2 : IsPGroup 2 ↥D :=
      (hQ2.to_le (inf_le_right : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 H)).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ pCoreOf 2 H ≤ K)).symm
    have hD0 : D = ⊥ := hK1 D hDn hD2
    have hd := Subgroup.subgroupOf_eq_bot.1 hD0
    exact disjoint_self.1 (hd.mono_right inf_le_left)
  have hKC : K ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 (hcomm.trans hDK.le))
  have hKQ : K ≤ pCoreOf 2 H := fun x hx => hH ⟨hKH' hx, hKC hx⟩
  have hK2g : IsPGroup 2 ↥K := hQ2.to_le hKQ
  have hbot : (⊥ : Subgroup ↥K) = ⊤ :=
    hK2 ⊥ (hK2g.of_surjective (QuotientGroup.mk' (⊥ : Subgroup ↥K)) (QuotientGroup.mk'_surjective _))
  refine eq_bot_iff.2 fun x hx => ?_
  have : (⟨x, hx⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
  rw [← hbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

end L246C127

end CFSG.QuasithinUnique
