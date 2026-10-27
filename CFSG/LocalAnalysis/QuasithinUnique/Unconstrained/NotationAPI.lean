module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_5

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Tuple

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem Tuple25.le_M_of_charTwo (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    {X : Subgroup G} (hSX : S ≤ X) (hX : CharTwo X) : X ≤ M :=
  IsGamma0.le_of_charTwo_of_forall_not_charTwo hs.setting hs.noCharTwo ht.gamma0 ht.sylow_inf
    hSX hX

theorem Tuple25.maximal_inf (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z) :
    (H ⊓ M ≤ H ∧ S ≤ H ⊓ M ∧ CharTwo (H ⊓ M)) ∧
      (∀ X : Subgroup G, X ≤ H → S ≤ X → CharTwo X → X ≤ H ⊓ M) ∧
      Maximal (fun X : Subgroup G => X ≤ H ∧ S ≤ X ∧ CharTwo X) (H ⊓ M) ∧
      ∀ X : Subgroup G, Maximal (fun X : Subgroup G => X ≤ H ∧ S ≤ X ∧ CharTwo X) X →
        X = H ⊓ M :=
  IsGamma0.maximal_inf_of_forall_not_charTwo hs.setting hs.noCharTwo ht.gamma0 ht.sylow_inf
    (ht.gamma0.charTwo_inf hs.setting ht.sylow_inf)

theorem Tuple25.le_T (ht : Tuple25 T M H S z) : S ≤ T := ht.lt.le

theorem Tuple25.le_H (ht : Tuple25 T M H S z) : S ≤ H := ht.sylow.le

end Tuple

namespace Notation25

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

theorem S_le_H : N.S ≤ N.H := N.tuple.le_H

theorem S_le_T : N.S ≤ T := N.tuple.le_T

theorem K_le_H : N.K ≤ N.H := N.isComp.1

theorem K0_le_H : N.K0 ≤ N.H := by
  refine iSup_le fun s => ?_
  rintro _ ⟨y, hy, rfl⟩
  have hs' : (s : G) ∈ N.H := N.S_le_H s.2
  exact N.H.mul_mem (N.H.mul_mem hs' (N.K_le_H hy)) (N.H.inv_mem hs')

theorem H_le_normalizer_K0 : N.H ≤ Subgroup.normalizer (N.K0 : Set G) := by
  rw [N.join]
  exact sup_le ((N.K_le_K0).trans Subgroup.le_normalizer) N.S_le_normalizer_K0

theorem H_eq_K0_sup_S : N.H = N.K0 ⊔ N.S := by
  refine le_antisymm ?_ (sup_le N.K0_le_H N.S_le_H)
  rw [N.join]
  exact sup_le_sup_right N.K_le_K0 _

theorem le_M_of_charTwo {X : Subgroup G} (hSX : N.S ≤ X) (hX : CharTwo X) : X ≤ M :=
  N.tuple.le_M_of_charTwo hs hSX hX

theorem charTwo_inf : CharTwo (N.H ⊓ M) :=
  N.tuple.gamma0.charTwo_inf hs.setting N.tuple.sylow_inf

end Notation25

end CFSG.QuasithinUnique
