module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem normalizer_S_le_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611Nat G T M L V n) :
    Subgroup.normalizer (ch6S T L V : Set G) ≤ M := by
  have hSL : ch6S T L V ⊓ L = T ⊓ L := by
    apply le_antisymm (inf_le_inf_right L inf_le_left)
    have hTLS : T ⊓ L ≤ ch6S T L V := by rw [h.S_eq]; exact le_sup_left
    exact le_inf hTLS inf_le_right
  have hsyl := h.toHyp611.isSylowIn_TL
  refine (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le h.maximal
    h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).2 _ inf_le_left ?_
  rw [hSL]
  exact ⟨hsyl.1, hsyl.2.1, hsyl.2.2⟩

theorem normalizer_ZS_eq_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611Nat G T M L V n) :
    Subgroup.normalizer (ch6ZS T L V : Set G) =
        Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
          (M ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) ∧
      Subgroup.normalizer (ch6ZS T L V : Set G) =
        Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
          (ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) := by
  have hle : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (ch6ZS T L V : Set G) →
      Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ X ≤
        Subgroup.normalizer (ch6ZS T L V : Set G) :=
    fun X hX => sup_le (Subgroup.centralizer_le_normalizer _) hX
  have hS := h.isSylowIn_S
  have hfrat := exists_mul_of_sylow (Subgroup.centralizer_le_normalizer _)
    (F7.normalizer_le_normalizer_centralizer _) hS.le hS.isPGroup hS.not_dvd_relIndex
  have hNS := h.normalizer_S_le_F4 h432
  have hMV : M ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ≤ ch6MV M V :=
    h.normalizer_le h.ZS_ne_bot h.ZS_le
  have key : Subgroup.normalizer (ch6ZS T L V : Set G) ≤
      Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
        (ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) := by
    intro x hx
    obtain ⟨m, hm, c, hc, rfl⟩ := hfrat x hx
    rw [sup_comm]
    refine Subgroup.mul_mem_sup ?_ hc
    exact ⟨hMV ⟨hNS hm.2, hm.1⟩, hm.1⟩
  refine ⟨le_antisymm ?_ (hle _ inf_le_right), le_antisymm key (hle _ inf_le_right)⟩
  exact key.trans (sup_le_sup_left (inf_le_inf_right _ inf_le_left) _)

end Hyp611Nat

end CFSG.Quasithin.H13
