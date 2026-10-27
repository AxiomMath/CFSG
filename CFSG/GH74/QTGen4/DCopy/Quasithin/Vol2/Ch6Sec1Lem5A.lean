module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem reduced_ch615_F4 (h614 : Stmt6_1_4_F4) (h : Hyp611 G T M L V n) :
    Hyp611 G T M L (reducedAggregate (L ⊔ T)) n := by
  have hVR := h.le_reducedAggregate
  have hRred := isTwoReducedIn_reducedAggregate (L ⊔ T)
  have hVL : ⁅V, L⁆ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := Subgroup.commutator_mono hVR le_rfl
  have hRL0 : ⁅reducedAggregate (L ⊔ T), L⁆ ≠ ⊥ := fun h0 =>
    h.module.2.2 (eq_bot_iff.mpr (h0 ▸ hVL))
  have hRLR : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ reducedAggregate (L ⊔ T) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hRred.2.1)
  have hRc : ∀ a ∈ ⁅reducedAggregate (L ⊔ T), L⁆, ∀ b ∈ ⁅reducedAggregate (L ⊔ T), L⁆,
      a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hRred.2.2.1 (hRLR ha) (hRLR hb)
  exact
    { toHyp5_0_1 := h.toHyp5_0_1
      module := ⟨hRred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hRred).2, hRL0⟩
      not_a5 := by
        rintro ⟨rfl, hA5⟩
        have hq := h614 G T M L V 2 h
        have hC : ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [← isA5ModuleSum_inf_centralizer_ch615 hA5 hRc]
          exact ⟨hVL hx.1, hx.2⟩
        exact false_of_isNatModCh5_le_isA5ModuleSum (isNatModCh5_of_isNatQuotCh5 hq hC) hVL
          hRc hA5
      nParam_eq_one := h.nParam_eq_one
      noLie := h.noLie }

end Hyp611

end CFSG.Quasithin.H13
