module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6MS
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C134L32Corr

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem exists_c134Case_F4 (hMS : C134L32Corr_F4)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ i : ℕ, C134CorrLocal.IsC134CaseCorr i (L ⊔ c.R1) c.R1 L := by
  obtain ⟨α, hα⟩ := c.exists_alpha
  have hcomp : L ∈ cComp (L ⊔ c.R1) := c.sup_R1_eq ▸ c.comp
  exact hMS G (L ⊔ c.R1) c.R1 L (c.isMSPair hN) hcomp c.coe_sup_R1
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

theorem commutator_Q_eq_F4 (hMS : C134L32Corr_F4)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ⁅pCoreOf 2 (L ⊔ T), L⁆ = V := by
  obtain ⟨i, hi⟩ := c.exists_c134Case_F4 hMS hN
  have hi5 : i = 5 := by
    by_contra h5
    rcases (by omega : i ≤ 4 ∨ 5 < i) with h | h
    · exact c.not_case_le_four hi h
    · revert hi
      unfold C134CorrLocal.IsC134CaseCorr
      split <;> first | omega | exact id
  subst hi5
  have h16 := c.card_c134Q_of_case5 hi
  have hVQ := c.V_le_c134Q
  have heq : V = c134Q (L ⊔ c.R1) L :=
    Subgroup.eq_of_le_of_card_ge hVQ (by rw [h16, c.card16]; norm_num)
  rw [heq]
  unfold c134Q
  rw [c.sup_R1_eq]

end Ctx

end N1246

end CFSG.Quasithin.H13
