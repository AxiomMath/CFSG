module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B4a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_SM5_le_NM5 (c : Ctx7 G L) (hb : B5Std c) :
    SM5 c.e ≤ normalizer (M5 c.e : Set G) := by
  change c.s.fr.S ⊔ M5 c.e ≤ normalizer (M5 c.e : Set G)
  exact sup_le (c.s.S_le_R.trans (y7b_R_le_NM5 c hb)) Subgroup.le_normalizer

theorem y7b_SM5_comm_sq (c : Ctx7 G L) (hb : B6Std c) :
    (∀ w ∈ SM5 c.e, ∀ w' ∈ SM5 c.e, ⁅w, w'⁆ ∈ M5 c.e) ∧ ∀ w ∈ SM5 c.e, w ^ 2 ∈ M5 c.e := by
  rw [y7b_SM5_eq c hb.toB5Std]
  have hn₁ : AM5 c.e ≤ normalizer (BM5 c.e : Set G) :=
    (y7b_AM5_le_SM5 c).trans
      (le_normalizer_of_relIndex_two (y7b_BM5_le_SM5 c hb.toB5Std)
        (y7b_relIndex_BM5_SM5 c hb))
  have hn₂ : BM5 c.e ≤ normalizer (AM5 c.e : Set G) :=
    (y7b_BM5_le_SM5 c hb.toB5Std).trans
      (le_normalizer_of_relIndex_two (y7b_AM5_le_SM5 c)
        (y7b_relIndex_AM5_SM5 c hb))
  exact comm_sq_mem_sup_of_relIndex_two (y7b_M5_le_AM5 c) (y7b_M5_le_BM5 c)
    (y7b_relIndex_M5_AM5 c hb) (y7b_relIndex_M5_BM5 c hb) (y7b_AM5_inf_BM5 c hb) hn₁ hn₂

theorem y7b_X76_le_NAM5 (c : Ctx7 G L) (hb : B6Std c) :
    X76 c.e ≤ normalizer (AM5 c.e : Set G) := by
  intro x hx
  rw [← y7b_R5_inf_cs c hb.toB5Std]
  exact mem_normalizer_inf hx.1.1.1 (mem_normalizer_centralizerSection hx.1.1.2 hx.1.2)

theorem y7b_X76_le_NBM5 (c : Ctx7 G L) (hb : B6Std c) :
    X76 c.e ≤ normalizer (BM5 c.e : Set G) := by
  intro x hx
  rw [← y7b_R5_inf_cV2 c hb]
  exact mem_normalizer_inf hx.1.1.1 (mem_normalizer_centralizer hx.2)

theorem y7b_X76_le_NSM5 (c : Ctx7 G L) (hb : B6Std c) :
    X76 c.e ≤ normalizer (SM5 c.e : Set G) := by
  intro x hx
  rw [y7b_SM5_eq c hb.toB5Std]
  exact mem_normalizer_sup (y7b_X76_le_NAM5 c hb hx) (y7b_X76_le_NBM5 c hb hx)

end CFSG.OddStandard.HigherRank.YamadaG23
