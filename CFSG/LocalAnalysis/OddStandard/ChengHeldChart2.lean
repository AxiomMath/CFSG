module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartFrame
public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartPure

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

section Assembly2

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {d : Datum A}
  {P : Pos d} (F : FrameData P 2)

theorem act2_S (hC : ChCoverParts) (hstd : ∀ a b : ZMod 4, zz P.l a b = 1 ↔ b.val % 2 = 0)
    {k : ℕ} (hk : k < 3) {y : G} {hy : y ∈ d.X} (hp : Pure d P.l (k + 1) y hy) :
    ∀ e ∈ act2Rels k, cS d y hy (F.p e.1) = evalE F.p e.2 := by
  intro e he
  apply jS_injective d
  rw [jS_cS, F.hp, jS_evalE F]
  exact act2_nfM hC.act2 P.isQ hstd hk (β := betaHat A (d.X_sylow.le hy)) hp e he

theorem act2_G (hC : ChCoverParts) (hstd : ∀ a b : ZMod 4, zz P.l a b = 1 ↔ b.val % 2 = 0)
    {k : ℕ} (hk : k < 3) {y : G} {hy : y ∈ d.X} (hp : Pure d P.l (k + 1) y hy) :
    ∀ e ∈ act2Rels k,
      cj (((F.p e.1 : ↥d.S)) : G) y = evalE (fun i => ((F.p i : ↥d.S) : G)) e.2 := by
  intro e he
  have h1 := evalE_map d.S.subtype F.p e.2
  simp only [Subgroup.coe_subtype] at h1
  rw [cj_coe d y hy (F.p e.1), act2_S F hC hstd hk hp e he, h1]

end Assembly2

end CFSG.OddStandard.ChengHeld.M1b

