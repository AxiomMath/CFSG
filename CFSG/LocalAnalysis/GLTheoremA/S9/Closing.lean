module

public import CFSG.LocalAnalysis.GLTheoremA.S9.ClosingC

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure ClosingInputs (G : Type) [Group G] [Finite G] : Prop where
  rank23 : Rank23At G
  i81 : I81U5At G
  i2811 : I2811At G
  i102 : I102U4At G
  i183 : Input18_3_4
  i112 : I112RkAt G
  i1431 : I1431ClAt G
  table : U4TableAt G

theorem closing {G : Type} [Group G] [Finite G] {p q : ℕ} {B : Subgroup G} {x : G}
    {L Q₁ : Subgroup G} (hc : S9Ctx G p) (hin : ClosingInputs G) (hC : Contra92 p B x L q Q₁)
    (h96 : ∀ B' : Subgroup G, H92 p B' x L → Concl96 p B' x L Q₁) : False := by
  have hB : Concl96 p B x L Q₁ := h96 B hC.h
  have hp3 : p = 3 := hB.p_eq
  subst hp3
  have hrank : GLATwoLocalRank 3 G = 4 := by
    have h1 : 3 ^ GLATwoLocalRank 3 G = 3 ^ 4 := hC.h.bmax.2.1.symm.trans hB.card
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  obtain ⟨Bs, D, J, E₀, y, z, hcfg⟩ :=
    Cl.exists_cfg hc hin.rank23 hin.i81 hin.i2811 hin.i102 hC hB
  exact Cl.final_contra hc hrank hin.i183 hin.i112 hin.i1431 hin.table hC hB.center hcfg

end CFSG.LocalAnalysis.GLTheoremA.S9
