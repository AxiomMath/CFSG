module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Spor
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure KD264Res : Prop where
  spor : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264SporS p
  lie : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264KLie p

section KD264Asm


theorem kd264K_of_res (h : KD264Res) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264K p :=
  kd264K_of_parts (kd264KAlt_holds p hp hp2) (kd264KSpor_of_S p hp hp2 (h.spor p hp hp2)) (h.lie p hp hp2)

theorem i264At_of_res (h : KD264Res) (G : Type) [Group G] [Finite G] (p : ℕ) : I264At G p := by
  unfold I264At
  intro hp hp2
  have h264 := i264At_of_K (G := G) (kd264K_of_res h p hp hp2)
  unfold I264At at h264
  exact h264 hp hp2

end KD264Asm

end CFSG.LocalAnalysis.GLTheoremA
