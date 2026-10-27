module

public import CFSG.LieType.AlgebraicGroups.KernelRootCentralizer
public import CFSG.LieType.Chevalley.E6CubicPointwiseStabilizer

public section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.Foote5.OddLieCore.Exc


theorem mem_torusGroup_of_mem_toralCentralizer_of_cubic_commute
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ) (ha : ∀ i, a i ^ 3 = 1)
    (ζ : Kˣ) (hζ : ζ ^ 2 ≠ 1)
    {z : ModGL Tag.E6 K} (hz : z ∈ toralCentralizer Tag.E6 K a)
    (hcomm : ∀ x ∈ rootSpan Tag.E6 K (kernelRoots (rootCharHom a)), Commute z x) :
    z ∈ torusGroup Tag.E6 K := by
  classical
  have hzAdj : z ∈ adjointGroup Tag.E6 K := hz.1
  obtain ⟨hfac, _, _, _⟩ := Chevalley_toral_centralizer_Bruhat_factors Tag.E6 K a
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hzfactor⟩ := hfac z hz
  have hh' : h ∈ torusGroup Tag.E6 K := hh
  apply mem_torusGroup_of_bruhat_factor_of_commute_kernelSpan a ζ hζ hzAdj hcomm
    hh' hu hv hzfactor
  intro hwfix
  apply E6CubicPointwiseStabilizer.eq_one_of_mem_rootCharStabilizer_of_fix_kernelRoots a ha hw
  intro beta hb
  rcases IsRoot.height_pos_or_neg hb.1 with hpos | hneg
  · exact hwfix beta ⟨hb, hpos⟩
  · have hn : -beta ∈ posRoots (kernelRoots (rootCharHom a)) :=
      ⟨neg_mem_rootCharKernel hb, by rw [height_neg]; omega⟩
    have hf := hwfix (-beta) hn
    simpa only [smul_neg, neg_inj] using hf

end CFSG.LieType.AlgebraicGroups
