module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWSound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWChkE8a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWChkE8b

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.Sec6.Up34Exc


theorem exc3core_wobs_E8 {L : Type} [Field L] (a : Fin Tag.E8.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hn : (componentRoots (rootCharHom a) i).ncard = 72 ∨
      (componentRoots (rootCharHom a) i).ncard = 84) :
    exc3core_WObs Tag.E8 (rootCharHom a) (componentRoots (rootCharHom a) i) ∧
      ∀ i' : KernelComponent (rootCharHom a),
        (componentRoots (rootCharHom a) i').ncard = (componentRoots (rootCharHom a) i).ncard →
          i' = i := by
  have hcap : Tag.E8.artifactRoots.length < 241 := by decide +kernel
  have hlen : (RD.allVecs Tag.E8.rank).length ≤ 1641 * 4 := by decide +kernel
  have hchunks : ∀ j < 4, (((RD.allVecs Tag.E8.rank).drop (1641 * j)).take 1641).all
      (exc3core_eCheck .E8 241 exc3core_dngE8 exc3core_dngE8) = true := by
    intro j hj
    interval_cases j
    · simpa only [exc3core_wCheck] using exc3core_wCheck_E8_0
    · simpa only [exc3core_wCheck] using exc3core_wCheck_E8_1
    · simpa only [exc3core_wCheck] using exc3core_wCheck_E8_2
    · simpa only [exc3core_wCheck] using exc3core_wCheck_E8_3
  have h8 : ∀ d ∈ RD.allVecs Tag.E8.rank,
      exc3core_eCheck .E8 241 exc3core_dngE8 exc3core_dngE8 d = true := by
    intro d hd
    exact List.all_eq_true.1
      (exc3core_all_of_chunks (RD.allVecs Tag.E8.rank)
        (exc3core_eCheck .E8 241 exc3core_dngE8 exc3core_dngE8) 1641 4 (by norm_num) hlen
        hchunks) d hd
  have hu : exc3core_dngE8 (componentRoots (rootCharHom a) i).ncard = true := by
    rcases hn with h | h <;> simp [exc3core_dngE8, h]
  refine ⟨exc3core_wobs_of_check noG2_E8 241 exc3core_dngE8 exc3core_dngE8 hcap h8 a ha i hu hu, ?_⟩
  exact exc3core_unique_of_ker_lt (rootCharHom a) i
    (exc3core_ker_lt_of_check noG2_E8 241 exc3core_dngE8 exc3core_dngE8 hcap h8 a ha i hu)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
