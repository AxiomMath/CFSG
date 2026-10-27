module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenNormality
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Interface
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.Yardstones.M67c2c3e09a6b.Definitions

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.HardMathSupport.Solomon.Coordinator.YS08

set_option linter.unusedSectionVars false

theorem lThreeFourComponentFacts_of_lieQ
    (hSpor : ∀ s, SporL3Down s) (hLie : LieL3Down) (h2 : LieQConstrained 2)
    (hodd : ∀ q : ℕ, q.Prime → 5 ≤ q → LieQConstrainedInner q) :
    CFSG.Yardstones.M67c2c3e09a6b.LThreeFourComponentFacts := by
  have hBT : ∀ q : ℕ, q.Prime → q ≠ 3 → LieQConstrainedInner q := by
    intro q hq hq3
    rcases eq_or_ne q 2 with rfl | hq2
    · exact LieQConstrainedInner.of_lieQConstrained h2
    · refine hodd q hq ?_
      have h2le := hq.two_le
      have hq4 : q ≠ 4 := by
        rintro rfl
        norm_num at hq
      omega
  exact ⟨⟨fun Y _ _ K hKq hKK b hb hb3 J hJ p hp hJL =>
      chev_of_branches (fun s => l3EpsSporBranch_of_down (hSpor s)) (l3EpsLieBranch_of_down hLie)
        Y K hKq hKK b hb hb3 J hJ p hp hJL,
    fun Y _ _ K A Q q hq hq3 hKq hChev hAK _ hmax hQc =>
      borelTits_of_constrainedInner hq (hBT q hq hq3) Y K A Q hKq hChev hAK hmax hQc⟩,
    ⟨fun Y _ _ K hKq hKK hK3 b hb hb3 J hJ hJL =>
      chevTwo_of_branches (fun s => l34SporBranch_of_down (hSpor s)) (l34LieBranch_of_down hLie)
        Y K hKq hKK hK3 b hb hb3 J hJ hJL,
    generation_of_faithful (genFaithful_of_parts
      (genNormality_of_semisimpleCent LieSemisimple.lieSemisimpleCent)
      (genCore_of_constrained h2))⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
