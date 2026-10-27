module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Set

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Seven

variable {X : Type} [Group X] [Finite X] {h h' : Hyp52 X} {y : X}

theorem Prop62Output.secCond (hrel : Prop62Output h h' y) : h'.SecCond y := by
  obtain ⟨-, -, hB', -, -, -, hQ0, hyQ, hyP, hyT, hy2, -, -⟩ := hrel
  have hQ0' : h'.Q ≤ h'.secG0 y := by
    show h'.Q ≤ normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X)
    rw [hB']
    exact hQ0
  exact ⟨hyP, hyT, hy2, hQ0', hyQ⟩

theorem Prop62Output.maximal (hrel : Prop62Output h h' y)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) :
    GSMaximalUnbalancingTriple h'.a h'.x h'.J := by
  obtain ⟨ha', hJ', -, -, ⟨c, hcmem, -, hx'c⟩, -⟩ := hrel
  rw [ha', hx'c, hJ']
  exact ⟨gsUnbalancingTriple_conj hmax.1 (mem_inf.mp hcmem).1 (mem_inf.mp hcmem).2, hmax.2⟩

end Seven

end CFSG.ComponentClassification.GSThmB
