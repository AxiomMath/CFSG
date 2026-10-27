module

public import CFSG.LocalAnalysis.GLTheoremB.PiGenDefs
public import CFSG.LocalAnalysis.GL83PartI.I_27_9

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def OrthCentGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → LocalAnalysis.GLTheoremB.IsPiGroup p ↥K → IsOrthType p ↥K → ¬ IsAltType p ↥K →
      ∀ A : Subgroup X, IsElemAbelian p A → A ≤ Subgroup.normalizer (K : Set X) →
        K ≤ GL83.CompFam.centGenI p A K

theorem inputPiGenOrth_of_orthCentGen (h : OrthCentGen) : InputPiGenOrth := by
  intro X _ _ p hp hp2 K hK hPi hO hA B hB _
  have : Fact p.Prime := ⟨hp⟩
  exact GL83.PiGen.le_glbCore_of_centGenI hB hK
    (h X p hp hp2 K hK hPi hO hA (GL83.CompFam.stab B K) (GL83.CompFam.elem_mono hB inf_le_left)
      (GL83.PiGen.stab_le_normalizer B K))

end CFSG.HardMathSupport.Timmesfeld.Coordinator
