module

import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ree
public import CFSG.Open.LocalVocabulary
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

open scoped MatrixGroups

section


theorem exists_injective_psl_two_galoisField_to_ree {d : TauCeti.ValidLieTypeIndex} {m : ℕ}
    (hd : d.1 = .reeG2 m) :
    1 ≤ m ∧ ∃ f : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 (2 * m + 1)) →*
      (TauCeti.CFSGIndex.lie d).Group, Function.Injective f := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .reeG2 m := hd
  have ha : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  refine ⟨ha, ?_⟩
  haveI : CharP (GaloisField 3 (2 * m + 1)) CFSG.LieType.Ree.ReeTag.G2.prime :=
    inferInstanceAs (CharP (GaloisField 3 (2 * m + 1)) 3)
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  obtain ⟨ψ⟩ := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.nonempty_reeGamma_equiv hv
    (K := GaloisField 3 (2 * m + 1)) hK
  set J : CFSG.Walter.JT.JTHyp ↥(CFSG.LieType.Ree.ReeTag.G2.reeGamma
    (GaloisField 3 (2 * m + 1)) m) :=
    CFSG.Walter.Ree.Model.smallReeJTHyp ha hK
  exact ⟨ψ.symm.toMonoidHom.comp (J.F.subtype.comp J.iso.symm.toMonoidHom),
    ψ.symm.injective.comp (J.F.subtype_injective.comp J.iso.symm.injective)⟩

end

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
