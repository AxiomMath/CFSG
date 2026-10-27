module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.DefChar

@[expose] def TitsNoElemAbelian27 : Prop :=
  ∀ hv : TauCeti.LieTypeIndex.tits.Valid, ∀ D : Subgroup (MulAut (Cat ⟨.tits, hv⟩)),
    IsElemAbelian 3 D → Nat.card D ≠ 27

theorem crossCharFamAt_tits_three (h : TitsNoElemAbelian27) :
    CrossCharFamAt .tits fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ hd p hp hp2 _ hp3 D hD hcard H hH hDH
  have hd' : d = .tits := hd
  subst hd'
  subst hp3
  exact absurd (by rw [hcard]; norm_num) (h hv D hD)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
