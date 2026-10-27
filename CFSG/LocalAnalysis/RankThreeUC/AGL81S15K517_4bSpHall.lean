module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorelAll
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridgeAux

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem noXBlock_borelPre_subtype_sp
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : Nat) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hcard : 5 ≤ Q.card ∨ Q.card = 4) :
    ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  intro Y hsub hblock
  let Y' : Subgroup X := Y.map (borelPre T Ls).subtype
  have hY' : Y' ≤ borelPre T Ls := by
    simpa only [Y'] using Subgroup.map_subtype_le Y
  have hsub' : IsSubnormal Y' (borelPre T Ls) := by
    have h := hsub.map (borelPre T Ls).subtype
    simpa only [Y', Subgroup.map_top, Subgroup.range_subtype] using h
  have hblock' : InClassXBlock Y' := by
    have hx : CFSG.RankThree.PartOne.InClassX ↥Y :=
      CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hblock
    let eY : ↥Y ≃* ↥Y' :=
      Subgroup.equivMapOfInjective Y (borelPre T Ls).subtype
        (borelPre T Ls).subtype_injective
    have hx' : CFSG.RankThree.PartOne.InClassX ↥Y' :=
      CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv eY hx
    exact CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hx'
  exact noXBlock_borelPre_done_B hX hLs hinv m hm Q hQ hv e hcard Y' hY' hsub' hblock'

end CFSG.LocalAnalysis.RankThreeUC.S15

end
