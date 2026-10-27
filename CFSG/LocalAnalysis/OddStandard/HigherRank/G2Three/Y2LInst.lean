module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank

@[expose] def Lemma26Pres2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsExt26 2 X → ∀ P : Sylow 2 X,
    ∃ (e : Bool) (u v w r s : ↥P), IsPres26 2 e ↥P u v w r s ∧
      closure {(u : X), (v : X), (w : X)} = pCoreOf 2 (⊤ : Subgroup X)

@[expose] def Lemma26HS : Prop :=
  ∀ (P : Type) [Group P] (u v w r s : P), IsPres26 2 false P u v w r s → IsHSType P

@[expose] def Lemma27G23 : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (u v w r s : P), IsPres26 2 true P u v w r s →
    SecProp (⊤ : Subgroup P) (omega1 (closure {u, v, w})) (fun Y _ _ _ => IsG23Type Y)

end CFSG.OddStandard.HigherRank.G2Three.Sec2
