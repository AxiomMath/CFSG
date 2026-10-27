module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1Pieces

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def KD264Y1ClsAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 3 → P d.1 → KD264Y1Fam d.1

@[expose] def KD264Y1IsLin (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .A n q

@[expose] def KD264Y1IsUni (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .twistedA n q

@[expose] def KD264Y1IsSym (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .B n q) ∨ (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .C n q)

@[expose] def KD264Y1IsOrthPlus (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .D n q

@[expose] def KD264Y1IsOrthMinus (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .twistedD n q

@[expose] def KD264Y1IsExc : TauCeti.LieTypeIndex → Prop
  | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .G2 _ | .twistedE6 _ | .trialityD4 _ | .suzuki _ | .reeG2 _ | .reeF4 _
  | .tits => True
  | _ => False

@[expose] def KD264Y1ClsLin : Prop := KD264Y1ClsAt KD264Y1IsLin

@[expose] def KD264Y1ClsUni : Prop := KD264Y1ClsAt KD264Y1IsUni

@[expose] def KD264Y1ClsSym : Prop := KD264Y1ClsAt KD264Y1IsSym

@[expose] def KD264Y1ClsOrthPlus : Prop := KD264Y1ClsAt KD264Y1IsOrthPlus

@[expose] def KD264Y1ClsOrthMinus : Prop := KD264Y1ClsAt KD264Y1IsOrthMinus

@[expose] def KD264Y1ClsExc : Prop := KD264Y1ClsAt KD264Y1IsExc

theorem kd264Y1Cls_of_families (hLin : KD264Y1ClsLin) (hUni : KD264Y1ClsUni) (hSym : KD264Y1ClsSym)
    (hOP : KD264Y1ClsOrthPlus) (hOM : KD264Y1ClsOrthMinus) (hExc : KD264Y1ClsExc) : KD264Y1Cls := by
  intro d _ hns hk2 hk3 hrk
  obtain ⟨d1, hd1⟩ := d
  cases d1 with
  | A n q => exact hLin ⟨_, hd1⟩ hns hk2 hk3 hrk ⟨n, q, rfl⟩
  | twistedA n q => exact hUni ⟨_, hd1⟩ hns hk2 hk3 hrk ⟨n, q, rfl⟩
  | B n q => exact hSym ⟨_, hd1⟩ hns hk2 hk3 hrk (Or.inl ⟨n, q, rfl⟩)
  | C n q => exact hSym ⟨_, hd1⟩ hns hk2 hk3 hrk (Or.inr ⟨n, q, rfl⟩)
  | D n q => exact hOP ⟨_, hd1⟩ hns hk2 hk3 hrk ⟨n, q, rfl⟩
  | twistedD n q => exact hOM ⟨_, hd1⟩ hns hk2 hk3 hrk ⟨n, q, rfl⟩
  | E6 q => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | E7 q => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | E8 q => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | F4 q => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | G2 q => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | twistedE6 q => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | trialityD4 q => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | suzuki m => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | reeG2 m => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | reeF4 m => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial
  | tits => exact hExc ⟨_, hd1⟩ hns hk2 hk3 hrk trivial

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
