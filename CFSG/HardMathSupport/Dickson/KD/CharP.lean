module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.Exc
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.ClassA1
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.ClassC
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.ClassOrth
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.ClassTwistedA
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels

public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

@[expose] def IsClassicalLieIndex : TauCeti.LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ => True
  | _ => False

@[expose] def KDCharPClassical (p : ℕ) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), IsClassicalLieIndex d.1 → d.1.characteristic = p →
    KDCharPAt p (TauCeti.CFSGIndex.lie d).Group

theorem kdCharPClassical_holds {p : ℕ} (hp2 : p ≠ 2) : KDCharPClassical p := by
  intro d hcl hch
  obtain ⟨idx, hv⟩ := d
  have hch' : idx.characteristic = p := hch
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases idx with
  | A r q =>
    have hpq : p = q.p := by simpa using hch'.symm
    rcases Nat.lt_or_ge r 2 with hr | hr
    · obtain rfl : r = 1 := by have := hrange.1; omega
      exact kdCharPAt_A_one q hv hp2 hpq
    · exact kdCharPAt_A q r hv hr hp2 hpq
  | twistedA r q =>
    exact kdCharPAt_twistedA q r hv hp2 (by simpa using hch'.symm)
  | B r q =>
    have hpq : p = q.p := by simpa using hch'.symm
    rcases Nat.lt_or_ge r 3 with hr | hr
    · obtain rfl : r = 2 := by have := hrange.1; omega
      exact kdCharPAt_B_two q hv hp2 hpq
    · exact kdCharPAt_B q r hv hr hp2 hpq
  | C r q => exact kdCharPAt_C q r hv hp2 (by simpa using hch'.symm)
  | D r q => exact kdCharPAt_D q r hv hp2 (by simpa using hch'.symm)
  | twistedD r q => exact kdCharPAt_twistedD q r hv hp2 (by simpa using hch'.symm)
  | E6 q => exact absurd hcl id
  | E7 q => exact absurd hcl id
  | E8 q => exact absurd hcl id
  | F4 q => exact absurd hcl id
  | G2 q => exact absurd hcl id
  | twistedE6 q => exact absurd hcl id
  | trialityD4 q => exact absurd hcl id
  | suzuki m => exact absurd hcl id
  | reeG2 m => exact absurd hcl id
  | reeF4 m => exact absurd hcl id
  | tits => exact absurd hcl id

theorem kdCharP_of_classical {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcl : KDCharPClassical p) :
    KDCharP p := by
  intro d hch u hu
  obtain ⟨idx, hv⟩ := d
  have hch' : idx.characteristic = p := hch
  cases idx with
  | A r q => exact hcl ⟨_, hv⟩ trivial hch' u hu
  | twistedA r q => exact hcl ⟨_, hv⟩ trivial hch' u hu
  | B r q => exact hcl ⟨_, hv⟩ trivial hch' u hu
  | C r q => exact hcl ⟨_, hv⟩ trivial hch' u hu
  | D r q => exact hcl ⟨_, hv⟩ trivial hch' u hu
  | twistedD r q => exact hcl ⟨_, hv⟩ trivial hch' u hu
  | E6 q => exact kdCharPAt_E6 q hv hp2 (by simpa using hch'.symm) u hu
  | E7 q => exact kdCharPAt_E7 q hv hp2 (by simpa using hch'.symm) u hu
  | E8 q => exact kdCharPAt_E8 q hv hp2 (by simpa using hch'.symm) u hu
  | F4 q => exact kdCharPAt_F4 q hv hp hp2 (by simpa using hch'.symm) u hu
  | G2 q => exact kdCharPAt_G2 q hv hp hp2 (by simpa using hch'.symm) u hu
  | twistedE6 q => exact kdCharPAt_twistedE6 q hv (by simpa using hch'.symm) u hu
  | trialityD4 q => exact kdCharPAt_trialityD4 q hv hp2 (by simpa using hch'.symm) u hu
  | reeG2 m => exact kdCharPAt_reeG2 m hv (by simpa using hch'.symm) u hu
  | suzuki m => exact absurd (by simpa using hch'.symm) hp2
  | reeF4 m => exact absurd (by simpa using hch'.symm) hp2
  | tits => exact absurd (by simpa using hch'.symm) hp2

theorem kdCharP_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KDCharP p :=
  kdCharP_of_classical hp hp2 (kdCharPClassical_holds hp2)

end CFSG.HardMathSupport.Dickson.KD
