module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossLinearOne
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossLinearThree
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossSuzuki
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossTits

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

@[expose] def CrossFamLinearGeThree : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A m q).Valid),
    CrossAt ⟨.A m q, hv⟩

theorem crossFamLinear_of_geThree (h : CrossFamLinearGeThree) : CrossFamLinear := by
  intro m q hv
  have h1 : 1 ≤ m :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  rcases Nat.lt_or_ge m 3 with hm | hm
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      exact crossAt_linearOne hv
    · obtain rfl : m = 2 := by omega
      exact crossAt_linearTwo hv
  · exact h m hm q hv

@[expose] def CrossFamUnitaryGeThree : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid), CrossAt ⟨.twistedA m q, hv⟩

theorem crossFamUnitary_of_geThree (h : CrossFamUnitaryGeThree) : CrossFamUnitary := by
  intro m q hv
  have h2 : 2 ≤ m := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases Nat.lt_or_ge m 3 with hm | hm
  · obtain rfl : m = 2 := by omega
    exact crossAt_unitaryTwo hv
  · exact h m hm q hv

@[expose] def CrossSylowAbelianF4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid),
    CrossSylowAbelianAt ⟨.F4 q, hv⟩

@[expose] def CrossSylowAbelianG2 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
    CrossSylowAbelianAt ⟨.G2 q, hv⟩

@[expose] def CrossSylowAbelianTrialityD4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    CrossSylowAbelianAt ⟨.trialityD4 q, hv⟩

@[expose] def CrossSylowAbelianReeG2 : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid), CrossSylowAbelianAt ⟨.reeG2 m, hv⟩

@[expose] def CrossSylowAbelianReeF4 : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid), CrossSylowAbelianAt ⟨.reeF4 m, hv⟩

section Reduced

theorem kd29Cross_reduced (hA : CrossFamLinearGeThree) (htA : CrossFamUnitaryGeThree)
    (hB : CrossFamB)
    (hC : CrossFamC) (hD : CrossFamD) (htD : CrossFamTwistedD) (hE6 : CrossFamE6)
    (htE6 : CrossFamTwistedE6) (hE7 : CrossFamE7) (hE8 : CrossFamE8) (hF4 : CrossSylowAbelianF4)
    (hG2 : CrossSylowAbelianG2) (htr : CrossSylowAbelianTrialityD4)
    (hRG : CrossSylowAbelianReeG2) (hRF : CrossSylowAbelianReeF4) : KD29Cross :=
  kd29Cross_of_families (crossFamLinear_of_geThree hA) (crossFamUnitary_of_geThree htA) hB hC hD
    htD hE6 htE6 hE7 hE8
    (fun q hv => crossAt_of_sylowAbelian (hF4 q hv))
    (fun q hv => crossAt_of_sylowAbelian (hG2 q hv))
    (fun q hv => crossAt_of_sylowAbelian (htr q hv))
    (fun m hv => crossAt_suzuki hv)
    (fun m hv => crossAt_of_sylowAbelian (hRG m hv))
    (fun m hv => crossAt_of_sylowAbelian (hRF m hv))
    crossFamTits

end Reduced

end CFSG.LocalAnalysis.RankFourTheoremC
