module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamMain2
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDMain
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthFam

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

@[expose] def CrossFamBOrthEvenLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid),
    q.p ≠ 2 → 3 ≤ r →
    CrossAtOn ⟨.B r q, hv⟩ (fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r + 1) (q.p ^ q.exponent) p ∧ p ≤ r)

@[expose] def CrossFamDEvenLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid),
    CrossAtOn ⟨.D r q, hv⟩ (fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)

@[expose] def CrossFamTwistedDEvenLarge : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid),
    CrossAtOn ⟨.twistedD r q, hv⟩ (fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)

theorem crossFamBOrthLarge_of_even (h : CrossFamBOrthEvenLarge) : CrossFamBOrthLarge :=
  fun r q hv hq hr3 => crossAtOn_of_cover2
    (S₁ := fun p => OddOrderAt (q.p ^ q.exponent) p)
    (S₂ := fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r + 1) (q.p ^ q.exponent) p ∧ p ≤ r)
    (fun p hp => by
      by_cases h1 : OddOrderAt (q.p ^ q.exponent) p
      · exact Or.inl h1
      · exact Or.inr ⟨h1, hp⟩)
    (crossAtOn_B_odd hv) (h r q hv hq hr3)

theorem crossFamDLarge_of_even (h : CrossFamDEvenLarge) : CrossFamDLarge :=
  fun r q hv => crossAtOn_of_cover2
    (S₁ := fun p => OddOrderAt (q.p ^ q.exponent) p)
    (S₂ := fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)
    (fun p hp => by
      by_cases h1 : OddOrderAt (q.p ^ q.exponent) p
      · exact Or.inl h1
      · exact Or.inr ⟨h1, hp⟩)
    (crossAtOn_D_odd hv) (h r q hv)

theorem crossFamTwistedDLarge_of_even (h : CrossFamTwistedDEvenLarge) :
    CrossFamTwistedDLarge :=
  fun r q hv => crossAtOn_of_cover2
    (S₁ := fun p => OddOrderAt (q.p ^ q.exponent) p)
    (S₂ := fun p => ¬ OddOrderAt (q.p ^ q.exponent) p ∧
      ¬ AmbSmallAt (2 * r) (q.p ^ q.exponent) p ∧ p ≤ r)
    (fun p hp => by
      by_cases h1 : OddOrderAt (q.p ^ q.exponent) p
      · exact Or.inl h1
      · exact Or.inr ⟨h1, hp⟩)
    (crossAtOn_twistedD_odd hv) (h r q hv)

section Reduced


theorem kd29Cross_reduced_of_bcd_even (hU : CrossFamUnitaryLarge)
    (hBbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid),
      CrossAtOn ⟨.B r q, hv⟩ (fun p => r < p))
    (hCbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.C r q).Valid),
      CrossAtOn ⟨.C r q, hv⟩ (fun p => r < p))
    (hDbig : ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid),
      CrossAtOn ⟨.D r q, hv⟩ (fun p => r < p))
    (htDbig : ∀ (r : ℕ) (q : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid),
      CrossAtOn ⟨.twistedD r q, hv⟩ (fun p => r < p))
    (hBsp : CrossFamBSpLarge) (hBorth : CrossFamBOrthEvenLarge) (hCl : CrossFamCLarge)
    (hDl : CrossFamDEvenLarge) (htDl : CrossFamTwistedDEvenLarge) (hE6 : CrossFamE6)
    (htE6 : CrossFamTwistedE6) (hE7 : CrossFamE7) (hE8 : CrossFamE8) (hF4 : CrossSylowAbelianF4)
    (hG2 : CrossSylowAbelianG2) (htr : CrossSylowAbelianTrialityD4)
    (hRG : CrossSylowAbelianReeG2) (hRF : CrossSylowAbelianReeF4) : KD29Cross :=
  kd29Cross_reduced_of_large hU (crossFamB_of_large hBbig hBsp (crossFamBOrthLarge_of_even hBorth))
      (crossFamC_of_large hCbig hCl) (crossFamD_of_large hDbig (crossFamDLarge_of_even hDl))
      (crossFamTwistedD_of_large htDbig (crossFamTwistedDLarge_of_even htDl)) hE6 htE6 hE7 hE8 hF4
      hG2 htr hRG hRF

end Reduced

end CFSG.LocalAnalysis.RankFourTheoremC
