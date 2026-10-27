module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankOrthField
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def HqSixIdx (q : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A n Q => Q.p = q ∧ (8 ≤ n ∨ (4 ≤ n ∧ 3 ≤ Q.exponent))
  | .twistedA n Q => Q.p = q ∧ (8 ≤ n ∨ (4 ≤ n ∧ 3 ≤ Q.exponent))
  | .B n Q => Q.p = q ∧ (4 ≤ n ∨ (n = 3 ∧ 3 ≤ Q.exponent))
  | .D n Q => Q.p = q ∧ (5 ≤ n ∨ (n = 4 ∧ 3 ≤ Q.exponent))
  | .twistedD n Q => Q.p = q ∧ (5 ≤ n ∨ (n = 4 ∧ 3 ≤ Q.exponent))
  | _ => False

theorem six_le_twoLocalRank_of_field
    (hA : ∀ {n : ℕ}, 4 ≤ n → ∀ (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A n Q).Valid),
      Q.p ≠ 2 → 3 ≤ Q.exponent → ∀ {X : Type} [Group X] [Finite X]
        (φ : X →* (TauCeti.CFSGIndex.lie ⟨.A n Q, hv⟩).Group), Function.Surjective φ →
          6 ≤ GLATwoLocalRank Q.p X)
    (hU : ∀ {n : ℕ}, 4 ≤ n → ∀ (Q : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid), Q.p ≠ 2 → 3 ≤ Q.exponent →
        ∀ {X : Type} [Group X] [Finite X]
          (φ : X →* (TauCeti.CFSGIndex.lie ⟨.twistedA n Q, hv⟩).Group), Function.Surjective φ →
            6 ≤ GLATwoLocalRank Q.p X)
    {q : ℕ} (hq2 : q ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : HqSixIdx q d.1) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie d).Group) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank q X := by
  obtain ⟨d, hv⟩ := d
  cases d <;> simp only [HqSixIdx] at hd
  case A n Q =>
    obtain ⟨rfl, h | ⟨h4, hr⟩⟩ := hd
    · exact six_le_twoLocalRank_A h Q hv hq2 φ hφ
    · exact hA h4 Q hv hq2 hr φ hφ
  case twistedA n Q =>
    obtain ⟨rfl, h | ⟨h4, hr⟩⟩ := hd
    · exact six_le_twoLocalRank_twistedA h Q hv hq2 φ hφ
    · exact hU h4 Q hv hq2 hr φ hφ
  case B n Q =>
    obtain ⟨rfl, h | ⟨rfl, hr⟩⟩ := hd
    · exact six_le_twoLocalRank_B h Q hv hq2 φ hφ
    · exact six_le_twoLocalRank_B_field le_rfl Q hv hq2 hr φ hφ
  case D n Q =>
    obtain ⟨rfl, h | ⟨rfl, hr⟩⟩ := hd
    · exact six_le_twoLocalRank_D h Q hv hq2 φ hφ
    · exact six_le_twoLocalRank_D_field le_rfl Q hv hq2 hr φ hφ
  case twistedD n Q =>
    obtain ⟨rfl, h | ⟨rfl, hr⟩⟩ := hd
    · exact six_le_twoLocalRank_twistedD h Q hv hq2 φ hφ
    · exact six_le_twoLocalRank_twistedD_field le_rfl Q hv hq2 hr φ hφ

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
