module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.Alt
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.M22
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L2
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L3
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


private theorem kdClub_u3_at (c e : ℕ) [Fact c.Prime] (he : e ≠ 0)
    (hq : (c ^ e) % 9 = 2 ∨ (c ^ e) % 9 = 5) (hq2 : c ^ e ≠ 2) :
    KDClubAt (StatedProj (StatedSU (2 + 1) (c ^ e) (GaloisField c (2 * e)))) := by
  have hK : Nat.card (GaloisField c (2 * e)) = (c ^ e) ^ 2 := by
    rw [GaloisField.card c (2 * e) (by omega), pow_mul']
  exact kdClubAt_u3 (GaloisField c (2 * e)) (c ^ e) hK hq hq2

theorem kdClub_holds : KDClub := by
  refine kdClub_of_at fun i hi => ?_
  cases i with
  | cyclic p hp => simp [clubIndex, excIndex] at hi
  | alternating n h =>
    have hn : n = 5 ∨ n = 6 ∨ n = 7 := by
      simp only [clubIndex, excIndex] at hi
      omega
    exact kdClubAt_alternating n hn
  | sporadic s =>
    have hs : s = .M22 := by
      simpa [clubIndex, excIndex] using hi
    subst hs
    exact kdClubAt_m22
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d
    case A r q =>
      rcases r with _ | _ | _ | r
      · simp [clubIndex, excIndex] at hi
      ·
        have hi1 : q.card % 3 ≠ 0 ∧ q.card % 9 ≠ 1 ∧ q.card % 9 ≠ 8 := by
          simpa [clubIndex, excIndex] using hi
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
        letI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
        have hc : Fintype.card (GaloisField q.p q.exponent) = q.card :=
          (Nat.card_eq_fintype_card).symm.trans hK
        have e := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
            (GaloisField q.p q.exponent))
        exact kdClubAt_congr e.symm
          (kdClubAt_l2 (GaloisField q.p q.exponent)
            (by rw [hc]; exact hi1.1) (by rw [hc]; exact hi1.2.1) (by rw [hc]; exact hi1.2.2))
      ·
        have hi2 : q.card % 9 = 4 ∨ q.card % 9 = 7 := by
          simpa [clubIndex, excIndex] using hi
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
        have e := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
            (GaloisField q.p q.exponent))
        exact kdClubAt_congr e.symm
          (kdClubAt_l3 (GaloisField q.p q.exponent) (by rw [hK]; exact hi2))
      · simp [clubIndex, excIndex] at hi
    case twistedA r q =>
      rcases r with _ | _ | _ | r
      · simp [clubIndex, excIndex] at hi
      · simp [clubIndex, excIndex] at hi
      ·
        have hi2 : q.card % 9 = 2 ∨ q.card % 9 = 5 := by
          simpa [clubIndex, excIndex] using hi
        have hq3 : 3 ≤ q.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
        have hchar : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
          TauCeti.LieTypeIndex.characteristic_twistedA 2 q
        have hexp : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
          TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
        have e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
        exact kdClubAt_congr e.symm
          (kdClub_u3_at (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
            (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩)
            (by rw [hexp]; exact q.exponent_pos.ne')
            (by rw [hchar, hexp, ← TauCeti.PrimePower.card_def]; exact hi2)
            (by rw [hchar, hexp, ← TauCeti.PrimePower.card_def]; omega))
      · simp [clubIndex, excIndex] at hi
    all_goals simp [clubIndex, excIndex] at hi

theorem i1411At_holds {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) : I1411At G p :=
  i1411At_of_kdClub kdClub_holds hp

end CFSG.LocalAnalysis.GLTheoremA
