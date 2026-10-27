module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2FamB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Out
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Fam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem hchar_of_two {d : ValidLieTypeIndex} {p : ℕ} (hd : d.1.characteristic = 2) (hp2 : p ≠ 2) :
    p ≠ d.1.characteristic := by
  rw [hd]
  exact hp2

theorem card_of_p_two {q : PrimePower} (hq2 : q.p = 2) : q.card = 2 ^ q.exponent := by
  rw [PrimePower.card_def, hq2]

section Mixed

variable (ctx : LvCtx) (hK3 : K3NotChev2At) (hN1 : KD264OutCyc) (hN2 : KD264OuterIdx) (p : ℕ)

include ctx hK3 hN1 hN2

theorem kDescFamRes_linear_aux (htd : Td4Ob p fLinear) (hN3 : KD264InnGood) (hPL : KD264PL 3)
    (hL : LinearRes) : KDescFamRes p fLinear := by
  refine kDescFamRes_of_solves hK3 ?_ htd
  intro hp hp2 S _ _ h hlv
  obtain ⟨n, q, hv, hq2, hne, ⟨e⟩⟩ := fam_linear h
  have hx := lv_idx ctx hp hp2 ⟨.A n q, hv⟩ (by simpa using hq2) e hlv
  simp [ExcT, tagOf, dimOf] at hx
  obtain ⟨rfl, hn⟩ := hx
  refine ⟨⟨.A n q, hv⟩, ⟨e⟩, ?_⟩
  rcases hn with rfl | ⟨rfl, hev⟩
  · exact solvesAt_A1 hN1 hN2 hv hq2 (fun h8 => hne ⟨rfl, h8⟩)
  · obtain ⟨hlp, hc1⟩ := hL q hv hq2 hev
    have hq4 : q.card ≠ 2 := by
      obtain ⟨m, hm⟩ := hev
      have hpos := q.exponent_pos
      have h2e : 2 ≤ q.exponent := by omega
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2e
      rw [card_of_p_two hq2]
      omega
    refine solvesAt_of_goodSub _ (goodSub_one_of_inputs' _ hp hp2 hN2 hN3 hPL
      (hchar_of_two (char_A hq2) hp2) ?_ h5_of_three ?_ htits_of_three hlp) hc1
    · rintro ⟨-, ⟨q', hq' | hq', -⟩ | ⟨q', hq'⟩⟩ <;> simp at hq'
    · rintro ⟨-, hov⟩
      exact hq4 (by simpa [ov2Idx, fieldSize] using hov)

theorem kDescFamRes_unitary_aux (htd : Td4Ob p fUnitary) (hN3 : KD264InnGood) (hPL : KD264PL 3)
    (hLow : KD264LiftLow 3) (hU : UnitaryRes) :
    KDescFamRes p fUnitary := by
  refine kDescFamRes_of_solves hK3 ?_ htd
  intro hp hp2 S _ _ h hlv
  obtain ⟨n, q, hv, hq2, hne8, hne32, hne42, ⟨e⟩⟩ := fam_unitary h
  have hx := lv_idx ctx hp hp2 ⟨.twistedA n q, hv⟩ (by simpa using hq2) e hlv
  simp [ExcT, tagOf, dimOf] at hx
  refine ⟨⟨.twistedA n q, hv⟩, ⟨e⟩, ?_⟩
  have hcard := card_of_p_two hq2
  have hchar : (LieTypeIndex.twistedA n q).characteristic = 2 := by simpa using hq2
  rcases hx with ⟨rfl, hq1⟩ | ⟨rfl, hs⟩
  · exact absurd ⟨rfl, by rw [hcard, hq1]; norm_num⟩ hne32
  · rcases hs with ⟨rfl, hodd⟩ | ⟨rfl, hq3⟩ | ⟨rfl, hq1⟩ | ⟨rfl, hq1⟩
    · obtain ⟨hlp, hc1⟩ := hU.1 q hv hq2 hodd (fun h8 => hne8 ⟨rfl, h8⟩)
      have h3le : 3 ≤ q.card :=
        ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).2 rfl
      refine solvesAt_of_goodSub _ (goodSub_one_of_inputs' _ hp hp2 hN2 hN3 hPL
        (hchar_of_two hchar hp2) ?_ h5_of_three ?_ htits_of_three hlp) hc1
      · rintro ⟨-, ⟨q', hq' | hq', hq'8⟩ | ⟨q', hq'⟩⟩
        · simp at hq'
        · have : q = q' := by injection hq'
          subst this
          exact hne8 ⟨rfl, hq'8⟩
        · simp at hq'
      · rintro ⟨-, hov⟩
        have : q.card = 2 := by simpa [ov2Idx, fieldSize] using hov
        omega
    · have hq8 : q.card = 8 := by rw [hcard, hq3]; norm_num
      have hlp : LpEpsNoGoodTwoLocal 3 ⟨.twistedA 3 q, hv⟩ := by
        rintro ⟨q', ⟨hq', -⟩ | ⟨hq', -⟩⟩
        · simp at hq'
        · simp at hq'
      refine solvesAt_of_goodSub _ (goodSub_one_of_inputs' _ hp hp2 hN2 hN3 hPL
        (hchar_of_two hchar hp2) ?_ h5_of_three ?_ htits_of_three hlp) (hU.2.1 q hv hq8)
      · rintro ⟨-, ⟨q', hq' | hq', -⟩ | ⟨q', hq'⟩⟩ <;> simp at hq'
      · rintro ⟨-, hov⟩
        have : q.card = 2 := by simpa [ov2Idx, fieldSize] using hov
        omega
    · exact absurd ⟨rfl, by rw [hcard, hq1]; norm_num⟩ hne42
    · have hq2c : q.card = 2 := by rw [hcard, hq1]; norm_num
      obtain ⟨g1, g2⟩ := hU.2.2 q hv hq2c
      exact solvesAt_of_goodSubLow hLow _ g1 g2

end Mixed

section SmallGroups

variable (ctx : LvCtx) (hK3 : K3NotChev2At) (hN1 : KD264OutCyc) (hN2 : KD264OuterIdx) (p : ℕ)

include ctx hK3 hN1 hN2

theorem kDescFamRes_symplectic_aux (htd : Td4Ob p fSymplectic)
    (hout : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid), q.p = 2 →
      OutAbelianAt ⟨.B 2 q, hv⟩) (hS : SymplecticRes) : KDescFamRes p fSymplectic := by
  refine kDescFamRes_of_solves hK3 ?_ htd
  intro hp hp2 S _ _ h hlv
  obtain ⟨n, q, hv, hq2, hne, ⟨e⟩⟩ := fam_symplectic h
  have hx := lv_idx ctx hp hp2 ⟨.B n q, hv⟩ (by simpa using hq2) e hlv
  simp [ExcT, tagOf, dimOf] at hx
  obtain ⟨rfl, hs⟩ := hx
  refine ⟨⟨.B n q, hv⟩, ⟨e⟩, ?_⟩
  have hcard := card_of_p_two hq2
  have hchar : (LieTypeIndex.B n q).characteristic = 2 := by simpa using hq2
  rcases hs with ⟨rfl, hq3⟩ | ⟨rfl, hq1⟩
  · have hq8 : q.card = 8 := by rw [hcard, hq3]; norm_num
    refine solvesAt_rankOne hN1 hN2 _ (hchar_of_two hchar hp2) ?_ h5_of_three (hout q hv hq2)
      (hS q hv hq2 hq8)
    rintro ⟨-, ⟨q', hq' | hq', -⟩ | ⟨q', hq'⟩⟩ <;> simp at hq'
  · exact absurd ⟨rfl, by rw [hcard, hq1]; norm_num⟩ hne

theorem kDescFamRes_g2_aux (htd : Td4Ob p fG2)
    (hout : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 → OutAbelianAt ⟨.G2 q, hv⟩)
    (hG : G2Res) : KDescFamRes p fG2 := by
  refine kDescFamRes_of_solves hK3 ?_ htd
  intro hp hp2 S _ _ h hlv
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_g2 h
  have hx := lv_idx ctx hp hp2 ⟨.G2 q, hv⟩ (by simpa using hq2) e hlv
  simp [ExcT, tagOf, dimOf] at hx
  obtain ⟨rfl, hq3⟩ := hx
  refine ⟨⟨.G2 q, hv⟩, ⟨e⟩, ?_⟩
  have hq8 : q.card = 8 := by rw [card_of_p_two hq2, hq3]; norm_num
  have hchar : (LieTypeIndex.G2 q).characteristic = 2 := by simpa using hq2
  refine solvesAt_rankOne hN1 hN2 _ (hchar_of_two hchar hp2) ?_ h5_of_three (hout q hv hq2)
    (hG q hv hq2 hq8)
  rintro ⟨-, ⟨q', hq' | hq', -⟩ | ⟨q', hq'⟩⟩ <;> simp at hq'

theorem kDescFamRes_reeTits_aux (htd : Td4Ob p fReeTits)
    (hout : ∀ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid), OutAbelianAt ⟨.reeF4 m, hv⟩)
    (hR : ReeTitsRes) : KDescFamRes p fReeTits := by
  refine kDescFamRes_of_solves hK3 ?_ htd
  intro hp hp2 S _ _ h hlv
  obtain ⟨m, hv, ⟨e⟩⟩ := fam_reeTits h
  have hx := lv_idx ctx hp hp2 ⟨.reeF4 m, hv⟩ (by simp) e hlv
  simp [ExcT, tagOf, dimOf] at hx
  refine ⟨⟨.reeF4 m, hv⟩, ⟨e⟩, ?_⟩
  have hchar : (LieTypeIndex.reeF4 m).characteristic = 2 := by simp
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
  · refine solvesAt_rankOne hN1 hN2 _ (hchar_of_two hchar hp2) ?_ h5_of_three (hout 1 hv)
      (hR.1 hv)
    rintro ⟨-, ⟨q', hq' | hq', -⟩ | ⟨q', hq'⟩⟩ <;> simp at hq'
  · have hm2 : m = 2 := by omega
    subst hm2
    refine solvesAt_rankOne hN1 hN2 _ (hchar_of_two hchar hp2) ?_ ?_ (hout 2 hv) (hR.2 hv)
    · rintro ⟨h3, -⟩
      omega
    · rintro ⟨-, h'⟩
      simp at h'

end SmallGroups

section TriD4

variable (ctx : LvCtx) (hK3 : K3NotChev2At) (hT : TD4Alt) (p : ℕ)

include ctx hK3 hT

theorem kDescFamRes_triD4_aux : KDescFamRes p fTriD4 := by
  refine kDescFamRes_of_solves hK3 ?_ (htd_of_alt hT)
  intro hp hp2 S _ _ h hlv
  obtain ⟨q, hv, hq2, hne, ⟨e⟩⟩ := fam_triD4 h
  have hx := lv_idx ctx hp hp2 ⟨.trialityD4 q, hv⟩ (by simpa using hq2) e hlv
  simp [ExcT, tagOf, dimOf] at hx
  obtain ⟨-, hq1⟩ := hx
  exact absurd (by rw [card_of_p_two hq2, hq1]; norm_num) hne

end TriD4

end CFSG.LocalAnalysis.GLTheoremA.HDesc
