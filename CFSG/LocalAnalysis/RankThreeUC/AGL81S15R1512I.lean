module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.RowHyps
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankGe3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankEq2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512H

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open scoped commutatorElement

theorem row1513_gen (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hK541 : K541)
    (hK4a : K517_4a) (hK518 : K518) (hKParU5 : KParU5)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hLift : RowLifts G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h12 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1512Datum G M T T₁ T₂)
    (hsub : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.RowNotDvdSubOne G M T T₁ T₂) :
    Row1513 G M T T₁ T₂ := by
  intro p hp Ls L hLs hL h3
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp3 : p ≠ 3 := fun h => h11 (h ▸ hp)
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hpP (by decide)
  have hp5 : 5 ≤ p := by have := hpP.two_le; omega
  have hdat := h12 Ls L hLs hL
  have hodd := (centre_of_lift ctx.gn hLs.1 hL).2.2
  rcases hdat with ⟨d, hdr, hd, e, hr⟩ | ⟨n, hn, e, hr⟩ | ⟨n, hn, e, hr⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have h3' : 3 ≤ mRankChev d.1 p (Nat.card (Subgroup.center ↥(barO2 L))) := by
      rw [← hr p hpP hp2]; omega
    rcases rank_ge_three_of_in1512 hd hpP hp5 h3' with ⟨Q, hQ, hdv⟩ | ⟨Q, hQ, hdv⟩ |
      ⟨Q, hQ, hdv⟩ | ⟨Q, hQ, hc, hp5'⟩
    · exfalso
      exact hsub p hp hp5 Ls L hLs hL (by omega) d hdr hd
        (fun Q' h => by rw [hQ] at h; cases h) e (by rw [hQ]; exact hdv)
    · have hQp : Q.p = 2 := by rw [hQ] at hdr; exact hdr.1
      have hU : IsUFour (fun Q' => p ∣ Q' + 1) ↥Ls :=
        isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hLs.1.2.2 hodd hd
          (fun Q' h => by rw [hQ] at h; cases h) (fun Q' h => by rw [hQ] at h; cases h) e hQp hQ hdv
      obtain ⟨Is, hIs, hne, hpI⟩ :=
        exists_other_of_isUFour_gen hK4a hK518 hKSMU4 ctx hp hp5 hLs hL hU
      exact (false_of_other_component_isUFour_gen hT hKSMU4 hK541 ctx hLift hp hp5 hLs hL hU hIs
        hne hpI (h3 := ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11)).elim
    · have hQp : Q.p = 2 := by
        rcases hQ with hQ | hQ <;> (rw [hQ] at hdr; exact hdr.1)
      by_cases hsubQ : p ∣ Q.card - 1
      · exfalso
        refine hsub p hp hp5 Ls L hLs hL (by omega) d hdr hd
          (fun Q' h => by rcases hQ with hQ | hQ <;> (rw [hQ] at h; cases h)) e ?_
        rcases hQ with hQ | hQ <;> (rw [hQ]; exact hsubQ)
      · have hadd := dvd_add_one_of_dvd_sq_sub_one hpP (rank_ge_three_of_in1512_auxCard Q) hdv hsubQ
        rcases hQ with hQ | hQ
        · exact Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hLs.1.2.2 hodd hd
            (fun Q' h => by rw [hQ] at h; cases h) (fun Q' h => by rw [hQ] at h; cases h) e hQp hQ
            hadd)
        · exact Or.inr (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hLs.1.2.2 hodd hd
            (fun Q' h => by rw [hQ] at h; cases h) (fun Q' h => by rw [hQ] at h; cases h) e hQp hQ
            hadd)
    · exfalso
      have hQp : Q.p = 2 := by rw [hQ] at hdr; exact hdr.1
      have h5 : 5 ∈ sigmaM G M := hp5' ▸ hp
      rcases two_le_mN_of_u5 hKParU5 ctx.gn (S15CtxGen.good ctx) hLs.1 hQp hc hQ e with h | h
      · exact (Nat.not_lt.2 (ctx.rank_N₁ 5 h5)) h
      · exact (Nat.not_lt.2 (ctx.rank_N₂ 5 h5)) h
  · exfalso
    have h1 := hr p hpP hp2
    have h2 : n / p ≤ n / 5 := Nat.div_le_div_left hp5 (by norm_num)
    rcases hn with rfl | rfl <;> omega
  · exfalso
    have h1 := hr p hpP hp2
    have h2 : n / p ≤ n / 5 := Nat.div_le_div_left hp5 (by norm_num)
    rcases hn with rfl | rfl <;> omega
  · exfalso
    have := hr p hpP hp2
    split_ifs at this <;> omega
  · exfalso
    have := hr p hpP hp2
    split_ifs at this <;> omega

theorem row1513 (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    (hK541 : K541) (hK4a : K517_4a) (hK4b : K517_4b) (hK518 : K518) (hKParU5 : KParU5)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (hLift : RowLifts G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) :
    Row1513 G M T T₁ T₂ :=
  row1513_gen hT hKSMOdd hKSMU4 hK541 hK4a hK518 hKParU5
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx) hLift h11
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.row1512Datum_of_ctx2 hT ctx)
    (rowNotDvdSubOne_of_ctx2 hKSMOdd hKSMU4 hKSML3 hK4b ctx)

theorem row1514_gen (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂)
    (h12 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1512Datum G M T T₁ T₂)
    (hsub : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.RowNotDvdSubOne G M T T₁ T₂) :
    Row1514 G M T T₁ T₂ := by
  intro p hp Ls L hLs hL h2
  have hpP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp3 : p ≠ 3 := fun h => h11 (h ▸ hp)
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hpP (by decide)
  have hp5 : 5 ≤ p := by have := hpP.two_le; omega
  have hdat := h12 Ls L hLs hL
  have hodd := (centre_of_lift ctx.gn hLs.1 hL).2.2
  rcases hdat with ⟨d, hdr, hd, e, hr⟩ | ⟨n, hn, e, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have h2' : mRankChev d.1 p (Nat.card (Subgroup.center ↥(barO2 L))) = 2 := by
      rw [← hr p hpP hp2]; exact h2
    have hbad : ∀ {Q : TauCeti.PrimePower}, (d.1 = .A 2 Q ∨ d.1 = .twistedA 3 Q ∨ d.1 = .G2 Q ∨
        d.1 = .B 2 Q) → p ∣ indexQ d.1 - 1 → False := by
      intro Q hQ hdv
      exact hsub p hp hp5 Ls L hLs hL (by omega) d hdr hd
        (fun Q' h => by rcases hQ with hQ | hQ | hQ | hQ <;> (rw [hQ] at h; cases h)) e hdv
    rcases rank_eq_two_of_in1512 hd hpP hp5 h2' with ⟨Q, hQ, hdv⟩ | ⟨Q, hQ, hdv⟩ | ⟨Q, hQ, hdv⟩ |
      ⟨Q, hQ, hdv⟩ | ⟨Q, hQ, hc, hp7⟩
    · have hQp : Q.p = 2 := by
        rcases hQ with hQ | hQ
        · rw [hQ] at hdr; exact hdr
        · rw [hQ] at hdr; exact hdr.1
      by_cases hsubQ : p ∣ Q.card - 1
      · exfalso
        rcases hQ with hQ | hQ
        · exact hbad (Q := Q) (Or.inr (Or.inr (Or.inl hQ))) (by rw [hQ]; exact hsubQ)
        · exact hbad (Q := Q) (Or.inr (Or.inr (Or.inr hQ))) (by rw [hQ]; exact hsubQ)
      · have hadd := dvd_add_one_of_dvd_sq_sub_one hpP (rank_ge_three_of_in1512_auxCard Q) hdv hsubQ
        rcases hQ with hQ | hQ
        · exact Or.inl (Or.inl (Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hLs.1.2.2 hodd hd
            (fun Q' h => by rw [hQ] at h; cases h) (fun Q' h => by rw [hQ] at h; cases h) e hQp hQ
            hadd)))
        · exact Or.inl (Or.inr (Or.inl (Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4
            hLs.1.2.2 hodd hd (fun Q' h => by rw [hQ] at h; cases h)
            (fun Q' h => by rw [hQ] at h; cases h) e hQp hQ hadd))))
    · have hQp : Q.p = 2 := by rw [hQ] at hdr; exact hdr.1
      exact Or.inl (Or.inr (Or.inr (Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4
        hLs.1.2.2 hodd hd (fun Q' h => by rw [hQ] at h; cases h)
        (fun Q' h => by rw [hQ] at h; cases h) e hQp hQ hdv))))
    · exact (hbad (Q := Q) (Or.inr (Or.inl hQ)) (by rw [hQ]; exact hdv)).elim
    · exact (hbad (Q := Q) (Or.inl hQ) (by rw [hQ]; exact hdv)).elim
    · have hQp : Q.p = 2 := by rcases hQ with hQ | hQ <;> (rw [hQ] at hdr; exact hdr.1)
      refine Or.inr (Or.inl ⟨?_, hp7⟩)
      rcases hQ with hQ | hQ
      · exact Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hLs.1.2.2 hodd hd
          (fun Q' h => by rw [hQ] at h; cases h) (fun Q' h => by rw [hQ] at h; cases h) e hQp
          (f := TauCeti.LieTypeIndex.A (6 - 1)) (c := fun Q => Q = 2) hQ hc)
      · exact Or.inr (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hLs.1.2.2 hodd hd
          (fun Q' h => by rw [hQ] at h; cases h) (fun Q' h => by rw [hQ] at h; cases h) e hQp
          (f := TauCeti.LieTypeIndex.A (7 - 1)) (c := fun Q => Q = 2) hQ hc)
  · exfalso
    have h1 := hr p hpP hp2
    have h2' : n / p ≤ n / 5 := Nat.div_le_div_left hp5 (by norm_num)
    rcases hn with rfl | rfl <;> omega
  · have h1 := hr p hpP hp2
    rcases hn with rfl | rfl
    · exfalso
      have h2' : 7 / p ≤ 7 / 5 := Nat.div_le_div_left hp5 (by norm_num)
      omega
    · have hp6 : p ≤ 5 := by
        by_contra hlt
        have h2' : 10 / p ≤ 10 / 6 := Nat.div_le_div_left (by omega) (by norm_num)
        omega
      exact Or.inr (Or.inr ⟨⟨e⟩, by omega⟩)
  · exfalso
    have := hr p hpP hp2
    split_ifs at this <;> omega
  · exfalso
    have := hr p hpP hp2
    split_ifs at this <;> omega

theorem row1514 (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    (hK4b : K517_4b) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) : Row1514 G M T T₁ T₂ :=
  row1514_gen hKSMOdd hKSMU4 (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx)
    h11 (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.row1512Datum_of_ctx2 hT ctx)
    (rowNotDvdSubOne_of_ctx2 hKSMOdd hKSMU4 hKSML3 hK4b ctx)

end CFSG.LocalAnalysis.RankThreeUC.S15
