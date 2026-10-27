module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512F
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515F
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankNT1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD CFSG.LocalAnalysis.AGL81TheoremCD.Section15

section Row1519

variable {X : Type} [Group X] [Finite X]

theorem pRank_le_of_lift {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hL : LiftOf T L Ls)
    {p : ℕ} (hp : p.Prime) (hC : ¬ p ∣ Nat.card (gnC T)) :
    CFSG.Open.pRank p Ls ≤ CFSG.Open.pRank p L := by
  rw [← hL.2]
  refine CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp _ ?_ L
  show ¬ p ∣ Nat.card (QuotientGroup.mk' (gnC T)).ker
  rw [QuotientGroup.ker_mk']
  exact hC

theorem exists_other_component_s15 {T T₁ T₂ : Subgroup X} {p : ℕ} (hp : p.Prime)
    {Ls : Subgroup (X ⧸ gnC T)} (hC : ¬ p ∣ Nat.card (gnC T))
    (hY : (∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ p ∣ Nat.card ↥Is) →
      pElementSubgroup p (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hX3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) (hLs2 : CFSG.Open.pRank p Ls ≤ 2) :
    ∃ Is : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Is ∧ Is ≠ Ls ∧ p ∣ Nat.card ↥Is := by
  by_contra hcon
  have hle := hY fun Is hIs hne hd => hcon ⟨Is, hIs, hne, hd⟩
  have h3 := pRank_le_pRank_of_le_comap_at hp hC hle
  omega

theorem shape_of_row1514 {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (h : ((IsGTwo (fun Q => p ∣ Q + 1) Y ∨ IsSpFour (fun Q => p ∣ Q + 1) Y ∨
            IsLFour (fun Q => p ∣ Q + 1) Y) ∨
          ((IsLinTwo 6 Y ∨ IsLinTwo 7 Y) ∧ p = 7) ∨
          (Nonempty (Y ≃* alternatingGroup (Fin 10)) ∧ p = 5)))
    (h17 : (IsLinTwo 6 Y ∨ IsLinTwo 7 Y) → p ≠ 7)
    (h16 : ¬ (Nonempty (Y ≃* alternatingGroup (Fin 10)) ∧ p = 5)) :
    ∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧ p ∣ Q.card + 1 ∧
      (d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  rcases h with (hG | hS | hL) | hl | hA
  · rcases hG with ⟨Q, hQ, hc, d, hd, ⟨e⟩⟩ | ⟨hc, -⟩
    · exact ⟨d, Q, hQ, hc, Or.inl hd, ⟨e⟩⟩
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hc) hp3
  · rcases hS with ⟨Q, hQ, hc, d, hd, ⟨e⟩⟩ | ⟨hc, -⟩
    · exact ⟨d, Q, hQ, hc, Or.inr (Or.inl hd), ⟨e⟩⟩
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hc) hp3
  · rcases hL with ⟨Q, hQ, hc, d, hd, ⟨e⟩⟩ | ⟨hc, -⟩
    · exact ⟨d, Q, hQ, hc, Or.inr (Or.inr hd), ⟨e⟩⟩
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hc) hp3
  · exact absurd hl.2 (h17 hl.1)
  · exact absurd hA h16

theorem lift_lie_data (hchev : LieOddRankChev) (hKSMOdd : KSMOdd) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hd : d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q)
    (e : Nonempty (↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (Subgroup.center ↥(barO2 L)) = 1 ∧ Nat.card (Subgroup.center ↥Ls) = 1 ∧
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L = mRankChev d.1 r 1 := by
  obtain ⟨e0⟩ := e
  have hZLs : Subgroup.center ↥Ls = ⊥ := centre_eq_bot_of_equiv_lie hLs.2.2 hQ hd e0
  have heq : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZLs).trans ((QuotientGroup.quotientBot).trans e0)⟩
  obtain ⟨⟨eQ⟩, -, hodd⟩ := centre_of_lift hX hLs hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hin : In1512 d.1 := by
    rcases hd with h | h | h <;> rw [h] <;> simpa [In1512] using hQ
  have h2 : ∀ Q', d.1 ≠ .A 2 Q' := by
    intro Q'
    rcases hd with h | h | h <;> rw [h] <;> intro hh <;> simp at hh
  have h3 : ∀ Q', d.1 ≠ .twistedA 3 Q' := by
    intro Q'
    rcases hd with h | h | h <;> rw [h] <;> intro hh <;> simp at hh
  have h4 : ∀ Q', d.1 ≠ .twistedA 4 Q' := by
    intro Q'
    rcases hd with h | h | h <;> rw [h] <;> intro hh <;> simp at hh
  have hZ1 : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
    (hKSMOdd.1 ↥(barO2 L) hK d hin h2 h3 ⟨eQ.trans heq.some⟩ (centre_barO2_odd hL.1)).2 h4
  refine ⟨hZ1, Subgroup.card_eq_one.2 hZLs, heq, fun r hr hr2 => ?_⟩
  have hcl : IsClassicalOrG2Index d.1 := by
    rcases hd with h | h | h <;> rw [h] <;> simpa [IsClassicalOrG2Index] using hQ
  have h1 := hchev ↥(barO2 L) hK d hcl ⟨eQ.trans heq.some⟩ r hr hr2
  rw [hZ1] at h1
  exact ((pRank_barO2_eq hL.1 hr hr2).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L))).trans h1

theorem two_le_mRankChev_three {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower}
    (hQ : Q.p = 2) (hd : d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q) (z : ℕ) :
    2 ≤ mRankChev d.1 3 z := by
  have hrt : IsRankTwoPlus d.1 := by
    rcases hd with h | h | h <;> rw [h] <;> simp [IsRankTwoPlus, hQ]
  obtain ⟨-, h2, h3, -⟩ := mRank3_cases hrt z
  rcases hd with h | h | h
  · have := h2.2 (by rw [h]; trivial)
    omega
  · have := h2.2 (by rw [h]; trivial)
    omega
  · rcases Nat.even_or_odd Q.exponent with he | ho
    · have := h3.2 (by rw [h]; exact he)
      omega
    · have := h2.2 (by rw [h]; exact ho)
      omega

theorem xlevel_1519_gen (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSML3 : KSML3)
    (hK517 : K517_4a) (hK518 : K518) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hX3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    (h₁ : CFSG.Open.pRank p (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank p (Subgroup.normalizer (T₂ : Set X)) ≤ 1)
    (hLifts : ∀ Is : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Is → ∃ I, LiftOf T I Is)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hrk : CFSG.Open.pRank p L = 2)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hpQ : p ∣ Q.card + 1) (hd : d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q)
    (e : Nonempty (↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)) : False := by
  obtain ⟨hZ1, hZL, heq, hranks⟩ := lift_lie_data hT.chev hKSMOdd hX hLs.1 hL hQ hd e
  have hrank2 : IsRankTwoPlus d.1 := by
    rcases hd with h | h | h <;> rw [h] <;> simp [IsRankTwoPlus, hQ]
  have hdiv : p ∣ indexQ d.1 ^ 2 - 1 := by
    have : indexQ d.1 = Q.card := by rcases hd with h | h | h <;> rw [h] <;> rfl
    rw [this]; exact dvd_sq_sub_one_of_dvd_add_one_s15 hpQ
  obtain ⟨hA1, hA2⟩ := hK517 X T T₁ T₂ hX hg Ls hLs d hrank2 heq p hp hdiv
  have hZs : ¬ p ∣ Nat.card (Subgroup.center ↥Ls) := by rw [hZL]; exact hp.not_dvd_one
  have hinv := gnImg_le_normalizer_of_dvd_gnA (IsGNPair.le_normalizer₁ hg.pair) hp hp2 h₁
    hLs.1 hZs hA1
  obtain ⟨m1, n1⟩ := mS_mN_eq_one_of_dvd hp hp2 h₁ Ls hA1
  obtain ⟨m2, n2⟩ := mS_mN_eq_one_of_dvd hp hp2 h₂ Ls hA2
  obtain ⟨hC, hY⟩ := hK518 X T T₁ T₂ hX hg p hp hp2 Ls L hLs hL hinv m1 m2 n1 n2
  have hLs2 : CFSG.Open.pRank p Ls ≤ 2 := (pRank_le_of_lift hL hp hC).trans hrk.le
  obtain ⟨Is, hIs, hne, hdvdI⟩ := exists_other_component_s15 hp hC hY hX3 hLs2
  obtain ⟨I, hI⟩ := hLifts Is hIs
  have hLI : L ≠ I := by
    rintro rfl
    exact hne (hL.2.symm.trans hI.2).symm
  have hs : CFSG.Open.pRank 3 ((Subgroup.center ↥(barO2 L)).map (barO2 L).subtype) ≤ 0 := by
    have h0 := pRank_eq_zero_of_not_dvd_s15 (A := KFactsPair.centerIn (barO2 L)) Nat.prime_three
      (by rw [card_centerIn_s15, hZ1]; exact Nat.prime_three.not_dvd_one)
    unfold KFactsPair.centerIn at h0
    exact h0.le
  have hsum := pRank_add_le_pRank_sup hL.1 hI.1 hLI Nat.prime_three (by norm_num) hs
  have hLI3 : CFSG.Open.pRank 3 (L ⊔ I) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans h3X
  have hm3L : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [hranks 3 Nat.prime_three (by norm_num)]; exact two_le_mRankChev_three hQ hd 1
  have hm3I1 : 1 ≤ CFSG.Open.pRank 3 I := one_le_pRank_three_of_lift hg.three hIs hI
  have hm3I : CFSG.Open.pRank 3 I = 1 := by omega
  have hshapeI := rankOneShape_of_datum hKSML3 hX hIs.1 hI
    (rankDatum1512_of_pRank_three_eq_one (rankDatum hT hX hg.shape hIs hI) hm3I) hm3I
  have hpI : 1 ≤ CFSG.Open.pRank p I :=
    (one_le_pRank_iff_dvd I hp).2 (dvd_card_of_liftOf hI hdvdI)
  have hpe : p ∣ 2 ^ Q.exponent + 1 := by rw [← card_eq_two_pow_s15 hQ]; exact hpQ
  obtain ⟨hZI, hcases⟩ := hshapeI
  rcases hcases with ⟨m, d', Q', hodd, hm2, hQ'p, hQ'e, hd', e', hrank'⟩ | ⟨-, hrank'⟩
  · have hcard' : Q'.card = 2 ^ m := by rw [card_eq_two_pow_s15 hQ'p, hQ'e]
    have hmr : 1 ≤ rkLin 3 true (2 ^ m) p 1 := by
      have := hrank' p hp hp2
      rw [hd'] at this
      change CFSG.Open.pRank p I = rkLin 3 true Q'.card p 1 at this
      rw [hcard'] at this
      omega
    have hp_dvd := dvd_two_pow_add_one_of hp hp2 hpe hodd (dvd_of_one_le_rkLin_three hp hmr)
    have hrank2' : IsRankTwoPlus d'.1 := by rw [hd']; exact ⟨hQ'p, le_refl 2⟩
    have hdiv' : p ∣ indexQ d'.1 ^ 2 - 1 := by
      rw [hd']
      show p ∣ Q'.card ^ 2 - 1
      rw [hcard']
      exact dvd_sq_sub_one_of_dvd_add_one_s15 hp_dvd
    obtain ⟨hA1I, -⟩ := hK517 X T T₁ T₂ hX hg Is hIs d' hrank2' e' p hp hdiv'
    exact not_dvd_card_gnA_of_ne hp hp2 h₁ hLs.1 hIs.1 hne.symm
      (by rw [hZL]; exact hp.not_dvd_one) hA1 hA1I
  · have h37 : p = 3 ∨ p = 7 := by
      have := hrank' p hp hp2
      split_ifs at this with hh
      · exact hh
      · omega
    have hp7 : p = 7 := h37.resolve_left hp3
    have hp_dvd := dvd_two_pow_add_one_of (m := 1) hp hp2 hpe odd_one (by subst hp7; norm_num)
    have : p ∣ 3 := by simpa using hp_dvd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)



theorem xlevel_1519 (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSML3 : KSML3)
    (hK517 : K517_4a) (hK518 : K518) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂)
    (hr3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hX3 : CFSG.Open.pRank p (⊤ : Subgroup X) = 3)
    (h₁ : CFSG.Open.pRank p (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank p (Subgroup.normalizer (T₂ : Set X)) ≤ 1)
    (hLifts : ∀ Is : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Is → ∃ I, LiftOf T I Is)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hrk : CFSG.Open.pRank p L = 2)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hpQ : p ∣ Q.card + 1) (hd : d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q)
    (e : Nonempty (↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)) : False  :=
  xlevel_1519_gen hT hKSMOdd hKSML3 hK517 hK518 hX hg
    (hr3 3 Nat.prime_three (by norm_num)) hp hp2 hp3 hX3.ge h₁ h₂ hLifts hLs hL hrk hQ hpQ hd e

end Row1519

theorem row1519_gen (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSML3 : KSML3) (hK517 : K517_4a)
    (hK518 : K518) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (h11 : Row1511 G M T T₁ T₂) (h14 : Row1514 G M T T₁ T₂) (h16 : Row1516 G M T T₁ T₂)
    (h17 : Row1517 G M T T₁ T₂) (h18 : Row1518 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂)
    (ctx : S15CtxGen G M T T₁ T₂) : Row1519 G M T T₁ T₂ := by
  intro p hp Ls L hLs hL
  by_contra hgt
  have hlt := h18 p hp Ls L hLs hL
  have h2 : CFSG.Open.pRank p L = 2 := by omega
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp3 : p ≠ 3 := fun h => h11 (h ▸ hp)
  have h3X : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3 :=
    ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11
  have hshape := shape_of_row1514 hpp hp3 (h14 p hp Ls L hLs hL h2)
    (fun h => (h17 p hp Ls L hLs hL).1 h)
    (fun ⟨e, h5⟩ => h16 Ls L hLs hL e (h5 ▸ hp))
  obtain ⟨d, Q, hQ, hpQ, hd, e⟩ := hshape
  exact xlevel_1519_gen hT hKSMOdd hKSML3 hK517 hK518 ctx.gn (S15CtxGen.good ctx) h3X hpp hp2
    hp3 (ctx.three_le p hp) (ctx.rank_N₁ p hp) (ctx.rank_N₂ p hp) hLifts hLs hL h2 hQ hpQ hd e

theorem row1519 (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSML3 : KSML3) (hK517 : K517_4a)
    (hK518 : K518) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (h11 : Row1511 G M T T₁ T₂) (h14 : Row1514 G M T T₁ T₂) (h16 : Row1516 G M T T₁ T₂)
    (h17 : Row1517 G M T T₁ T₂) (h18 : Row1518 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂)
    (ctx : S15Ctx2 G M T T₁ T₂) : Row1519 G M T T₁ T₂  :=
  row1519_gen hT hKSMOdd hKSML3 hK517 hK518 h11 h14 h16 h17 h18 hLifts
    (S15CtxGen.of_ctx2 ctx)

end CFSG.LocalAnalysis.RankThreeUC.S15
