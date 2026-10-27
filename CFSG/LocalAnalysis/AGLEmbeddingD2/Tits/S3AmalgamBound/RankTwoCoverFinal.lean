module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSLMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSpMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSpinMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusAltEight
import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.RankThreeTheoremC

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}

theorem CoverCtx.false_of_model_psl (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) (hf : 2 ≤ f) : False := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ctx.false_of_psl (m := m) (by omega) (four_le_card_of_card_eq_two_pow hcard hf)
    ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm)

theorem CoverCtx.false_of_model_psl_two (ctx : CoverCtx L S₀ A₁ A₂) {n : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 1) (hn4 : 4 ≤ n) : False := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ctx.false_of_psl_two (m := m) (by omega) hF2
    ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm)

section Main


theorem CoverCtx.false_of_index (ctx : CoverCtx L S₀ A₁ A₂) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  obtain ⟨d, hv⟩ := d
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hv'.1
  have hdup := hv'.2
  rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at h
    by_cases hf : 2 ≤ q.exponent
    · exact ctx.false_of_model_psl h hf
    · have hq2 := card_eq_two_of_not_two_le_exponent hd hf
      have he1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [he1] at h
      simp only at hrange hdup
      exact ctx.false_of_model_psl_two h (by omega)
  | twistedA r q =>
    change q.p = 2 at hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at h
    simp only at hrange
    by_cases h4 : 4 ≤ r + 1
    · exact ctx.false_of_psu h h4
    · obtain rfl : r = 2 := by omega
      exact ctx.false_of_psu_three h
  | B r q =>
    change q.p = 2 at hd
    simp only at hrange hdup
    have h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp r q.p q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
          (by omega) e
    rw [hd] at h
    by_cases hf : 2 ≤ q.exponent
    · exact ctx.false_of_psp h hf
    · have hq2 := card_eq_two_of_not_two_le_exponent hd hf
      have he1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [he1] at h
      exact ctx.false_of_psp_two (n := r) h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    simp only at hrange
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    by_cases hf : 2 ≤ q.exponent
    · exact ctx.false_of_pomegaPlus h hf
    · have he1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [he1] at h
      exact ctx.false_of_pomegaPlus_two h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact ctx.false_of_pomegaMinus_short h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    have hq3 : 3 ≤ q.card := by simpa using hrange
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
    have hm : 2 ≤ q.exponent := by
      by_contra hm
      have h1 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ctx.false_of_g2 (e.trans b.symm)
      (by rw [hK, hcard]; exact four_le_two_pow_of_le hm)
  | _ => exact hd.elim

theorem kFactParabolicCoverRankTwo : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactParabolicCoverRankTwo := by
  intro W _ _ L S₀ A₁ A₂ hL hY hS hcov h1 h2 hE
  have htrans : ∀ E : Subgroup W, (E ≤ A₁ ⊓ L ∨ E ≤ A₂ ⊓ L) → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → TransitiveOnNonidentity (Subgroup.normalizer (E : Set W)) E := by
    intro E hEle hab hcard
    refine (hE E hEle ?_ ?_).2.2
    · intro g
      have h3 : (g : E) ^ 3 = 1 := Subtype.ext (hab.2 g g.2)
      exact ⟨1, by simpa using h3⟩
    · intro hc
      obtain ⟨g, hg⟩ := hc.exists_generator
      have h3 : (g : E) ^ 3 = 1 := Subtype.ext (hab.2 g g.2)
      have h9 : orderOf g = 9 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg]; exact hcard
      have := orderOf_dvd_of_pow_eq_one h3
      rw [h9] at this
      omega
  have ctx : CoverCtx L S₀ A₁ A₂ := ⟨hL, hS, hcov, h1, h2, htrans⟩
  rcases hY with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact (ctx.false_of_index d hd e).elim
  · rcases hn with rfl | rfl | rfl
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
      obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
        (GaloisField 2 2) (Or.inl (by rw [hcard]; norm_num))
      exact ctx.false_of_model_psl (n := 2) (f := 2)
        ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
          inferInstance, inferInstance, hcard, ⟨e.trans e4.symm⟩⟩ le_rfl
    · exact Or.inl ⟨e⟩
    · exfalso
      obtain ⟨e8⟩ := CFSG.AGLEmbedding.ToralCensus.nonempty_alt_eight_mulEquiv_projectiveSL
      have hF : Nat.card (GaloisField 2 1) = 2 := by
        have := Fact.mk Nat.prime_two
        rw [GaloisField.card 2 1 one_ne_zero]; norm_num
      exact ctx.false_of_psl_two (m := 3) (F := GaloisField 2 1) (by norm_num) hF
        ((QuotientGroup.quotientMulEquivOfEq
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4
            (GaloisField 2 1))).symm.trans (e8.symm.trans e.symm))
  · obtain ⟨dd, hv⟩ := d
    rcases hd with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      exact Or.inr (Or.inl (CFSG.RankThree.PartTwo.Sec3.statedClassicalModel_psl_three_two_of_seven h (by norm_num)))
    · simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at h
      exact Or.inr (Or.inr h)

end Main

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
