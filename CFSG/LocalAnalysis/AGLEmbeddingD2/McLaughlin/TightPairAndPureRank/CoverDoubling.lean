module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverG2
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LieType.SteinbergBROddSylowNormalizers
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.Assembly.LowTwoRank
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData


theorem kFactParabolicCoverDoubling_proved : KFactParabolicCoverDoubling := by
  intro W _ _ L S₀ A₁ A₂ hLq hcl hS hcov h1 h2
  obtain ⟨-, hr1, hs1⟩ := h1
  obtain ⟨-, hr2, hs2⟩ := h2
  have ctx : CoverCtx L S₀ A₁ A₂ :=
    ⟨hS, hcov, coverOk_image L A₁ hs1 hr1, coverOk_image L A₂ hs2 hr2⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcl with ⟨⟨d1, hv⟩, hd, ⟨e⟩⟩ | ⟨N, hN, ⟨e⟩⟩ | h3
  · exfalso
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
    simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    cases d1 with
    | A r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hd] at h
      obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, hK, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent)
        (by rw [← Nat.card_eq_fintype_card]; exact hK)
      refine ctx.false_sl_all hK hrange.1 (fun hf => ?_)
        ((projectiveSpecialLinearGroupEquivStatedProj (r + 1) K).trans e'.symm)
      have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hd, hf]; norm_num
      by_contra hlt
      have hr12 : r = 1 ∨ r = 2 := by have := hrange.1; omega
      rcases hr12 with rfl | rfl
      · have := hrange.2 rfl
        omega
      · exact hdup (Or.inr (Or.inl ⟨rfl, hc⟩))
    | twistedA r q =>
      change q.p = 2 at hd
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hd] at h
      obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
        (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
      refine ctx.false_su_all hK (by have := hrange.1; omega) (fun hf => ?_) e'
      have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hd, hf]; norm_num
      have := hrange.1
      by_contra hlt
      have hr2 : r = 2 := by omega
      subst hr2
      have := hrange.2 rfl
      omega
    | B r q =>
      change q.p = 2 at hd
      have hr3 : 2 ≤ r := hrange.1
      by_cases h2 : r = 2
      · subst h2
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rw [hd] at h
        obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
        have := Fintype.ofFinite K
        have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent)
          (by rw [← Nat.card_eq_fintype_card]; exact hK)
        refine ctx.false_sp_all hK (by omega) (fun hf => ?_) e'
        have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hd, hf]; norm_num
        exact (hrange.2 ⟨rfl, hc⟩).elim
      · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
          (by omega) e
        rw [hd] at h
        obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
        have := Fintype.ofFinite K
        have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent)
          (by rw [← Nat.card_eq_fintype_card]; exact hK)
        exact ctx.false_sp_all hK (by omega) (fun _ => by omega) e'
    | C r q => exact hd.elim
    | D r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
      rw [hd] at h
      obtain ⟨⟨-, -, hm⟩, K, _, _, hK, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent)
        (by rw [← Nat.card_eq_fintype_card]; exact hK)
      exact ctx.false_spinPlus_all hK (by omega) e'
    | twistedD r q =>
      change q.p = 2 at hd
      have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
      rw [hd] at h
      obtain ⟨⟨-, -, hm⟩, K, _, _, hK, b, c, hirr, ⟨e'⟩⟩ := h
      have := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent)
        (by rw [← Nat.card_eq_fintype_card]; exact hK)
      exact ctx.false_spinMinus_all hirr hK (by omega) e'
    | G2 q =>
      change q.p = 2 at hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
      have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
        (GaloisField q.p q.exponent) hK
      have hq3 : 3 ≤ q.card := hrange
      have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
      have hm : 2 ≤ q.exponent := by
        by_contra hm
        have h1 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact ctx.false_g2_big (K := GaloisField q.p q.exponent)
        (by rw [hK, hcard]; exact four_le_two_pow_of_le hm) (e.trans b.symm)
    | _ => exact hd.elim
  · rcases hN with rfl | rfl | rfl
    · exfalso
      have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
      obtain ⟨eK⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
        (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
      exact ctx.false_sl_all (m := 1) (f := 2) hK le_rfl (fun h => by omega)
        ((projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)).trans
          (e.trans eK.symm).symm)
    · exact Or.inr (Or.inl ⟨e⟩)
    · exfalso
      have e8 : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSL 4 (ZMod 2)) :=
        (e.trans CFSG.LieType.SteinbergBR.OddSylow.alternatingEightEquiv).trans
          (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 4 (ZMod 2))
      have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
      exact ctx.false_sl_all (m := 3) (f := 1) hK (by omega) (fun _ => le_rfl)
        ((projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod 2)).trans e8.symm)
  · obtain ⟨d, hd | hd, he⟩ := h3
    · exact Or.inl ⟨d, hd, he⟩
    · exact Or.inr (Or.inr ⟨d, hd, he⟩)

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
