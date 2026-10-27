module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOrthTr
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOmega4
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOmega6
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviA3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviE3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviCenter
public import CFSG.Models.Blueprint
public import CFSG.RankThree.PartTwo.KFacts.K71Item119

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

noncomputable def pslCongrOfRingEquiv {F F' : Type} [Field F] [Field F'] (n : ℕ) (φ : F ≃+* F') :
    Matrix.SpecialLinearGroup (Fin n) F ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) ≃*
      Matrix.SpecialLinearGroup (Fin n) F' ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F') :=
  QuotientGroup.congr _ _ (CFSG.RankThree.PartTwo.KFacts.slCongrOfRingEquiv n φ)
    (map_center_mulEquiv _)

section

set_option linter.unusedSectionVars false


theorem tD4_e3_full {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.twistedD 4 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedD 4 q, hv⟩)) : E3Concl K₀ B z p := by
  obtain ⟨e⟩ := e
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hLM := CFSG.Models.lieModel_twistedD 4 q hv e
  have hmodel : CFSG.Blueprint.LieModel ↥K .POmegaMinus 4 2 q.exponent := by
    have h1 := hLM.toBlueprint (by decide)
    rw [hq2] at h1
    exact h1
  obtain ⟨⟨-, -, hn4⟩, hm⟩ := hLM
  rcases hm with hm | ⟨h0, -⟩
  swap
  · omega
  obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨eF⟩⟩ := hm
  have hF2 : Nat.card F = 2 ^ q.exponent := by rw [hF, hq2]
  haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF2
  let eE : ↥K ≃* ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c))) :=
    eF.trans ((orthMinusStatedProjEquiv (by omega : 2 ≤ 4)).trans
      (tailOmegaEquiv (minusTailIsometry 4 F b c) (coe_quadMinus 4 F b c)
        (commutator_orthogonalGroup_quadMinus (by omega) hirr)))
  have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq2]
  haveI : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmodel
  have hrk3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eE]
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.orthMinus_two_le_pRank_three
      (r := 3) (f := q.exponent) (by norm_num) hF2 hirr
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_of_two_le_pRank Nat.prime_three hrk3
  have hdiv : ¬ p ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .POmegaMinus 4
      (2 ^ q.exponent) := by
    intro hd
    have h1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .POmegaMinus 4
        (2 ^ q.exponent) = Nat.gcd 4 ((2 ^ q.exponent) ^ 4 + 1) := rfl
    rw [h1] at hd
    have h3 : Nat.gcd 4 ((2 ^ q.exponent) ^ 4 + 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
    have hpos : 0 < Nat.gcd 4 ((2 ^ q.exponent) ^ 4 + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have := Nat.le_of_dvd hpos hd
    have := S.hp5
    omega
  obtain ⟨f₀, hf₀⟩ := field_degree_of_faithful S.hp (by have := S.hp5; omega) S.hKr hZ S.hB S.hBc
    S.hBK S.hnb (CFSG.Blueprint.LieModel.admissible hmodel) hmodel (by decide) hdiv (by simp)
    (by simp)
  have hf5 : 5 ≤ q.exponent := five_le_of_eq_mul S.hp5 q.exponent_pos hf₀
  have hq32 : 32 ≤ q.card := by
    rw [hq]
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf5
  have h4 : 4 ≤ Nat.card F := by omega
  rcases tD4_leviSurj_of_equiv S hirr h4 hF2 eE with hL | ⟨m, hm, hL⟩
  ·
    have hv2 : (LieTypeIndex.A 2 q).Valid := valid_A_two_of_ne_two (by omega)
    haveI : CharP (GaloisField q.p q.exponent) 2 := by
      have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
        (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
      exact ringChar.of_eq hchar
    haveI : Finite (GaloisField q.p q.exponent) := inferInstance
    have hcardGF : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
      rw [GaloisField.card q.p q.exponent (by have := q.exponent_pos; omega), hq2]
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
    let φ : F ≃+* GaloisField q.p q.exponent :=
      FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF2, hcardGF])
    have hL' : LeviSurj p K₀ z (CFSGIndex.lie ⟨.A 2 q, hv2⟩).Group :=
      hL.of_mulEquiv ((pslCongrOfRingEquiv 3 φ).trans
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv2).symm)
    exact LeviSurj.conclusion S.hp S.hBK₀ (d := ⟨.A 2 q, hv2⟩) (by simpa using hq2) (by simp)
      (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hL'
  · rcases hm with rfl | rfl
    ·
      obtain ⟨ψ⟩ := orthResDer_one_equiv_psl2 hirr hF2
      let q' : PrimePower := ⟨2, 2 * q.exponent, Nat.prime_two, by omega⟩
      have hcard' : 10 ≤ q'.card := by
        rw [PrimePower.card_def]
        show 10 ≤ 2 ^ (2 * q.exponent)
        calc 10 ≤ 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (2 * q.exponent) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hv' : (LieTypeIndex.A 1 q').Valid := valid_A_one_of_ten_le hcard'
      haveI : Fact q'.p.Prime := ⟨q'.prime_p⟩
      have hL' : LeviSurj p K₀ z (CFSGIndex.lie ⟨.A 1 q', hv'⟩).Group :=
        hL.of_mulEquiv (ψ.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q' hv').symm)
      exact LeviSurj.conclusion S.hp S.hBK₀ (d := ⟨.A 1 q', hv'⟩) (by simp [q']) (by simp)
        (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hL'
    ·
      obtain ⟨ψ⟩ := orthResDer_two_equiv_psu4 hirr hF2
      have hv3 : (LieTypeIndex.twistedA 3 q).Valid := by
        refine (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2
          ⟨by norm_num, fun h => absurd h (by norm_num)⟩, ?_⟩
        rw [LieTypeIndex.isDuplicateRepresentative_iff]
        exact fun h => h
      have hchar : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv3⟩ = 2 :=
        (LieTypeIndex.characteristic_twistedA 3 q).trans hq2
      have hexp : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv3⟩ = q.exponent :=
        LieTypeIndex.fieldExponent_twistedA 3 q
      have key : ∀ (p' f' : ℕ) [Fact p'.Prime], p' = 2 → f' = q.exponent →
          Nonempty (StatedProj (StatedSU 4 (p' ^ f') (GaloisField p' (2 * f'))) ≃*
            StatedProj (StatedSU 4 (2 ^ q.exponent) (GaloisField 2 (2 * q.exponent)))) := by
        intro p' f' _ h1 h2
        subst h1
        subst h2
        exact ⟨MulEquiv.refl _⟩
      obtain ⟨ι⟩ := key (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv3⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv3⟩) hchar hexp
      have hL' : LeviSurj p K₀ z (CFSGIndex.lie ⟨.twistedA 3 q, hv3⟩).Group :=
        hL.of_mulEquiv (ψ.trans (ι.symm.trans
          (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv3).symm))
      exact LeviSurj.conclusion S.hp S.hBK₀ (d := ⟨.twistedA 3 q, hv3⟩) (by simpa using hq2)
        (by simp)
        (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hL'

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
