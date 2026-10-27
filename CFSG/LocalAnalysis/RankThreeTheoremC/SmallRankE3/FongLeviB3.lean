module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviB3Equiv
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviA3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviE3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSp4
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr)

theorem valid_B_two_of_four_le {q : PrimePower} (h : 4 ≤ q.card) : (LieTypeIndex.B 2 q).Valid := by
  refine (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 ⟨le_rfl, ?_⟩, ?_⟩
  · rintro ⟨-, h2⟩
    omega
  · rw [LieTypeIndex.isDuplicateRepresentative_iff]
    rintro ⟨-, h3⟩
    omega

noncomputable def typeB2EquivStatedSp (q : PrimePower) [Fact q.p.Prime] (hq2 : q.p = 2)
    (hv : (LieTypeIndex.B 2 q).Valid) :
    ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩ ≃* CFSG.Open.StatedSp 2 (GaloisField q.p q.exponent) := by
  haveI : CharP (GaloisField q.p q.exponent) 2 := by
    have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
      (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
    exact ringChar.of_eq hchar
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  let φ : ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) ≃+* GaloisField q.p q.exponent :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField _ q.p q.exponent q.exponent_pos (by
      rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
        show ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ = q.p from
          LieTypeIndex.characteristic_B 2 q,
        show ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ = q.exponent from
          LieTypeIndex.fieldExponent_B 2 q])
  exact ((CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv).trans
    (statedProjCongr (glCongr φ) (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
      (glCongr_statedScalars φ))).trans (statedProjSpEquiv 2)

noncomputable def typeB3EquivStatedSp (q : PrimePower) [Fact q.p.Prime] (hq2 : q.p = 2)
    (hv : (LieTypeIndex.B 3 q).Valid) :
    ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩ ≃* CFSG.Open.StatedSp 3 (GaloisField q.p q.exponent) := by
  haveI : CharP (GaloisField q.p q.exponent) 2 := by
    have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
      (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
    exact ringChar.of_eq hchar
  exact ((CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivProjSp 3 q hv hq2
    (by norm_num)).trans (CFSG.PGLModel.projSpEquivStatedProj 3 _)).trans (statedProjSpEquiv 3)

section

set_option linter.unusedSectionVars false


theorem three_dvd_two_pow_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  have h : (2 ^ f) ^ 2 = 4 ^ f := by
    rw [sq, ← mul_pow]
    norm_num
  rw [h]
  have h1 : (1 : ℕ) ≡ 4 [MOD 3] := rfl
  have h2 := h1.pow f
  rw [one_pow] at h2
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h2

theorem b3_e3_full {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.B 3 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩)) : E3Concl K₀ B z p := by
  obtain ⟨e⟩ := e
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
    (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
  haveI : CharP (GaloisField q.p q.exponent) 2 := ringChar.of_eq hchar
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq2]
  have hcardF : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
    rw [GaloisField.card q.p q.exponent (by omega), hq2]
  let eSp : ↥K ≃* CFSG.Open.StatedSp 3 (GaloisField q.p q.exponent) :=
    e.trans (typeB3EquivStatedSp q hq2 hv)
  have hmodel : CFSG.Blueprint.LieModel ↥K .PSp 3 2 q.exponent := by
    have h1 := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2
      (by norm_num) e
    rw [hq2] at h1
    exact Or.inl ⟨by decide, h1⟩
  haveI : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmodel
  have hrk3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eSp]
    have hdvd : 3 ∣ Nat.card (GaloisField q.p q.exponent) ^ 2 - 1 := by
      rw [hcardF]
      exact three_dvd_two_pow_sq_sub_one _
    have := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp
      (K := GaloisField q.p q.exponent) (n := 3) (r := 3) Nat.prime_three hdvd
    omega
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_of_two_le_pRank Nat.prime_three hrk3
  have hdiv : ¬ p ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSp 3 (2 ^ q.exponent) := by
    intro hd
    have h1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSp 3 (2 ^ q.exponent) =
        Nat.gcd 2 (2 ^ q.exponent - 1) := rfl
    rw [h1] at hd
    have h3 : Nat.gcd 2 (2 ^ q.exponent - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hpos : 0 < Nat.gcd 2 (2 ^ q.exponent - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
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
  have h4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by omega
  rcases b3_leviSurj_of_equiv S h4 eSp with hL | hL
  ·
    have hv2 : (LieTypeIndex.A 2 q).Valid := valid_A_two_of_ne_two (by omega)
    have hL' : LeviSurj p K₀ z (CFSGIndex.lie ⟨.A 2 q, hv2⟩).Group :=
      hL.of_mulEquiv (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv2).symm
    exact LeviSurj.conclusion S.hp S.hBK₀ (d := ⟨.A 2 q, hv2⟩) (by simpa using hq2) (by simp)
      (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hL'
  ·
    have hv2 : (LieTypeIndex.B 2 q).Valid := valid_B_two_of_four_le (by omega)
    have hL' : LeviSurj p K₀ z (CFSGIndex.lie ⟨.B 2 q, hv2⟩).Group :=
      hL.of_mulEquiv (typeB2EquivStatedSp q hq2 hv2).symm
    exact LeviSurj.conclusion S.hp S.hBK₀ (d := ⟨.B 2 q, hv2⟩) (by simpa using hq2) (by simp)
      (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hL'

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
