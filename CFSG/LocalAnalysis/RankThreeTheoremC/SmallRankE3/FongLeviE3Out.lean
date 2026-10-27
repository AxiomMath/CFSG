module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviE3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviU4Sub
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.LieModelSimple
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

theorem not_dvd_lieOrderDivisor_psl3 {p : ℕ} (hp5 : 5 ≤ p) (q : ℕ) :
    ¬ p ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 q := by
  intro hd
  have h1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 q = Nat.gcd 3 (q - 1) :=
    rfl
  rw [h1] at hd
  have h3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hpos : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have := Nat.le_of_dvd hpos hd
  omega

theorem not_dvd_lieOrderDivisor_psu4 {p : ℕ} (hp5 : 5 ≤ p) (q : ℕ) :
    ¬ p ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 q := by
  intro hd
  have h1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 q = Nat.gcd 4 (q + 1) :=
    rfl
  rw [h1] at hd
  have h3 : Nat.gcd 4 (q + 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  have hpos : 0 < Nat.gcd 4 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have := Nat.le_of_dvd hpos hd
  omega

theorem l3_e3_full {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K ≤ 1) (hz : orderOf z = p)
    (hzK₀ : z ∈ K₀)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) (hne : K₀ ≠ K)
    (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBK : B ≤ normalizer (K : Set A)) (hBK₀ : B ≤ normalizer (K₀ : Set A))
    (hnb : ∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.A 2 q).Valid) (e : ↥K ≃* ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) :
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex d.1 ∧
        ∃ φ : ↥H →* (CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
    (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
  haveI : CharP (GaloisField q.p q.exponent) 2 := ringChar.of_eq hchar
  let e0 : ↥K ≃* projectiveSL 3 (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _))
  have hZ : Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e0 x ∈ Subgroup.center (projectiveSL 3 (GaloisField q.p q.exponent)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := Subgroup.mem_center_iff.mp hx (e0.symm y)
      have h3 := congrArg e0 h2
      simpa using h3
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)] at h1
    rw [Subgroup.mem_bot]
    exact e0.injective (by simpa using h1)
  have hmodel : CFSG.Blueprint.LieModel ↥K .PSL 3 2 q.exponent := by
    have h1 := (CFSG.Models.lieModel_A 2 q hv e).toBlueprint (by decide)
    rw [hq2] at h1
    exact h1
  obtain ⟨f₀, hf₀⟩ := field_degree_of_faithful hp (by omega) hKr hZ hB hBc hBK hnb
    (CFSG.Blueprint.LieModel.admissible hmodel) hmodel (by decide)
    (not_dvd_lieOrderDivisor_psl3 hp5 _)
    (by simp) (by simp)
  exact l3_e3_conclusion hp hp5 hKr hz hzK₀ hpar hne hBK₀ hq2 hv e
    (five_le_of_eq_mul hp5 q.exponent_pos hf₀)

theorem u4_e3_full {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K ≤ 1) (hz : orderOf z = p)
    (hzK₀ : z ∈ K₀)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) (hne : K₀ ≠ K)
    (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBK : B ≤ normalizer (K : Set A)) (hBK₀ : B ≤ normalizer (K₀ : Set A))
    (hnb : ∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.twistedA 3 q).Valid)
    (e : ↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) :
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex d.1 ∧
        ∃ φ : ↥H →* (CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H := by
  have hmodel : CFSG.Blueprint.LieModel ↥K .PSU 4 2 q.exponent := by
    have h1 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hq2] at h1
    exact Or.inl ⟨by decide, h1⟩
  haveI : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmodel
  obtain ⟨K', _, h, ⟨e1⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hmodel
  obtain ⟨f, hf, -, -, hfr⟩ := exists_prime_two_le_pRank_hypSU h
  haveI : Finite (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0) := by
    haveI := h.finite
    exact CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hfr' : 2 ≤ CFSG.Open.pRank f (⊤ : Subgroup ↥K) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hf.one_lt e1]
    exact hfr
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_of_two_le_pRank hf hfr'
  obtain ⟨f₀, hf₀⟩ := field_degree_of_faithful hp (by omega) hKr hZ hB hBc hBK hnb
    (CFSG.Blueprint.LieModel.admissible hmodel) hmodel (by decide)
    (not_dvd_lieOrderDivisor_psu4 hp5 _)
    (by simp) (by simp)
  exact u4_e3_conclusion hp hp5 hKr hz hzK₀ hpar hne hBK₀ hq2 hv e
    (by have := five_le_of_eq_mul hp5 q.exponent_pos hf₀; omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
