module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
import CFSG.HardMathSupport.Malle.E27Lie.Cross.Index
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ree
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwG2
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticRank
import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
import CFSG.LieType.SeitzGeneration.ExtSeitzBridge
import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Ree


private theorem false_of_pRank_le_one (hI : GL83.I_7_13_1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1) {A : Subgroup (MulAut S)}
    (hA : CFSG.Open.IsElemAbelian p A) (h3 : p ^ 3 ≤ Nat.card A) : False := by
  have h3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) :=
    three_le_pRank_of_card hp hA h3
  have h2' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ 2 :=
    (hI p hp hp2 S hS hnab hcat hrk).2
  omega

private theorem exists_noncomm_of_elemAbelian_cube {p : ℕ} (hp : p.Prime)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) {A : Subgroup (MulAut S)}
    (hA : CFSG.Open.IsElemAbelian p A) (h3 : p ^ 3 ≤ Nat.card A) :
    ∃ a b : S, a * b ≠ b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ^ 2 ≤ Nat.card A :=
    (Nat.pow_le_pow_right hp.pos (by norm_num : 2 ≤ 3)).trans h3
  obtain ⟨E, hEcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥A) hp hA.isPGroup
      (by simpa using hp2)
  have hE : CFSG.Open.IsElemAbelian p (E.map A.subtype) :=
    hA.mono (Subgroup.map_subtype_le E)
  refine CFSG.LieType.SeitzGeneration.exists_noncommuting_of_isElementaryAbelian_aut
    (E := E.map A.subtype) hE.isElementaryAbelian ?_
  rw [Subgroup.card_map_of_injective A.subtype_injective, hEcard]

private theorem false_of_pRank_le_one_of_mulEquiv (hI : GL83.I_7_13_1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S Γ : Type} [Group S] [Finite S] [Group Γ] [Finite Γ]
    (hΓ : IsSimpleGroup Γ) (hrkΓ : CFSG.Open.pRank p (⊤ : Subgroup Γ) ≤ 1) (e : S ≃* Γ)
    (hcat : CFSG.Open.IsCatalogGroup S) {A : Subgroup (MulAut S)}
    (hAel : CFSG.Open.IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A) : False := by
  have hS : IsSimpleGroup S := e.isSimpleGroup
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).le.trans hrkΓ
  exact false_of_pRank_le_one hI hp hp2 hS
    (exists_noncomm_of_elemAbelian_cube hp hS hAel hA3) hcat hrk hAel hA3

private theorem false_of_PSL_two (hI : GL83.I_7_13_1) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower} (hQ : Q.p = q) (hq2 : q ≠ 2)
    (hpq : p ≠ q) (hS : IsSimpleGroup S) (hcat : CFSG.Open.IsCatalogGroup S)
    (hmodel : StatedClassicalModel S .PSL 2 Q.p Q.exponent)
    {A : Subgroup (MulAut S)} (hAel : CFSG.Open.IsElemAbelian p A)
    (hA3 : p ^ 3 ≤ Nat.card A) : False := by
  obtain ⟨-, K, _, _, hKcard, ⟨eK⟩⟩ := hmodel
  let ePSL : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Finite.of_equiv S ePSL.toEquiv
  haveI : Fact p.Prime := ⟨hp⟩
  have hreq : Q.p ≠ 2 := by rw [hQ]; exact hq2
  have hpq' : p ≠ Q.p := by rw [hQ]; exact hpq
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 := by
    refine (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt ePSL).le.trans ?_
    exact CFSG.LocalAnalysis.RankFourTheoremC.pRank_le_one_of_sylow_isCyclic hp fun R =>
      CFSG.SectionRank.OddCover.psl_two_sylow_isCyclic Q.prime_p hreq hKcard hp2 hpq' R
  exact false_of_pRank_le_one hI hp hp2 hS
    (exists_noncomm_of_elemAbelian_cube hp hS hAel hA3) hcat hrk hAel hA3

private theorem false_of_PSU_three (hI : GL83.I_7_13_1) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower} (hQ : Q.p = q) (hpq : p ≠ q)
    (hndvd : ¬ p ∣ Q.card + 1) (hS : IsSimpleGroup S) (hcat : CFSG.Open.IsCatalogGroup S)
    (hmodel : StatedClassicalModel S .PSU 3 Q.p Q.exponent)
    {A : Subgroup (MulAut S)} (hAel : CFSG.Open.IsElemAbelian p A)
    (hA3 : p ^ 3 ≤ Nat.card A) : False := by
  obtain ⟨-, K, _, _, hKcard, ⟨eSU⟩⟩ := hmodel
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card K = Q.p ^ (2 * Q.exponent) := by
    rw [hKcard, ← pow_mul, mul_comm]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K Q.p :=
    charP_of_card_eq_prime_pow (p := Q.p) (f := 2 * Q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hpq' : p ≠ Q.p := by rw [hQ]; exact hpq
  have hre : ¬ p ∣ Q.p ^ Q.exponent + 1 := by simpa using hndvd
  have hcycSU : ∀ P : Sylow p ↥(StatedSU 3 (Q.p ^ Q.exponent) K),
      IsCyclic (P : Subgroup ↥(StatedSU 3 (Q.p ^ Q.exponent) K)) := fun P =>
    CFSG.ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow
      (p := Q.p) (f := Q.exponent) hKcard hp2 hpq' hre P
  have hSUrank : CFSG.Open.pRank p
      (⊤ : Subgroup ↥(StatedSU 3 (Q.p ^ Q.exponent) K)) ≤ 1 :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_le_one_of_sylow_isCyclic hp hcycSU
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (Q.p ^ Q.exponent) K)) := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Q.prime_p hKcard (n := 3)
      (by norm_num)).2.2]
    exact fun hd => hre (hd.trans (Nat.gcd_dvd_right 3 _))
  have hprojRank : CFSG.Open.pRank p
      (⊤ : Subgroup (StatedProj (StatedSU 3 (Q.p ^ Q.exponent) K))) ≤ 1 := by
    refine (CFSG.SectionRank.pRank_quotient_eq
      ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (Q.p ^ Q.exponent) K)) hN).le.trans ?_
    exact hSUrank
  haveI : Finite (StatedProj (StatedSU 3 (Q.p ^ Q.exponent) K)) :=
    Finite.of_equiv S eSU.toEquiv
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eSU).le.trans hprojRank
  exact false_of_pRank_le_one hI hp hp2 hS
    (exists_noncomm_of_elemAbelian_cube hp hS hAel hA3) hcat hrk hAel hA3

private theorem not_sq_dvd_five_factorial {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ (5).factorial / 2 := by
  have h60 : Nat.factorial 5 / 2 = 60 := by norm_num
  rw [h60]
  intro h
  have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h
  have hp2' : 2 ≤ p := hp.two_le
  have hp7 : p ≤ 7 := by nlinarith
  interval_cases p
  all_goals first
    | exact hp2 rfl
    | exact absurd h (by norm_num)

private theorem not_sq_dvd_six_factorial {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ (6).factorial / 2 := by
  have h360 : Nat.factorial 6 / 2 = 360 := by norm_num
  rw [h360]
  intro h
  have hle : p ^ 2 ≤ 360 := Nat.le_of_dvd (by norm_num) h
  have hp2' : 2 ≤ p := hp.two_le
  have hp18 : p ≤ 18 := by nlinarith
  interval_cases p
  all_goals first
    | exact hp2 rfl
    | exact hp3 rfl
    | exact absurd hp (by decide)
    | exact absurd h (by norm_num)

private theorem false_of_alt (hI : GL83.I_7_13_1) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 2 ≤ n) {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥(alternatingGroup (Fin n))) (hcat : CFSG.Open.IsCatalogGroup S)
    (hS : IsSimpleGroup S) (hdiv : ¬ p ^ 2 ∣ n.factorial / 2) {A : Subgroup (MulAut S)}
    (hAel : CFSG.Open.IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A) : False := by
  haveI : Nontrivial (Fin n) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_fin]
    omega
  have hcard : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hdiv' : ¬ p ^ 2 ∣ Nat.card S := by rwa [hcard]
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p S]
    exact CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_not_dvd hdiv'
  exact false_of_pRank_le_one hI hp hp2 hS
    (exists_noncomm_of_elemAbelian_cube hp hS hAel hA3) hcat hrk hAel hA3

private theorem false_of_reeG2 (hI : GL83.I_7_13_1) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3)
    (hm : 1 ≤ m) {S : Type} [Group S] [Finite S] {hv : (TauCeti.LieTypeIndex.reeG2 m).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group)
    (hcat : CFSG.Open.IsCatalogGroup S) {A : Subgroup (MulAut S)}
    (hAel : CFSG.Open.IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A) : False := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
  haveI : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    inferInstanceAs (CharP (GaloisField 3 (2 * m + 1)) 3)
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  obtain ⟨ψ⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.nonempty_reeGamma_equiv hv
      (K := GaloisField 3 (2 * m + 1)) hK
  have hsimple : IsSimpleGroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) :=
    (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hm
      (GaloisField 3 (2 * m + 1)) hK).2.1
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥(ReeTag.G2.reeGamma
      (GaloisField 3 (2 * m + 1)) m)) ≤ 1 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_le_one_reeGamma_G2
      m hm (GaloisField 3 (2 * m + 1)) hK hp hp5
  exact (false_of_pRank_le_one_of_mulEquiv hI hp (by omega) hsimple hrank (e.trans ψ) hcat
    hAel hA3).elim


theorem rankOneFact_holds : RankOneFact := by
  intro p q hp hp2 hq hq2 hqp S _ _ hChev hCat hA
  obtain ⟨A, hAel, hA3⟩ := hA
  obtain ⟨i, hi, ⟨e⟩⟩ := hCat
  have hI : GL83.I_7_13_1 := GL83.I713.i_7_13_1_holds
  have hcat : CFSG.Open.IsCatalogGroup S := ⟨i, ⟨e⟩⟩
  cases i with
  | cyclic p' hp' => simp [CatRankOne] at hi
  | sporadic s => simp [CatRankOne] at hi
  | alternating n hn =>
    rcases (by simpa only [CatRankOne] using hi) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact (false_of_alt hI hp hp2 (by norm_num : 2 ≤ 5) e hcat e.isSimpleGroup
        (not_sq_dvd_five_factorial hp hp2) hAel hA3).elim
    · haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hp3 : p ≠ 3 := fun h => hqp h.symm
      exact (false_of_alt hI hp hp2 (by norm_num : 2 ≤ 6) e hcat e.isSimpleGroup
        (not_sq_dvd_six_factorial hp hp2 hp3) hAel hA3).elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A rank Q =>
      rcases rank with _ | _ | rank
      · simp [CatRankOne] at hi
      · simp only [CatRankOne] at hi
        have hmodel := CFSG.HardMathSupport.Malle.E27Lie.statedClassicalModel_typeA' hv e
        have hS : IsSimpleGroup S :=
          (CFSG.LieType.Simplicity.fam_PSL_simplicity S 2 Q.p Q.exponent hmodel).2
        exact (false_of_PSL_two hI hp hp2 hi hq2 (Ne.symm hqp) hS hcat hmodel hAel hA3).elim
      · simp [CatRankOne] at hi
    | twistedA rank Q =>
      rcases rank with _ | _ | _ | rank
      · simp [CatRankOne] at hi
      · simp [CatRankOne] at hi
      · simp only [CatRankOne] at hi
        by_cases hdvd : p ∣ Q.card + 1
        · exact ⟨Q, hi, hdvd, ⟨.lie ⟨.twistedA 2 Q, hv⟩, rfl, ⟨e⟩⟩⟩
        · have hmodel :=
            CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 Q hv e
          have hS : IsSimpleGroup S :=
            (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity S 3 Q.p Q.exponent hmodel).2
          exact (false_of_PSU_three hI hp hp2 hi (Ne.symm hqp) hdvd hS hcat hmodel hAel
            hA3).elim
      · simp [CatRankOne] at hi
    | reeG2 m =>
      simp only [CatRankOne] at hi
      have hm : 1 ≤ m :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have hp3 : p ≠ 3 := fun h => hqp (hi.trans h.symm)
      exact (false_of_reeG2 hI hp hp2 hp3 hm e hcat hAel hA3).elim
    | _ => simp [CatRankOne] at hi

end CFSG.LocalAnalysis.GLTheoremA.H248
