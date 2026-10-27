module

public import CFSG.CGT.PushingUpLit.CGT6K1.Defs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push29Defs
public import CFSG.Dihedral.Glauberman.DicksonMaxB

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.CGT.PushingUpLit.CGT6
open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoStandard

theorem kProper_catalog_of_isKGroupCat {Y : Type} [Group Y] (hY : SectionRank.IsKGroupCat Y) :
    Assembly.KProper Catalog Y :=
  CFSG.KCore.KGroupNonab.kProperNonab (CFSG.KCore.KGroupAllSimple.kGroupNonab hY)

theorem center_specialLinear_two_eq_bot {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

theorem center_eq_bot_of_mulEquiv_specialLinear_two {X : Type} [Group X] {K : Type} [Field K]
    [CharP K 2] (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_center_iff.mp hz (e.symm g)
    simpa using congrArg e h
  rw [center_specialLinear_two_eq_bot, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hz', map_one])

theorem statedClassicalModel_psl_two_of_mulEquiv_specialLinear_two {X : Type} [Group X] {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : StatedClassicalModel X .PSL 2 2 n := by
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK'
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let eP : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_specialLinear_two_eq_bot.symm)
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK',
    ⟨(e.trans eP).trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem standardComponentOddCore_eq_bot_of_isSimpleGroup {D : Type} [Group D] [Finite D]
    (hD : IsSimpleGroup D) {A : Subgroup D} (hA : Open.standardComponentIsStandard A) :
    Open.standardComponentOddCore D = ⊥ := by
  have hev : Even (Nat.card D) := by
    have h1 : Even (Nat.card ↥(Subgroup.centralizer (A : Set D))) := hA.2.1
    exact even_iff_two_dvd.mpr
      ((even_iff_two_dvd.mp h1).trans (Subgroup.card_subgroup_dvd_card _))
  refine eq_bot_iff.mpr (sSup_le ?_)
  rintro N ⟨hN, hodd⟩
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h.le
  · rw [h, Subgroup.card_top] at hodd
    exact absurd hev (Nat.not_even_iff_odd.mpr hodd)

theorem normalClosure_eq_top_of_not_commute {D : Type} [Group D] (hD : IsSimpleGroup D)
    {A : Subgroup D} {a b : D} (ha : a ∈ A) (hab : a * b ≠ b * a) :
    Subgroup.normalClosure (A : Set D) = ⊤ := by
  have : (Subgroup.normalClosure (A : Set D)).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (A : Set D)) with h | h
  · have ha' : a ∈ Subgroup.normalClosure (A : Set D) := Subgroup.subset_normalClosure ha
    rw [h, Subgroup.mem_bot] at ha'
    exact absurd (by rw [ha', one_mul, mul_one]) hab
  · exact h

theorem rank2Std_of_inputs (hL2 : GMS78.L2Res) (hK3 : RankTwoAlternatingStandard) : Rank2Std := by
  intro D _ _ hD hK n A hA h2
  have hodd := standardComponentOddCore_eq_bot_of_isSimpleGroup hD hA.2.1
  have hyp : RankTwoHyp D A := ⟨kProper_catalog_of_isKGroupCat hK, hA.2.1, hA.2.2.1, h2⟩
  obtain ⟨a, haA, b, -, hab⟩ := AS76b.Lemma34.exists_not_commute hA.2.1.1
  have hX : rankTwoX A = ⊤ := normalClosure_eq_top_of_not_commute hD haA hab
  obtain ⟨hn, -, -, K, _, _, hK2, ⟨φ⟩⟩ := hA
  have hQ : StatedClassicalModel (rankTwoQuot A) .PSL 2 2 n := by
    have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK2]
    have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK'
    have hZ : Subgroup.center ↥A = ⊥ := center_eq_bot_of_mulEquiv_specialLinear_two φ
    exact statedClassicalModel_psl_two_of_mulEquiv_specialLinear_two hn hK2
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans φ))
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨e1⟩ := GMS78.nonempty_mulEquiv_psl2_of_stated hQ
    obtain ⟨e2⟩ := Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    have eTop : ↥(rankTwoX A) ≃* D := (MulEquiv.subgroupCongr hX).trans Subgroup.topEquiv
    rcases hK3 D A hyp hodd 5 le_rfl ⟨e1.trans e2⟩ with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, -, hne⟩
    · exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨eTop.symm.trans e⟩)))⟩
    · exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨eTop.symm.trans e⟩))⟩
    · exact absurd hX hne
  · exact (hL2 D A ⟨hyp.standard, hodd, hyp.not_normal, hyp.rank, Or.inl ⟨n, hn3, hQ⟩⟩ n hn3
      (GMS78.nonempty_mulEquiv_psl2_of_stated hQ)).elim

end CFSG.CGT.PushingUpLit.CGT6K1
