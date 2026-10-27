module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank TauCeti CFSG.LieType.SeitzGeneration
  CFSG.Models CFSG.SectionRank.ClassicalEven Matrix

theorem three_dvd_card_of_order_three {G : Type*} [Group G] [Finite G] (x : G) (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) : 3 ∣ Nat.card G := by
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
  have h3 : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  rw [← h3]
  exact orderOf_dvd_natCard x

theorem three_dvd_card_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {x : GL ι K} (hxH : x ∈ H) (hx : x ^ 3 = 1)
    (hx1 : x ∉ StatedScalars ι K) : 3 ∣ Nat.card (StatedProj H) := by
  let π : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)
  refine three_dvd_card_of_order_three (π ⟨x, hxH⟩) ?_ ?_
  · rw [← map_pow]
    have : (⟨x, hxH⟩ : H) ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hx)
    rw [this, map_one]
  · intro h
    apply hx1
    have := (QuotientGroup.eq_one_iff _).1 h
    simpa [Subgroup.mem_subgroupOf] using this

theorem three_dvd_card_psl {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) :
    3 ∣ Nat.card (StatedProj (StatedSL n K)) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine three_dvd_card_statedProj (x := rotGL (K := K) i0 i1)
    (Subgroup.subset_closure (det_rotMatrix _ _)) (rotGL_pow_three _ _) fun hx => ?_
  exact mul_scalar_ne (g := 1) h01 (one_mulVec _) (rotMatrix_mulVec_left _ _) hx (one_mul _)

theorem three_dvd_card_of_two_le_pRank {S : Type} [Group S] [Finite S]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)) : 3 ∣ Nat.card S := by
  obtain ⟨E, -, -, hE⟩ := exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup S)
  have h3 : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  exact h3.trans (Subgroup.card_subgroup_dvd_card E)

theorem A_three_dvd_card {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    {S : Type} [Group S] [Finite S] (e : S ≃* Cat ⟨.A r q, hv⟩) : 3 ∣ Nat.card S := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hmodel : StatedClassicalModel S .PSL (r + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (lieModel_A r q hv e)
  obtain ⟨-, K, _, _, -, ⟨eK⟩⟩ := hmodel
  rw [Nat.card_congr eK.toEquiv]
  exact three_dvd_card_psl (by omega)

theorem three_dvd_card_psu_three {K : Type} [Field K] [Finite K] {q : ℕ} (hq : q ≠ 0) :
    3 ∣ Nat.card (StatedProj (StatedSU 3 q K)) := by
  refine three_dvd_card_statedProj (x := glOfPowThree cycMat cycMat_pow_three) ?_
    (glOfPowThree_pow_three _ _) ?_
  · refine Subgroup.subset_closure ⟨by simpa [coe_glOfPowThree] using det_cycMat, ?_⟩
    simp only [coe_glOfPowThree]
    have hmap : (cycMat : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = cycMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cycMat, zero_pow hq]
    rw [hmap, cycMat_transpose, ← pow_succ, cycMat_pow_three]
  · intro hc
    obtain ⟨u, hu⟩ := statedScalars_eq_diagonal hc
    have := congrFun (congrFun hu 1) 0
    simp [coe_glOfPowThree, cycMat] at this

theorem twistedA_three_dvd_card {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* Cat ⟨.twistedA r q, hv⟩) : 3 ∣ Nat.card S := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  by_cases hr2 : r = 2
  · subst hr2
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
      LieTypeIndex.characteristic_twistedA 2 q
    have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
      LieTypeIndex.fieldExponent_twistedA 2 q
    have hmodel : StatedClassicalModel S .PSU 3 q.p q.exponent := by
      have := statedClassical_of_lieModel (by omega) (lieModel_twistedA 2 q hv e)
      rwa [hc, hf] at this
    obtain ⟨-, K, _, _, -, ⟨eK⟩⟩ := hmodel
    rw [Nat.card_congr eK.toEquiv]
    exact three_dvd_card_psu_three (pow_ne_zero _ q.prime_p.ne_zero)
  · exact three_dvd_card_of_two_le_pRank (twistedA_two_le_pRank_three hv e (by omega))

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls
