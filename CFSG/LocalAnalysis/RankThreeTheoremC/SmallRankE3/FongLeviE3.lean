module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviL3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviU4Typed

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

theorem valid_A_one_of_ten_le {q : PrimePower} (h : 10 ≤ q.card) :
    (LieTypeIndex.A 1 q).Valid := by
  refine (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 ⟨le_rfl, fun _ => ?_⟩, ?_⟩
  · omega
  · rw [LieTypeIndex.isDuplicateRepresentative_iff]
    omega

theorem five_le_of_eq_mul {p e f₀ : ℕ} (hp5 : 5 ≤ p) (he : 0 < e) (h : e = p * f₀) : 5 ≤ e := by
  rcases Nat.eq_zero_or_pos f₀ with h0 | h0
  · subst h0
    simp at h
    omega
  · calc 5 ≤ p := hp5
      _ = p * 1 := (mul_one p).symm
      _ ≤ p * f₀ := Nat.mul_le_mul_left p h0
      _ = e := h.symm

theorem l3_e3_conclusion {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K ≤ 1) (hz : orderOf z = p)
    (hzK₀ : z ∈ K₀)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) (hne : K₀ ≠ K)
    (hBK₀ : B ≤ normalizer (K₀ : Set A)) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.A 2 q).Valid) (e : ↥K ≃* ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩)
    (hq5 : 5 ≤ q.exponent) :
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex d.1 ∧
        ∃ φ : ↥H →* (CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H := by
  have hcard : 10 ≤ q.card := by
    rw [PrimePower.card_def, hq2]
    calc 10 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hq5
  have hv' := valid_A_one_of_ten_le hcard
  have hpkg := l3_levi_pkg hp hp5 hKr hpar hne hz hzK₀ hq2 hv e hv'
  exact conclusion_of_pkg (d := ⟨.A 1 q, hv'⟩) hBK₀ (by simpa using hq2) (by simp)
    (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hpkg

theorem u4_e3_conclusion {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K ≤ 1) (hz : orderOf z = p)
    (hzK₀ : z ∈ K₀)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) (hne : K₀ ≠ K)
    (hBK₀ : B ≤ normalizer (K₀ : Set A)) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.twistedA 3 q).Valid)
    (e : ↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) (hm : 2 ≤ q.exponent) :
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex d.1 ∧
        ∃ φ : ↥H →* (CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H := by
  let q' : PrimePower := ⟨2, 2 * q.exponent, Nat.prime_two, by omega⟩
  have hcard : 10 ≤ q'.card := by
    rw [PrimePower.card_def]
    show 10 ≤ 2 ^ (2 * q.exponent)
    calc 10 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * q.exponent) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hv' := valid_A_one_of_ten_le hcard
  have hpkg := u4_levi_pkg hp hp5 hKr hpar hne hz hzK₀ hq2 hm hv e (q' := q') rfl rfl hv'
  exact conclusion_of_pkg (d := ⟨.A 1 q', hv'⟩) hBK₀ (by simp [q'])  (by simp)
    (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hpkg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
