module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuaternionReduction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoverExcl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicBender
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverUnitary
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Assembly.LowTwoRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.ProperTwoGeneratedCore CFSG.ProperTwoGeneratedCore.Lemma37

theorem szEight_of_cyclic_core
    (hC : ∀ (G : Type) [Group G] [Finite G], CanonicalStatement G)
    {J : Type} [Group J] [Finite J] (hperf : Group.IsPerfect J)
    (hsimp : IsSimpleGroup (J ⧸ center J)) (hZ : Nat.card (center J) = 2)
    (hrk : 2 ≤ Open.twoRank J) (Q : Sylow 2 J) (B : Subgroup J) (hQB : (Q : Subgroup J) ≤ B)
    (hB : B ≠ ⊤)
    (hcyc : ∀ g : J, g ∉ B → ∀ P : Subgroup J, IsPGroup 2 P →
      (∀ p ∈ P, p ∈ B ∧ g⁻¹ * p * g ∈ B) → IsCyclic P) :
    Nonempty ((J ⧸ center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 ↥(center J) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hZne : center J ≠ ⊥ := by
    intro h
    rw [h] at hZ
    simp at hZ
  have hZcyc : IsCyclic ↥(center J) := by
    have : Fact (Nat.Prime (Nat.card ↥(center J))) := ⟨by rw [hZ]; exact Nat.prime_two⟩
    exact isCyclic_of_prime_card rfl
  obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(center J))).mp hZ
  have hy2 : y ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥(center J)) (x := y)
    rwa [hZ] at this
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  set e : J := (y : J) with he
  have heo : orderOf e = 2 := by rw [he, Subgroup.orderOf_coe]; exact hyo
  obtain ⟨E, -, hE, hEcard⟩ :=
    SU1.exists_isElemAbelian_of_le_pRank (H := (⊤ : Subgroup J)) Nat.prime_two hrk
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := (SU1.isElemAbelian_iff.mp hE).2 x hx
    rwa [pow_two] at this
  have hex : ∃ x ∈ E, x ≠ 1 ∧ x ≠ e := by
    by_contra hno
    push Not at hno
    have hle : E ≤ zpowers e := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1]; exact one_mem _
      · rw [hno x hx hx1]; exact mem_zpowers e
    have h1 := Subgroup.card_le_of_le hle
    rw [hEcard, Nat.card_zpowers, heo] at h1
    omega
  obtain ⟨x, hxE, hx1, hxe⟩ := hex
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hEsq x hxE) hx1
  have := hsimp
  have := hperf
  let π : J →* J ⧸ center J := QuotientGroup.mk' (center J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = center J := QuotientGroup.ker_mk' _
  have hZQ : center J ≤ (Q : Subgroup J) := hZ2.le_sylow_of_normal Q
  have hkerB : π.ker ≤ B := by rw [hker]; exact hZQ.trans hQB
  have hker2 : IsPGroup 2 π.ker := by rw [hker]; exact hZ2
  let Qs : Sylow 2 (J ⧸ center J) := Q.mapSurjective hπ
  have hQs : (Qs : Subgroup (J ⧸ center J)) ≤ B.map π := by
    have hQcoe : (Qs : Subgroup (J ⧸ center J)) = (Q : Subgroup J).map π :=
      Sylow.coe_mapSurjective hπ Q
    rw [hQcoe]
    exact map_mono hQB
  have hΓs : Open.properTwoGenCoreGamma (Qs : Subgroup (J ⧸ center J)) 2 ≤ B.map π :=
    CyclicCase.gamma_two_le_map_of_cyclic π hπ hkerB hker2 hcyc Qs hQs
  have hBs : B.map π ≠ ⊤ := CyclicCase.map_ne_top_of_ker_le π hkerB hB
  have hΓne : Open.properTwoGenCoreGamma (Qs : Subgroup (J ⧸ center J)) 2 ≠ ⊤ :=
    fun h => hBs (top_le_iff.mp (h ▸ hΓs))
  have hnonab : ∃ a b : J ⧸ center J, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hc : center (J ⧸ center J) = ⊤ :=
      eq_top_iff.mpr fun a _ => mem_center_iff.mpr fun g => hab g a
    rw [Group.IsPerfect.center_quotient_center_eq_bot J] at hc
    exact bot_ne_top hc
  have heven : Even (Nat.card (J ⧸ center J)) := by
    have h4 : 4 ∣ Nat.card J := by
      have := Subgroup.card_subgroup_dvd_card E
      rwa [hEcard] at this
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (center J)
    rw [hZ] at hmul
    obtain ⟨m, hm⟩ := h4
    rw [hmul] at hm
    exact ⟨m, by omega⟩
  have h2 : 2 ≤ Open.twoRank (J ⧸ center J) :=
    CFSG.Assembly.LowTwoRank.two_le_twoRank (J ⧸ center J) hnonab heven
  have hne2 : Open.twoRank (J ⧸ center J) ≠ 2 := fun h =>
    hxe (rankTwoCoverStatement J hperf.commutator_eq_top hZ2 hZne hZcyc hsimp h x e hxo heo)
  have h3 : 3 ≤ Open.pRank 2 (Qs : Subgroup (J ⧸ center J)) := by
    rw [sylow_two_rank_eq Qs]
    omega
  rcases hC (J ⧸ center J) hsimp hnonab Qs h3 hΓne with hΓ1 | ⟨⟨e1⟩⟩
  · have hBender : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ center J) :=
      CyclicCase.isBenderGroup_of_gamma_one_ne_top Qs h2 hΓ1
    rcases bender_cover_quotient hperf.commutator_eq_top hZ hBender with ⟨⟨e2⟩⟩ | h
    · exact absurd (CFSG.GH74.twoRank_eq_of_mulEquiv_psl2Model (by norm_num) e2) hne2
    · exact h
  · exact absurd (center_eq_bot_of_quotient_jOne hperf.commutator_eq_top e1) hZne

theorem qpcc_of_quaternion_canonical
    (hq : QuasisimpleQuaternionCoreClassification)
    (hC : ∀ (G : Type) [Group G] [Finite G], CanonicalStatement G) :
    QuasisimpleProperCoreClassification := by
  intro J _ _ hperf hsimp hZ hrk Q B hQB hB hΓ
  by_cases hnc : ∃ j : J, j ∉ B ∧ ∃ P : Subgroup J, IsPGroup 2 P ∧ ¬ IsCyclic P ∧
      ∀ p ∈ P, p ∈ B ∧ j⁻¹ * p * j ∈ B
  · exact hq J hperf hsimp hZ hrk Q B hQB hB hΓ hnc
  · refine Or.inr (szEight_of_cyclic_core hC hperf hsimp hZ hrk Q B hQB hB ?_)
    intro g hg P hP hPB
    by_contra hPc
    exact hnc ⟨g, hg, P, hP, hPc, hPB⟩

end CFSG.GH74.Uniqueness.SU.K.R6
