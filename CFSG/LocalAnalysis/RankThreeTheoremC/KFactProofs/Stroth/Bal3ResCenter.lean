module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Covers
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHighCover
public import CFSG.HardMathSupport.Timmesfeld.LieRank.U43
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLieModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.HardMathSupport.Timmesfeld.LinearRank
open CFSG.HardMathSupport.Timmesfeld.LieRank
open CFSG.RankThree.PerfectCover (hopfMultiplier)

section Arith

theorem card_eq_three_of_dvd {Z : Type} [Group Z] [Finite Z] (hZ : IsPGroup 3 Z)
    (h3 : 3 ∣ Nat.card Z) {T : ℕ} (hT : Nat.card Z ∣ T) (h9 : ¬ 9 ∣ T) : Nat.card Z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ
  rcases k with _ | _ | k
  · rw [hk] at h3
    norm_num at h3
  · simpa using hk
  · exfalso
    apply h9
    have : (9 : ℕ) ∣ Nat.card Z := by
      rw [hk]
      exact ⟨3 ^ k, by ring⟩
    exact this.trans hT

theorem not_nine_dvd_of_dvd_three {g a b : ℕ} (hg : g ∣ 3) (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) :
    ¬ 9 ∣ g * 1 * (a * b) := by
  intro h9
  have h1 : 3 * 3 ∣ 3 * (a * b) := by
    have := h9.trans (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right hg 1) (a * b))
    simpa using this
  have h2 : 3 ∣ a * b := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h2 with h | h
  · exact ha h
  · exact hb h

end Arith

section LinearRank

variable {K : Type} [Group K] [Finite K]

theorem sub_one_le_pRank_psl (hGA : GriessAllModelsStatement) (hperf : Group.IsPerfect K)
    (hZ : 3 ∣ Nat.card (center K)) {n r f : ℕ} (hn : 4 ≤ n)
    (hcl : StatedClassicalModel (K ⧸ center K) .PSL n r f)
    (ha : 3 ∣ (genericOrders .PSL n r f).1) : n - 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm := hcl.1
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  obtain ⟨-, K', _, _, hK, ⟨e'⟩⟩ := hcl
  have hga : (genericOrders .PSL n r f).1 = Nat.gcd n (r ^ f - 1) := rfl
  have hpq : 3 ∣ r ^ f - 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
  have hH : (Nat.card K' = r ^ f ∧ StatedSL n K' = StatedSL n K' ∧ 3 ∣ r ^ f - 1) ∨
      (Nat.card K' = (r ^ f) ^ 2 ∧ StatedSL n K' = StatedSU n (r ^ f) K' ∧ 3 ∣ r ^ f + 1) :=
    Or.inl ⟨hK, rfl, hpq⟩
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSL n K')) .PSL n r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, K', inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA hmm
  have hdv : (genericOrders .PSL n r f).1 ∣
      Nat.card ((StatedScalars (Fin n) K').subgroupOf (StatedSL n K')) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.dvd_card_scalars (q := r ^ f) (by omega) hq0
      (Or.inl ⟨hK, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have := hfin
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL n K')))).factorization 3 ≤
      (Nat.card ((StatedScalars (Fin n) K').subgroupOf (StatedSL n K'))).factorization 3 := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inl rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd
      (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos hadm).ne'
      Nat.card_pos.ne').2 hdv 3
  exact rank_ge_cover hperf hr hp hp2 hn (H := StatedSL n K') hH e' hZ hM

theorem sub_one_le_pRank_psu (hGA : GriessAllModelsStatement) (hperf : Group.IsPerfect K)
    (hZ : 3 ∣ Nat.card (center K)) {n r f : ℕ} (hn : 4 ≤ n)
    (hcl : StatedClassicalModel (K ⧸ center K) .PSU n r f)
    (ha : 3 ∣ (genericOrders .PSU n r f).1) : n - 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm := hcl.1
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  obtain ⟨-, K', _, _, hK, ⟨e'⟩⟩ := hcl
  have hga : (genericOrders .PSU n r f).1 = Nat.gcd n (r ^ f + 1) := rfl
  have hpq : 3 ∣ r ^ f + 1 := by rw [hga] at ha; exact ha.trans (Nat.gcd_dvd_right _ _)
  have hH : (Nat.card K' = r ^ f ∧ StatedSU n (r ^ f) K' = StatedSL n K' ∧ 3 ∣ r ^ f - 1) ∨
      (Nat.card K' = (r ^ f) ^ 2 ∧ StatedSU n (r ^ f) K' = StatedSU n (r ^ f) K' ∧
        3 ∣ r ^ f + 1) :=
    Or.inr ⟨hK, rfl, hpq⟩
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSU n (r ^ f) K')) .PSU n r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, K', inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA hmm
  have hdv : (genericOrders .PSU n r f).1 ∣
      Nat.card ((StatedScalars (Fin n) K').subgroupOf (StatedSU n (r ^ f) K')) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.dvd_card_scalars (q := r ^ f) (by omega) hq0
      (Or.inr ⟨hK, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have := hfin
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU n (r ^ f) K')))).factorization 3 ≤
      (Nat.card ((StatedScalars (Fin n) K').subgroupOf
        (StatedSU n (r ^ f) K'))).factorization 3 := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inr rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd
      (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos hadm).ne'
      Nat.card_pos.ne').2 hdv 3
  exact rank_ge_cover hperf hr hp hp2 hn (H := StatedSU n (r ^ f) K') hH e' hZ hM

theorem five_le_pRank_of_u43 (h3 : 3 ∣ Nat.card (center K)) {X : Type} [Group X]
    (e : K ⧸ center K ≃* X) (hm : CFSG.Models.LieModel X .PSU 4 3 1) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨e1⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.nonempty_mulEquiv_X₀_of_classical hcl
  have e' := e.trans e1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center K)) 3 h3
  have hzL : orderOf (z : K) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  let φ : K →* CFSG.LieType.Multipliers.U43.X₀ :=
    (e' : K ⧸ center K →* _).comp (QuotientGroup.mk' (center K))
  have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = center K := by
    ext x
    simp [φ]
  have hz3 : (z : K) ^ 3 = 1 := by rw [← hzL]; exact pow_orderOf_eq_one _
  exact five_le_pRank_of_cover φ hφ hker.le (Z := Subgroup.zpowers (z : K))
    (by rw [hker]; exact Subgroup.zpowers_le.mpr z.2)
    (fun w hw => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow])
    (by rw [Nat.card_zpowers, hzL])

end LinearRank

theorem bal3ThreeCenter_of_tables (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : Bal3ThreeCenter := by
  intro K _ _ hq hcat hZne hZp hrk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq' : CFSG.IsQuasisimple K := isQuasisimple_of_open' hq
  have hperf : Group.IsPerfect K := ⟨hq.1⟩
  have h3 : 3 ∣ Nat.card (center K) := by
    have h1 : 1 < Nat.card (center K) := (Subgroup.one_lt_card_iff_ne_bot _).2 hZne
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZp
    rcases k with _ | k
    · rw [hk] at h1
      norm_num at h1
    · rw [hk]
      exact ⟨3 ^ k, by ring⟩
  suffices hc : Nat.card (center K) = 3 from
    ⟨isCyclic_of_prime_card (p := 3) hc, hc⟩
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr => exact (GL83.I243.CoverList.false_of_cyclic hq' e).elim
  | alternating n hn =>
    have hdvd := GL83.I243.CoverList.card_center_dvd_alternating hAlt hq' hn e
    refine card_eq_three_of_dvd hZp h3 hdvd ?_
    split_ifs <;> norm_num
  | sporadic s =>
    have hdvd := (GL83.I243.CoverList.card_center_dvd_sporadic hSpor hq' e).trans
      (GL83.I243.CoverList.sporadicMultiplierOrder_dvd_twelve s)
    exact card_eq_three_of_dvd hZp h3 hdvd (by norm_num)
  | lie d =>
    obtain ⟨t, n, p0, f, hm, -, -, -, -⟩ := GL83.I243.CoverList.exists_lieModel_spec d
    have htab := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA hq' e hm
    have hmK := models_lieModel_of_mulEquiv e.symm hm
    rcases case_of_dvd_table Nat.prime_three (by norm_num) (h3.trans htab) with
      ⟨rfl, hg⟩ | ⟨rfl, hg⟩ | ⟨⟨rfl, -, hd⟩ | ⟨rfl, -, hd⟩⟩ | ⟨-, hx⟩
    ·
      have hadm := hm.1
      have hn2 : 2 ≤ n := hadm.2.2.1
      have hga : 3 ∣ (genericOrders .PSL n p0 f).1 := hg
      have hpn : 3 ∣ n := hg.trans (Nat.gcd_dvd_left _ _)
      by_cases hn4 : 4 ≤ n
      · exfalso
        have hcl : StatedClassicalModel (K ⧸ center K) .PSL n p0 f := by
          rcases hmK.2 with h | ⟨h0, -⟩
          · exact h
          · omega
        have := sub_one_le_pRank_psl hGA hperf h3 hn4 hcl hga
        omega
      · have hn3 : n = 3 := by omega
        subst hn3
        obtain ⟨hc1, hc2⟩ := not_dvd_exceptional_of_dvd_generic Nat.prime_three (by norm_num) hga
        refine card_eq_three_of_dvd hZp h3 htab ?_
        exact not_nine_dvd_of_dvd_three (Nat.gcd_dvd_left _ _) hc1 hc2
    ·
      have hadm := hm.1
      have hn3 : 3 ≤ n := hadm.2.2.1
      have hga : 3 ∣ (genericOrders .PSU n p0 f).1 := hg
      have hpn : 3 ∣ n := hg.trans (Nat.gcd_dvd_left _ _)
      by_cases hn4 : 4 ≤ n
      · exfalso
        have hcl : StatedClassicalModel (K ⧸ center K) .PSU n p0 f := by
          rcases hmK.2 with h | ⟨h0, -⟩
          · exact h
          · omega
        have := sub_one_le_pRank_psu hGA hperf h3 hn4 hcl hga
        omega
      · have hn3' : n = 3 := by omega
        subst hn3'
        obtain ⟨hc1, hc2⟩ := not_dvd_exceptional_of_dvd_generic Nat.prime_three (by norm_num) hga
        refine card_eq_three_of_dvd hZp h3 htab ?_
        exact not_nine_dvd_of_dvd_three (Nat.gcd_dvd_left _ _) hc1 hc2
    ·
      have hga : 3 ∣ (genericOrders .E6 n p0 f).1 := by
        show 3 ∣ Nat.gcd 3 (p0 ^ f - 1)
        exact Nat.dvd_gcd dvd_rfl hd
      obtain ⟨hc1, hc2⟩ := not_dvd_exceptional_of_dvd_generic Nat.prime_three (by norm_num) hga
      refine card_eq_three_of_dvd hZp h3 htab ?_
      exact not_nine_dvd_of_dvd_three (Nat.gcd_dvd_left _ _) hc1 hc2
    ·
      have hga : 3 ∣ (genericOrders .twistedE6 n p0 f).1 := by
        show 3 ∣ Nat.gcd 3 (p0 ^ f + 1)
        exact Nat.dvd_gcd dvd_rfl hd
      obtain ⟨hc1, hc2⟩ := not_dvd_exceptional_of_dvd_generic Nat.prime_three (by norm_num) hga
      refine card_eq_three_of_dvd hZp h3 htab ?_
      exact not_nine_dvd_of_dvd_three (Nat.gcd_dvd_left _ _) hc1 hc2
    ·
      rcases hx with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl, rfl⟩
      · refine card_eq_three_of_dvd hZp h3 htab ?_
        norm_num [genericOrders, exceptionalOrders]
      · refine card_eq_three_of_dvd hZp h3 htab ?_
        norm_num [genericOrders, exceptionalOrders]
      · refine card_eq_three_of_dvd hZp h3 htab ?_
        norm_num [genericOrders, exceptionalOrders]
      · exfalso
        have := five_le_pRank_of_u43 h3 (MulEquiv.refl (K ⧸ center K)) hmK
        omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
