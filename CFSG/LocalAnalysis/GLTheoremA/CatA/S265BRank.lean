module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRankLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BActS
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

private theorem tyUnTwo_of_low {G : Type} [Group G]
    (h : catalogIs G S9.isU5two ∨ catalogIs G S9.isU6two) :
    ∃ n, 5 ≤ n ∧ n ≤ 6 ∧ catalogIs G (tyUnTwo n) := by
  rcases h with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
  · refine ⟨5, le_rfl, by norm_num, i, ?_, e⟩
    cases i with
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r q =>
        rcases r with _ | _ | _ | _ | _ | r
        all_goals first | exact hi.elim | exact ⟨rfl, hi⟩
      | _ => exact hi.elim
    | _ => exact hi.elim
  · refine ⟨6, by norm_num, le_rfl, i, ?_, e⟩
    cases i with
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r q =>
        rcases r with _ | _ | _ | _ | _ | _ | r
        all_goals first | exact hi.elim | exact ⟨rfl, hi⟩
      | _ => exact hi.elim
    | _ => exact hi.elim

private theorem rank_arith {n m c : ℕ} (hrank : 3 ^ m ≤ c) (h1 : n ≤ m + 1)
    (h2 : ¬ 3 ∣ n → n ≤ m) :
    3 ^ n ≤ 3 * c ∧ (¬ 3 ∣ n → 3 ^ n ≤ c) ∧ (7 ≤ n → 3 ^ 6 ≤ c) := by
  have hr1 : 3 ^ n ≤ 3 * c :=
    calc 3 ^ n ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) h1
      _ = 3 * 3 ^ m := pow_succ' 3 m
      _ ≤ 3 * c := Nat.mul_le_mul_left 3 hrank
  refine ⟨hr1, fun h3 => (Nat.pow_le_pow_right (by norm_num) (h2 h3)).trans hrank, fun h7 => ?_⟩
  have h : 3 * 3 ^ 6 ≤ 3 * c := (Nat.pow_le_pow_right (by norm_num) h7).trans hr1
  exact Nat.le_of_mul_le_mul_left h (by norm_num)

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem qu_data {S B T : Subgroup Ω} {x b : Ω} (hN : QUNL 3 S B T x b) {n : ℕ}
    (hcat : catalogIs (PSimple 3 (Ipart 3 S b)) (tyUnTwo n)) :
    Dgrp b x ≤ B ∧ Ipart 3 S b ≤ S ∧ IsElemAbelian 3 (Dgrp b x) ∧ Nat.card (Dgrp b x) = 9 ∧
      (∀ d ∈ Dgrp b x, ∀ j ∈ Ipart 3 S b, d * j = j * d) ∧
      CFSG.Open.IsQuasisimple (PQuot 3 (Ipart 3 S b)) := by
  have hc := hN.cfg
  obtain ⟨hDB, hD, hD9⟩ := S10.card_Dgrp hc.elem hc.prime hc.hb hc.xB hc.x1 hc.hbx
  have hJ := (hN.nlAct_of_simple (isSimpleGroup_of_tyUnTwo hcat)).comp
  have hDc : Dgrp b x ≤ Subgroup.centralizer (Ipart 3 S b : Set Ω) := by
    refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2
      (Subgroup.mem_centralizer_iff.2 fun y _ => hc.xcen y)⟩)
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 (hJ.1 hy).2 b (Set.mem_singleton b)).symm
  exact ⟨hDB, hJ.1.trans inf_le_left, hD, hD9.trans (by norm_num), fun d hd j hj =>
    (Subgroup.mem_centralizer_iff.1 (hDc hd) j hj).symm,
    isQuasisimple_pQuot_of_glaPComponent hc.prime hJ⟩

private theorem qs_data {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (hN : QSNL 3 S B T x D K)
    {n : ℕ} (hcat : catalogIs (PSimple 3 K) (tyUnTwo n)) :
    D ≤ B ∧ K ≤ S ∧ IsElemAbelian 3 D ∧ Nat.card D = 9 ∧ (∀ d ∈ D, ∀ j ∈ K, d * j = j * d) ∧
      CFSG.Open.IsQuasisimple (PQuot 3 K) := by
  have hc := hN.cfg
  obtain ⟨hDB, hD, hD9, -, -, -, hDK⟩ := hc.std
  haveI := isSimpleGroup_of_tyUnTwo hcat
  have hJ := (hN.nlAct (T123C.dvd_card_of_nontrivial_pSimple hc.prime (X := K) inferInstance)).comp
  exact ⟨hDB, hJ.1.trans inf_le_left, hD, hD9.trans (by norm_num), fun d hd j hj =>
    (Subgroup.mem_centralizer_iff.1 (hDK.le hd).2 j hj).symm,
    isQuasisimple_pQuot_of_glaPComponent hc.prime hJ⟩

private theorem false_of_comm {S B T E : Subgroup Ω} (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set Ω)) (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B)
    (hB : Nat.card B = 3 ^ 5) (hT : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) (hEBS : E ≤ B ⊔ S)
    (hE : IsElemAbelian 3 E) (hE6 : 3 ^ 6 ≤ Nat.card E) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTB2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) :=
    hT2.to_le (Subgroup.le_normalizer_iff_commutator_le_left.1 hBT)
  have hEN : E ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) :=
    hEBS.trans (sup_le (Subgroup.normalizer_commutator_ge_right T B)
      ((Subgroup.le_centralizer_iff.1 hc).trans (Subgroup.centralizer_le_normalizer _)))
  have h := GL83.PiGen.card_le_pow_twoLocalRank hE hTB2 hT hEN
  have h56 : (3 : ℕ) ^ 6 ≤ 3 ^ 5 := hE6.trans (h.trans (hrank.trans hB.le))
  norm_num at h56


theorem QUNL.exists_elem_six {S B T : Subgroup Ω} {x b : Ω} (hN : QUNL 3 S B T x b)
    (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU5two ∨
      catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU6two) :
    ∃ E : Subgroup Ω, E ≤ Dgrp b x ⊔ Ipart 3 S b ∧ IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E := by
  obtain ⟨n, hn5, hn6, hcat⟩ := tyUnTwo_of_low hJ
  obtain ⟨-, -, hD, hD9, hDJ, hq⟩ := qu_data hN hcat
  exact BRank.exists_elem_six hD hD9 hDJ hq hn5 hn6 hcat

theorem QUNL.false_of_comm_le_centralizer {S B T : Subgroup Ω} {x b : Ω}
    (hN : QUNL 3 S B T x b)
    (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU5two ∨
      catalogIs (PSimple 3 (Ipart 3 S b)) S9.isU6two)
    (hB : Nat.card B = 3 ^ 5) (hT : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) : False := by
  obtain ⟨E, hEDJ, hE, hE6⟩ := hN.exists_elem_six hJ
  obtain ⟨n, -, -, hcat⟩ := tyUnTwo_of_low hJ
  obtain ⟨hDB, hJS, -⟩ := qu_data hN hcat
  exact false_of_comm hN.cfg.two hN.cfg.bnorm hN.cfg.rank hB hT hc
    (hEDJ.trans (sup_le_sup hDB hJS)) hE hE6

theorem QSNL.exists_elem_six {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (hN : QSNL 3 S B T x D K)
    (hK : catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two) :
    ∃ E : Subgroup Ω, E ≤ D ⊔ K ∧ IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E := by
  obtain ⟨n, hn5, hn6, hcat⟩ := tyUnTwo_of_low hK
  obtain ⟨-, -, hD, hD9, hDJ, hq⟩ := qs_data hN hcat
  exact BRank.exists_elem_six hD hD9 hDJ hq hn5 hn6 hcat

theorem QSNL.false_of_comm_le_centralizer {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (hN : QSNL 3 S B T x D K)
    (hK : catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two)
    (hB : Nat.card B = 3 ^ 5) (hT : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) : False := by
  obtain ⟨E, hEDK, hE, hE6⟩ := hN.exists_elem_six hK
  obtain ⟨n, -, -, hcat⟩ := tyUnTwo_of_low hK
  obtain ⟨hDB, hKS, -⟩ := qs_data hN hcat
  exact false_of_comm hN.cfg.two hN.cfg.bnorm hN.cfg.rank hB hT hc
    (hEDK.trans (sup_le_sup hDB hKS)) hE hE6

theorem quBRank_holds : QUBRank := by
  intro Ω _ _ S B T x b n hN hn5 _ hcat
  obtain ⟨-, -, hD, hD9, hDJ, hq⟩ := qu_data hN hcat
  obtain ⟨h1, h2⟩ := BRank.le_twoLocalRank_add_one hD hD9 hDJ hq hn5 hcat
  obtain ⟨r1, r2, r3⟩ := rank_arith hN.cfg.rank h1 h2
  refine ⟨⟨r1, r2⟩, ?_⟩
  by_cases hn6 : n ≤ 6
  · exact (BRank.exists_elem_six hD hD9 hDJ hq hn5 hn6 hcat).imp fun _ h => h.2
  · exact ⟨B, hN.cfg.elem, r3 (by omega)⟩

theorem qsBRank_holds : QSBRank := by
  intro Ω _ _ S B T x D K n hN hn5 _ hcat
  obtain ⟨-, -, hD, hD9, hDJ, hq⟩ := qs_data hN hcat
  obtain ⟨h1, h2⟩ := BRank.le_twoLocalRank_add_one hD hD9 hDJ hq hn5 hcat
  obtain ⟨r1, r2, r3⟩ := rank_arith hN.cfg.rank h1 h2
  refine ⟨⟨r1, r2⟩, ?_⟩
  by_cases hn6 : n ≤ 6
  · exact (BRank.exists_elem_six hD hD9 hDJ hq hn5 hn6 hcat).imp fun _ h => h.2
  · exact ⟨B, hN.cfg.elem, r3 (by omega)⟩

end CFSG.LocalAnalysis.GLTheoremA.S265

end
