module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaReduction
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeSp
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeUni
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeOmTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega Module

private theorem five_pow_six_dvd_of_formula {q n D e c : ℕ} {ε : ℤ} (hq : 1 ≤ q)
    (hε : ε = 1 ∨ ε = -1) (hD : (D : ℤ) = (q : ℤ) - ε) (h5D : 5 ∣ D) (hn5 : ¬ 5 ∣ n)
    (hn : 6 ≤ n)
    (hc : c = (q ^ e * ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - ε ^ i).toNat) / Nat.gcd n D) :
    5 ^ 6 ∣ c := by
  have h5 : (5 : ℤ) ∣ (q : ℤ) - ε := by rw [← hD]; exact_mod_cast h5D
  set T : ℕ → ℕ := fun i => ((q : ℤ) ^ i - ε ^ i).toNat with hT
  have hT5 : ∀ i, 5 ∣ T i := fun i => FiveDiagAux.five_dvd_toNat_pow_sub hq hε h5 i
  have hT25 : 25 ∣ T 5 := FiveDiagAux.twentyfive_dvd_toNat_pow_five hq hε h5
  have hTD : ∀ i, D ∣ T i := by
    intro i
    have h1 : (D : ℤ) ∣ (q : ℤ) ^ i - ε ^ i := by rw [hD]; exact sub_dvd_pow_sub_pow _ _ _
    have h2 : (D : ℤ) ∣ ((T i : ℕ) : ℤ) := by
      rw [hT]
      dsimp only
      rw [FiveDiagAux.toNat_pow_sub hq hε i]
      exact h1
    exact_mod_cast h2
  have hprod6 : ∏ i ∈ Finset.Icc 2 6, T i = T 2 * T 3 * T 4 * T 5 * T 6 := by
    rw [show Finset.Icc 2 6 = {2, 3, 4, 5, 6} from by decide]
    simp [Finset.prod_insert, mul_assoc]
  have h56 : 5 ^ 6 ∣ ∏ i ∈ Finset.Icc 2 6, T i := by
    rw [hprod6]
    have h := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (hT5 2) (hT5 3)) (hT5 4)) hT25)
      (hT5 6)
    have e5 : (5 * 5 * 5 * 25 * 5 : ℕ) = 5 ^ 6 := by norm_num
    rwa [e5] at h
  have hM6 : 5 ^ 6 ∣ q ^ e * ∏ i ∈ Finset.Icc 2 n, T i :=
    (h56.trans (Finset.prod_dvd_prod_of_subset _ _ _
      (Finset.Icc_subset_Icc le_rfl hn))).mul_left _
  have hgM : Nat.gcd n D ∣ q ^ e * ∏ i ∈ Finset.Icc 2 n, T i := by
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    exact ((Nat.gcd_dvd_right n D).trans (hTD 2)).trans
      ((Finset.dvd_prod_of_mem T h2).mul_left _)
  have hcM : c * Nat.gcd n D = q ^ e * ∏ i ∈ Finset.Icc 2 n, T i := by
    rw [hc]
    exact Nat.div_mul_cancel hgM
  have hcop : Nat.Coprime (5 ^ 6) (Nat.gcd n D) :=
    Nat.Coprime.pow_left 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2
      (fun h => hn5 (h.trans (Nat.gcd_dvd_left n D))))
  exact hcop.dvd_of_dvd_mul_right (by rw [hcM]; exact hM6)

private theorem not_five_pow_six_dvd {K : Type} [Group K] [Finite K] (S : Sylow 5 K)
    (hS : Nat.card S = 5 ^ 5) : ¬ 5 ^ 6 ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro h
  have h' := S.pow_dvd_card_of_pow_dvd_card h
  rw [hS] at h'
  exact absurd (Nat.le_of_dvd (by norm_num) h') (by norm_num)

private theorem not_five_dvd_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ5 : ℓ ≠ 5) : ¬ 5 ∣ ℓ ^ f :=
  fun h => hℓ5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hℓ).1
    (Nat.prime_five.dvd_of_dvd_pow h)).symm

private theorem commOrRank_psl {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSL n ℓ f) (hℓ5 : ℓ ≠ 5) (hdiag : ¬ FiveDiagType K)
    (S : Sylow 5 K) (hS : Nat.card S = 5 ^ 5) : I294Large.CommOrRank 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hp, hf, hn2, -⟩, F, _, _, hF, ⟨e⟩⟩ := id hm
  have h5q : ¬ 5 ∣ ℓ ^ f := not_five_dvd_pow hp hℓ5
  haveI : Fintype F := Fintype.ofFinite F
  have hrF' : ¬ 5 ∣ Fintype.card F := by rw [← Nat.card_eq_fintype_card, hF]; exact h5q
  have hGL : ∀ P : Sylow 5 (GL (Fin n) F), Nonempty (P ≃* sigmaModel 5
      (orderOf (Fintype.card F : ZMod 5))
      (padicValNat 5 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 5) - 1)) n) :=
    fun P => sylow_GL (Nat.prime_five.odd_of_ne_two (by norm_num)) F hrF' n P
  refine I294Large.CommOrRank.of_mulEquiv Nat.prime_five e.symm ?_
  by_cases hA : 5 ∣ Nat.card F - 1
  · have hA' : 5 ∣ ℓ ^ f - 1 := by rwa [← hF]
    have hn5 : ¬ 5 ∣ n := fun h => hdiag (Or.inl ⟨n, ℓ, f, hm, Nat.dvd_gcd h hA'⟩)
    have he : orderOf (Fintype.card F : ZMod 5) = 1 := by
      rw [orderOf_eq_one_iff, ← Nat.card_eq_fintype_card]
      have h1 : (((Nat.card F - 1 : ℕ)) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hA
      have hpos : 1 ≤ Nat.card F := Nat.card_pos
      rw [Nat.cast_sub hpos, Nat.cast_one, sub_eq_zero] at h1
      exact h1
    by_cases hnr : n < 5
    · have hc := sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_five
        (G := GL (Fin n) F) (e := orderOf (Fintype.card F : ZMod 5))
        (a := padicValNat 5 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 5) - 1)) (N := n)
        (by rw [he, Nat.div_one]; exact hnr) hGL
      exact Or.inl (sylow_comm_of_surjective (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) (sylow_comm_of_subgroup (StatedSL n F) hc))
    · exfalso
      have hn6 : 6 ≤ n := by omega
      have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hp.pos
      have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by omega) hm
      have hprod : ∏ i ∈ Finset.Icc 2 n, ((ℓ ^ f) ^ i - 1) =
          ∏ i ∈ Finset.Icc 2 n, ((((ℓ ^ f : ℕ) : ℤ)) ^ i - 1 ^ i).toNat :=
        Finset.prod_congr rfl fun i _ => (FiveDiagAux.toNat_pow_sub_one_eq hq i).symm
      rw [hprod] at hcard
      exact not_five_pow_six_dvd S hS (five_pow_six_dvd_of_formula (q := ℓ ^ f) (D := ℓ ^ f - 1)
        (e := n * (n - 1) / 2) (ε := 1) hq (Or.inl rfl)
        (by rw [Nat.cast_sub hq]; push_cast; ring) hA' hn5 hn6 hcard)
  · have hamb : I294Large.CommOrRank 5 (GL (Fin n) F) :=
      I294Large.CommOrRank.of_sylow_sigmaModel Nat.prime_five
        (PSLCross.one_le_padicValNat_card Nat.prime_five hrF') hGL
    haveI : (StatedSL n F).Normal := by
      rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]; infer_instance
    have hSL : I294Large.CommOrRank 5 ↥(StatedSL n F) :=
      I294Large.CommOrRank.of_normal_coprime_index Nat.prime_five _
        (fun hd => hA (hd.trans (PSLCross.index_statedSL_dvd n))) hamb
    exact I294Large.CommOrRank.of_surjective_coprime_ker Nat.prime_five (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
      (by
        rw [QuotientGroup.ker_mk']
        exact fun hd => hA (hd.trans (PSLCross.card_scalars_subgroupOf_dvd n))) hSL

private theorem commOrRank_psu {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSU n ℓ f) (hℓ5 : ℓ ≠ 5) (hdiag : ¬ FiveDiagType K)
    (S : Sylow 5 K) (hS : Nat.card S = 5 ^ 5) : I294Large.CommOrRank 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hp, hf, hn3, -⟩, F, _, _, hF, ⟨e⟩⟩ := id hm
  have h5q : ¬ 5 ∣ ℓ ^ f := not_five_dvd_pow hp hℓ5
  refine I294Large.CommOrRank.of_mulEquiv Nat.prime_five e.symm ?_
  by_cases hA : 5 ∣ ℓ ^ f + 1
  · have hn5 : ¬ 5 ∣ n := fun h => hdiag (Or.inr ⟨n, ℓ, f, hm, Nat.dvd_gcd h hA⟩)
    by_cases hnr : n < 5
    · exact Or.inl (I294LargeUni.sylow_comm_PSU_of_dvd Nat.prime_five le_rfl hF h5q
        (by omega) hnr hA)
    · exfalso
      have hn6 : 6 ≤ n := by omega
      have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hp.pos
      have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu (by omega) hm
      exact not_five_pow_six_dvd S hS (five_pow_six_dvd_of_formula (q := ℓ ^ f) (D := ℓ ^ f + 1)
        (e := n * (n - 1) / 2) (ε := -1) hq (Or.inr rfl) (by push_cast; ring) hA hn5 hn6 hcard)
  · exact I294LargeUni.commOrRank_PSU_of_not_dvd Nat.prime_five le_rfl hp hF h5q (by omega) hA

private theorem commOrRank_psp {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSp n ℓ f) (hℓ5 : ℓ ≠ 5) : I294Large.CommOrRank 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hp, hf, hn2, -⟩, F, _, _, hF, ⟨e⟩⟩ := id hm
  haveI : Fintype F := Fintype.ofFinite F
  have hrF' : ¬ 5 ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]; exact not_five_dvd_pow hp hℓ5
  have hSp : I294Large.CommOrRank 5 (StatedSp n F) :=
    I294Large.CommOrRank.of_sylow_sigmaModel Nat.prime_five
      (PSLCross.one_le_padicValNat_card Nat.prime_five hrF')
      (fun P => sylow_Sp (Nat.prime_five.odd_of_ne_two (by norm_num)) F hrF' n P)
  refine I294Large.CommOrRank.of_mulEquiv Nat.prime_five e.symm ?_
  exact I294Large.CommOrRank.of_surjective_coprime_ker Nat.prime_five (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _)
    (I294Large.not_dvd_card_ker_statedSp Nat.prime_five le_rfl (by omega)) hSp

private theorem commOrRank_pOmegaOdd {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .POmegaOdd n ℓ f) (hℓ5 : ℓ ≠ 5) :
    I294Large.CommOrRank 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hp, hf, hn, hp2⟩, F, _, _, hF, ⟨e⟩⟩ := id hm
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ 5 ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]; exact not_five_dvd_pow hp hℓ5
  have hodd' : Odd (Fintype.card F) := by
    rw [← Nat.card_eq_fintype_card, hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_of_char_two h
    rw [Nat.odd_iff] at hodd'
    omega
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := F) (n := n)
    (Ring.two_ne_zero h2) hn
  have hdim : finrank F (Fin n ⊕ Fin n ⊕ Unit → F) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_odd (p := 5) (by norm_num) hodd' hpq hdim
    hQnd
  refine I294Large.CommOrRank.of_mulEquiv Nat.prime_five e.symm ?_
  exact I294Large.CommOrRank.of_projOmega (CFSG.LieType.Universal.Spin.coe_quadOdd n F) hQnd hT
    Nat.prime_five (by norm_num)
    (I294Large.CommOrRank.of_sylow_sigmaModel Nat.prime_five (one_le_weirA hpq) hN)

private theorem commOrRank_pOmegaPlus {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .POmegaPlus n ℓ f) (hℓ5 : ℓ ≠ 5) :
    I294Large.CommOrRank 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hp, hf, hn⟩, F, _, _, hF, ⟨e⟩⟩ := id hm
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ 5 ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]; exact not_five_dvd_pow hp hℓ5
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := n)
    (by omega)
  have hdim : finrank F (Fin n ⊕ Fin n → F) = 2 * n := finrank_quadPlus_space n
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even (p := 5) (by norm_num) hpq (by omega)
    hdim hQnd (ε := 1) (Or.inl ⟨rfl, isPlusType_quadPlus F n⟩)
  refine I294Large.CommOrRank.of_mulEquiv Nat.prime_five e.symm ?_
  exact I294Large.CommOrRank.of_projOmega (CFSG.LieType.Universal.Spin.coe_quadPlus n F) hQnd hT
    Nat.prime_five (by norm_num)
    (I294Large.CommOrRank.of_sylow_sigmaModel Nat.prime_five (one_le_weirA hpq) hN)

private theorem commOrRank_pOmegaMinus {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .POmegaMinus n ℓ f) (hℓ5 : ℓ ≠ 5) :
    I294Large.CommOrRank 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hp, hf, hn⟩, F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := id hm
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ 5 ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]; exact not_five_dvd_pow hp hℓ5
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := F) (n := n) hn hbc
  have hdim : finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) = 2 * n :=
    finrank_quadMinus_space (by omega)
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even (p := 5) (by norm_num) hpq (by omega)
    hdim hQnd (ε := -1) (Or.inr ⟨rfl, isMinusType_quadMinus (by omega) hbc⟩)
  refine I294Large.CommOrRank.of_mulEquiv Nat.prime_five e.symm ?_
  exact I294Large.CommOrRank.of_projOmega (CFSG.LieType.Universal.Spin.coe_quadMinus n F b c) hQnd
    hT Nat.prime_five (by norm_num)
    (I294Large.CommOrRank.of_sylow_sigmaModel Nat.prime_five (one_le_weirA hpq) hN)

private theorem commOrRank_of_classical {K : Type} [Group K] [Finite K] {t : StatedLieTag}
    {n ℓ f : ℕ} (hm : StatedClassicalModel K t n ℓ f) (hℓ5 : ℓ ≠ 5) (hdiag : ¬ FiveDiagType K)
    (S : Sylow 5 K) (hS : Nat.card S = 5 ^ 5) : I294Large.CommOrRank 5 K := by
  cases t with
  | PSL => exact commOrRank_psl hm hℓ5 hdiag S hS
  | PSU => exact commOrRank_psu hm hℓ5 hdiag S hS
  | PSp => exact commOrRank_psp hm hℓ5
  | POmegaOdd => exact commOrRank_pOmegaOdd hm hℓ5
  | POmegaPlus => exact commOrRank_pOmegaPlus hm hℓ5
  | POmegaMinus => exact commOrRank_pOmegaMinus hm hℓ5
  | _ => exact (hm.2 : False).elim

theorem classicalCase_holds : ClassicalCase := by
  intro K _ _ t n ℓ f hm hℓ hdiag S hS
  rcases commOrRank_of_classical hm hℓ hdiag S hS with h | h
  · exact h S
  · exact isMulCommutative_sylow_of_five_le_pRank h S hS

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
