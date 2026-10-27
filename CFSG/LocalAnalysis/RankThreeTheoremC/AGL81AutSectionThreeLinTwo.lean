module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeDefs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.RankThree.PartOne.K159.AutL2
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

open Matrix MatrixGroups
open CFSG.RankThree.PartOne.K159

variable {K : Type*}

private theorem isPGroup_range_uHom_three [Field K] [CharP K 3] :
    IsPGroup 3 (uHom (K := K)).range := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hy
  refine ⟨1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, show 3 ^ 1 = 3 by norm_num]
  change (y : PSL(2, K)) ^ 3 = 1
  rw [show (y : PSL(2, K)) = uHom z from hz.symm]
  exact uHom_pow (p := 3) z

private theorem mem_normalizer_range_uHom [Field K] [Finite K] (a : Kˣ) :
    (QuotientGroup.mk (dHom a) : PSL(2, K)) ∈
      Subgroup.normalizer ((uHom (K := K)).range : Set (PSL(2, K))) := by
  refine Subgroup.mem_normalizer_fintype ?_
  rintro _ ⟨y, rfl⟩
  refine ⟨Multiplicative.ofAdd ((a : K) ^ 2 * Multiplicative.toAdd y), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact (dPSL_mul_uHom a (Multiplicative.toAdd y)).symm

theorem not_threeAutFour_psl_two {K : Type*} [Field K] [Finite K] [CharP K 3]
    (hK : 27 ≤ Nat.card K) : ¬ ThreeAutFour (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  intro h
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf a = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units]
  set g : PSL(2, K) := QuotientGroup.mk (dHom a) with hg
  set E : Subgroup (PSL(2, K)) := (uHom (K := K)).range with hEdef
  have hE : IsPGroup 3 E := by
    rw [hEdef]
    exact isPGroup_range_uHom_three
  have hgN : g ∈ Subgroup.normalizer (E : Set (PSL(2, K))) := by
    rw [hEdef, hg]
    exact mem_normalizer_range_uHom a
  obtain ⟨k, hk⟩ := h E hE g hgN
  have hcentral := hk (uHom (Multiplicative.ofAdd 1)) ⟨Multiplicative.ofAdd 1, rfl⟩
  have hgm : g ^ (4 * 3 ^ k) = QuotientGroup.mk (dHom (a ^ (4 * 3 ^ k))) := by
    rw [hg, map_pow, QuotientGroup.mk_pow]
  have hstep : uHom (Multiplicative.ofAdd (((a ^ (4 * 3 ^ k) : Kˣ) : K) ^ 2 * 1)) =
      uHom (Multiplicative.ofAdd 1) := by
    have h' := hcentral
    rw [hgm, dPSL_mul_uHom (a ^ (4 * 3 ^ k)) 1] at h'
    exact mul_right_cancel h'
  have h4 : (((a ^ (4 * 3 ^ k) : Kˣ) : K)) ^ 2 * 1 = 1 := by
    simpa using congrArg Multiplicative.toAdd (uHom_injective hstep)
  have h5 : a ^ (2 * (4 * 3 ^ k)) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul']
    simpa [Units.val_pow_eq_pow_val] using h4
  have hdvd : orderOf a ∣ 2 * (4 * 3 ^ k) := orderOf_dvd_of_pow_eq_one h5
  have hdvd' : Nat.card K - 1 ∣ 8 * 3 ^ k := by
    rw [← hord]
    simpa [show 2 * (4 * 3 ^ k) = 8 * 3 ^ k by ring] using hdvd
  have h3not : ¬ 3 ∣ Nat.card K - 1 := by
    let _ : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    have hcard : Nat.card K = 3 ^ (n : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hn
    intro hd
    have h3dvd : 3 ∣ Nat.card K := by
      rw [hcard]
      exact dvd_pow_self 3 n.pos.ne'
    have h1 : 3 ∣ 1 := by
      have h' := Nat.dvd_sub h3dvd hd
      rwa [Nat.sub_sub_self (by omega : 1 ≤ Nat.card K)] at h'
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hcop : Nat.Coprime (Nat.card K - 1) (3 ^ k) :=
    Nat.Coprime.pow_right k
      (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3not).symm)
  have h8 : Nat.card K - 1 ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd'
  have hle : Nat.card K - 1 ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  omega

theorem not_sevenCentralizesTwo_psl_two {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 8) :
    ¬ SevenCentralizesTwo (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  intro h
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcardu : Nat.card Kˣ = 7 := by
    rw [Nat.card_units, hK]
  have hord : orderOf a = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, hcardu]
  have ha7 : a ^ 7 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one a
  set g : PSL(2, K) := QuotientGroup.mk (dHom a) with hg
  set E : Subgroup (PSL(2, K)) := (uHom (K := K)).range with hEdef
  have hE : IsPGroup 2 E := by
    rw [hEdef]
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 1 = 2 by norm_num]
    change (y : PSL(2, K)) ^ 2 = 1
    rw [show (y : PSL(2, K)) = uHom z from hz.symm]
    exact uHom_pow (p := 2) z
  have hgN : g ∈ Subgroup.normalizer (E : Set (PSL(2, K))) := by
    rw [hEdef, hg]
    exact mem_normalizer_range_uHom a
  have hg7 : g ^ 7 = 1 := by
    rw [hg]
    have h' : (QuotientGroup.mk (dHom a) : PSL(2, K)) ^ 7 =
        QuotientGroup.mk (dHom (a ^ 7)) := by
      rw [map_pow, QuotientGroup.mk_pow]
    rw [h', ha7]
    simp
  have hnc : g * uHom (Multiplicative.ofAdd 1) ≠
      uHom (Multiplicative.ofAdd 1) * g := by
    intro hc
    have h' := dPSL_mul_uHom a 1
    rw [hg] at hc
    rw [hc] at h'
    have h2 := mul_right_cancel h'
    have h3 := uHom_injective h2
    have h4 : (a : K) ^ 2 * 1 = 1 := by
      simpa using (congrArg Multiplicative.toAdd h3).symm
    have h5 : a ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa using h4
    have hd := orderOf_dvd_of_pow_eq_one h5
    rw [hord] at hd
    have hle : 7 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  exact hnc (h E hE g hgN hg7 (uHom (Multiplicative.ofAdd 1))
    ⟨Multiplicative.ofAdd 1, rfl⟩)

theorem not_threeAutFour_lie_A_one {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower}
    (hd : d.1 = .A 1 Q) (hQ : Q.p = 3) : ¬ ThreeAutFour (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .A 1 Q := hd
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have h4 : 4 ≤ Q.card := by
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using hv'.1
  have hcardQ : Q.card = 3 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hexp2 : 2 ≤ Q.exponent := by
    by_contra h
    have h1 : Q.exponent ≤ 1 := by omega
    have hle : Q.card ≤ 3 := by
      rw [hcardQ]
      calc 3 ^ Q.exponent ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        _ = 3 := by norm_num
    omega
  have hexp3 : 3 ≤ Q.exponent := by
    rcases (show Q.exponent = 2 ∨ 3 ≤ Q.exponent by omega) with h | h
    · exfalso
      have hI : CFSG.AGLEmbedding.IsLinTwoIndex 3 Q.exponent
          ⟨TauCeti.LieTypeIndex.A 1 Q, hv⟩ := ⟨Q, rfl, hQ, rfl⟩
      exact CFSG.AGLEmbedding.card_ne_nine_of_isLinTwoIndex hI (by rw [h]; norm_num)
    · exact h
  have hexp0 : Q.exponent ≠ 0 := by omega
  have hcard : 27 ≤ Nat.card (GaloisField 3 Q.exponent) := by
    rw [GaloisField.card 3 Q.exponent hexp0]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num : 0 < 3) hexp3
  obtain ⟨e⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := 3) (n := Q.exponent) (d := ⟨TauCeti.LieTypeIndex.A 1 Q, hv⟩) ⟨Q, rfl, hQ, rfl⟩
  intro h
  exact not_threeAutFour_psl_two (K := GaloisField 3 Q.exponent) hcard
    (ThreeAutFour.of_injective e.symm.toMonoidHom e.symm.injective h)

theorem not_sevenCentralizesTwo_lie_A_one {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hd : d.1 = .A 1 Q) (hQ : Q.p = 2) (hn : Q.exponent = 3) :
    ¬ SevenCentralizesTwo (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .A 1 Q := hd
  have hI : CFSG.AGLEmbedding.IsLinTwoIndex 2 3
      ⟨TauCeti.LieTypeIndex.A 1 Q, hv⟩ := ⟨Q, rfl, hQ, hn⟩
  obtain ⟨e⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hI
  have hcard : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  intro h
  exact not_sevenCentralizesTwo_psl_two (K := GaloisField 2 3) hcard
    (SevenCentralizesTwo.of_injective e.symm.toMonoidHom e.symm.injective h)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
