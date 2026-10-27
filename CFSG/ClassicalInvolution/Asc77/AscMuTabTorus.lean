module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Std

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace MuTab

theorem natCard_units_eq' (F : Type) [Field F] [Finite F] : Nat.card Fˣ = Nat.card F - 1 := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]

section Linear

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem _root_.CFSG.ClassicalInvolution.Asc77.LinearBlockStandardPair.muTab_pow_card_sub_one
    (h4 : 4 ≤ Nat.card F) {W U V : Subgroup X} (h : WeakCT.LinearBlockStandardPair F W U V)
    {x : X} (hxV : x ∈ V) (hxN : x ∈ Subgroup.normalizer (U : Set X)) :
    x ^ (Nat.card F - 1) = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  rw [← hV] at hxV
  obtain ⟨g, hg, rfl⟩ := hxV
  rw [← hU] at hxN
  have hgN' := ih8_mem_normalizer_of_map hker (B12_perfect h4) hxN
  obtain ⟨M, rfl⟩ := hg
  have hb : WeakCT.blockSL F 3 2 0 (by omega) (WeakCT.rotSL) ∈ WeakCT.B12 F := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
  have h2 : WeakCT.blockSL F 3 2 0 (by omega) A' * WeakCT.blockSL F 3 2 1 (by omega) M =
      WeakCT.blockSL F 3 2 1 (by omega) M * WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL := by
    rw [hA']
    group
  have h3 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero, coe_blockSL_one] at h3
  obtain ⟨h01, h10⟩ := embPair_zero_conj_rot _ _ h3.symm
  obtain ⟨u, rfl⟩ := WeakCT.mem_diagTorus2_iff.mp (WeakCT.mem_diagTorus2_of_offDiag M h01 h10)
  have hu : u ^ (Nat.card F - 1) = 1 := by
    rw [← natCard_units_eq' F]
    exact pow_card_eq_one'
  rw [← map_pow, ← map_pow, ← map_pow, hu, map_one, map_one, map_one]

end Linear

section Unitary

open CFSG.ClassicalInvolution.Models (suMat)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem _root_.CFSG.ClassicalInvolution.Asc77.UnitaryBlockStandardPair.muTab_pow_card_add_one
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair K p f W U V) {x : X} (hxV : x ∈ V)
    (hxN : x ∈ Subgroup.normalizer (U : Set X)) : x ^ (p ^ f + 1) = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  rw [← hV] at hxV
  obtain ⟨g, hg, rfl⟩ := hxV
  rw [← hU] at hxN
  have hgN' := ih8_mem_normalizer_of_map hker (unitaryB12_perfect hK hq) hxN
  obtain ⟨M, rfl⟩ := hg
  have hb : embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) ∈
      Phan.B12 K p f := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
  have h2 : embSUid (unitaryInvolution K p f) 2 A' * embSUid (unitaryInvolution K p f) 0 M =
      embSUid (unitaryInvolution K p f) 0 M *
        embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) := by
    rw [hA']
    group
  have h3 := congrArg suMat h2
  simp only [Models.suMat_mul] at h3
  obtain ⟨h01, h10⟩ := embPair_zero_conj_rot _ _ h3.symm
  have hM : M ∈ Phan.torus (unitaryInvolution K p f) 2 := by
    rw [Phan.mem_torus_iff]
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact h01
    · exact h10
    · exact absurd rfl hab
  obtain ⟨dd, rfl⟩ := hM
  have hdd : dd ^ (p ^ f + 1) = 1 := by
    refine Subtype.ext (funext fun a => ?_)
    show (dd.1 a) ^ (p ^ f + 1) = 1
    rw [← Phan.card_normOne (K := K) (p := p) (f := f) hK]
    exact pow_card_eq_one'
  rw [← map_pow, ← map_pow, ← map_pow, hdd, map_one, map_one, map_one]

end Unitary

section Arith

variable {F : Type} [Field F] [Finite F]

theorem eight_dvd_two_pow_sl2 (hodd : Odd (Nat.card F)) :
    8 ∣ 2 ^ (Nat.card SL(2, F)).factorization 2 := by
  have hcard := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
  have h1 : Nat.card F ^ 2 - 1 = 8 * r := by
    rw [hm]
    have h2 : (2 * m + 1) ^ 2 = 8 * r + 1 := by nlinarith [hr]
    omega
  have hN0 : Nat.card SL(2, F) ≠ 0 := Nat.card_pos.ne'
  have h8 : 2 ^ 3 ∣ Nat.card SL(2, F) := by
    rw [hcard, h1]
    exact Dvd.dvd.mul_left ⟨r, by norm_num⟩ _
  have h3 : 3 ≤ (Nat.card SL(2, F)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).mp h8
  exact Nat.pow_dvd_pow 2 h3

theorem false_of_linear (hodd : Odd (Nat.card F)) (h3 : Nat.card F % 4 = 3) {a : ℕ}
    (hcard : 2 * 2 ^ a = 2 ^ (Nat.card SL(2, F)).factorization 2)
    (hdvd : 2 ^ a ∣ Nat.card F - 1) : False := by
  have h8 := eight_dvd_two_pow_sl2 hodd
  rw [← hcard] at h8
  have h4 : 4 ∣ 2 ^ a := by omega
  have := dvd_trans h4 hdvd
  omega

theorem false_of_unitary (hodd : Odd (Nat.card F)) (h1 : Nat.card F % 4 = 1) {a : ℕ}
    (hcard : 2 * 2 ^ a = 2 ^ (Nat.card SL(2, F)).factorization 2)
    (hdvd : 2 ^ a ∣ Nat.card F + 1) : False := by
  have h8 := eight_dvd_two_pow_sl2 hodd
  rw [← hcard] at h8
  have h4 : 4 ∣ 2 ^ a := by omega
  have := dvd_trans h4 hdvd
  omega

end Arith

end MuTab

end CFSG.ClassicalInvolution.Asc77
