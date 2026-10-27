module

public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open Matrix Polynomial

section Nilpotent

theorem pow_three_eq_zero_of_isNilpotent {F : Type*} [Field F] {N : Matrix (Fin 3) (Fin 3) F}
    (h : IsNilpotent N) : N ^ 3 = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h2 : N.charpoly - X ^ Fintype.card (Fin 3) = 0 := h1.eq_zero
  have h3 := Matrix.aeval_self_charpoly N
  rw [sub_eq_zero] at h2
  rw [h2] at h3
  simpa using h3

theorem pow_four_eq_one_of_two_power {F : Type*} [Field F] [CharP F 2]
    (g : SpecialLinearGroup (Fin 3) F) {k : ℕ} (hg : g ^ 2 ^ k = 1) : g ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) F) - 1 with hN
  have hgN : (g : Matrix (Fin 3) (Fin 3) F) = N + 1 := by rw [hN]; abel
  have h1 : (g : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ k = 1 := by
    have := congrArg (fun u : SpecialLinearGroup (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hg
    simpa [SpecialLinearGroup.coe_pow] using this
  have hc : Commute N 1 := Commute.one_right N
  have h2 : N ^ 2 ^ k = 0 := by
    have h3 := add_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) F) 2 k hc
    rw [← hgN, h1, one_pow] at h3
    have h4 : N ^ 2 ^ k + 1 = 0 + 1 := by rw [← h3, zero_add]
    exact add_right_cancel h4
  have h5 : N ^ 3 = 0 := pow_three_eq_zero_of_isNilpotent ⟨2 ^ k, h2⟩
  have h6 : N ^ 4 = 0 := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h5, zero_mul]
  have h7 := add_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) F) 2 2 hc
  rw [show (2 : ℕ) ^ 2 = 4 from rfl] at h7
  have hpow : ((g ^ 4 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) ^ 4 := Matrix.SpecialLinearGroup.coe_pow g 4
  have hmat : ((g ^ 4 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hpow, hgN, h7, h6, one_pow, zero_add]
  exact Subtype.ext (hmat.trans (Matrix.SpecialLinearGroup.coe_one (n := Fin 3) (R := F)).symm)

end Nilpotent

section Projective

variable {F : Type} [Field F]

theorem projectiveSL_pow_four_of_two_power [CharP F 2] (x : projectiveSL 3 F) {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hz : g ^ 2 ^ k ∈ scalars 3 F := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx
  obtain ⟨c, hc3, hcg⟩ := mem_scalars.mp hz
  have h3 : (g ^ 3) ^ 2 ^ k = 1 := by
    have hpow : (((g ^ 2 ^ k) ^ 3 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g ^ 2 ^ k : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 :=
      Matrix.SpecialLinearGroup.coe_pow (g ^ 2 ^ k) 3
    have hmat :
        (((g ^ 3) ^ 2 ^ k : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hpow, hcg, ← map_pow,
        ← Units.val_pow_eq_pow_val, hc3, Units.val_one, map_one]
    exact Subtype.ext (hmat.trans (Matrix.SpecialLinearGroup.coe_one (n := Fin 3) (R := F)).symm)
  have h4 : (g ^ 3) ^ 4 = 1 := pow_four_eq_one_of_two_power (g ^ 3) h3
  have hord : orderOf (QuotientGroup.mk g : projectiveSL 3 F) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hx
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hcop : (orderOf (QuotientGroup.mk g : projectiveSL 3 F)).Coprime 3 := by
    rw [hio]
    exact (Nat.Coprime.pow_left i (by norm_num : Nat.Coprime 2 3))
  have hord3 : orderOf ((QuotientGroup.mk g : projectiveSL 3 F) ^ 3) =
      orderOf (QuotientGroup.mk g : projectiveSL 3 F) := Nat.Coprime.orderOf_pow hcop
  have h5 : ((QuotientGroup.mk g : projectiveSL 3 F) ^ 3) ^ 4 = 1 := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, h4]
    rfl
  have h6 : orderOf (QuotientGroup.mk g : projectiveSL 3 F) ∣ 4 := by
    rw [← hord3]
    exact orderOf_dvd_of_pow_eq_one h5
  exact orderOf_dvd_iff_pow_eq_one.mp h6

end Projective

section Alternating

theorem exists_orderOf_eight_alt {m : ℕ} (hm : 10 ≤ m) :
    ∃ y : alternatingGroup (Fin m), orderOf y = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : Equiv.Perm (Fin 10) :=
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5 *
      Equiv.swap 5 6 * Equiv.swap 6 7 * Equiv.swap 8 9
  have hσ4 : ¬ σ ^ 2 ^ 2 = 1 := by decide +kernel
  have hσ8 : σ ^ 2 ^ (2 + 1) = 1 := by decide +kernel
  have hσs : Equiv.Perm.sign σ = 1 := by decide +kernel
  let p : Fin m → Prop := fun i => i.val < 10
  let f : Fin 10 ≃ {i : Fin m // p i} :=
    { toFun := fun i => ⟨⟨i.val, by omega⟩, i.2⟩
      invFun := fun i => ⟨i.1.val, i.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  let σ' : Equiv.Perm (Fin m) := Equiv.Perm.extendDomainHom f σ
  have hinj : Function.Injective (Equiv.Perm.extendDomainHom f) :=
    Equiv.Perm.extendDomainHom_injective f
  have h4 : ¬ σ' ^ 2 ^ 2 = 1 := fun h => hσ4 (hinj (by rw [map_pow, map_one]; exact h))
  have h8 : σ' ^ 2 ^ (2 + 1) = 1 := by
    rw [← map_pow, hσ8, map_one]
  have hs : Equiv.Perm.sign σ' = 1 := by
    rw [show σ' = σ.extendDomain f from rfl, Equiv.Perm.sign_extendDomain, hσs]
  have hmem : σ' ∈ alternatingGroup (Fin m) := Equiv.Perm.mem_alternatingGroup.mpr hs
  refine ⟨⟨σ', hmem⟩, ?_⟩
  have hord := orderOf_eq_prime_pow (p := 2) (n := 2) (x := σ') h4 h8
  rw [Subgroup.orderOf_mk, hord]
  norm_num

end Alternating

section Order

@[expose] noncomputable def projectiveSLEquivStatedProj (n : ℕ) (K : Type) [Field K] [Finite K] :
    projectiveSL n K ≃* StatedProj (StatedSL n K) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K)).trans
    (projectiveSpecialLinearGroupEquivStatedProj n K)

variable {F : Type} [Field F] [Finite F]

theorem lt_card_projectiveSL_three {f : ℕ} (hf : 3 ≤ f) (hF : Nat.card F = 2 ^ f) :
    181440 < Nat.card (projectiveSL 3 F) := by
  rw [Nat.card_congr (projectiveSLEquivStatedProj 3 F).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
    hF]
  have hq : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hg : Nat.gcd 3 (2 ^ f - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hgpos : 0 < Nat.gcd 3 (2 ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hprod : ∏ j ∈ Finset.Icc 2 3, ((2 ^ f) ^ j - 1) = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
    have : Finset.Icc 2 3 = {2, 3} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
  rw [hprod, show 3 * (3 - 1) / 2 = 3 by norm_num]
  have key : 181441 ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) /
      Nat.gcd 3 (2 ^ f - 1) := by
    refine (Nat.le_div_iff_mul_le hgpos).mpr ?_
    have h1 : 512 ≤ (2 ^ f) ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 63 ≤ (2 ^ f) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ f) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 511 ≤ (2 ^ f) ^ 3 - 1 := by omega
    calc 181441 * Nat.gcd 3 (2 ^ f - 1) ≤ 181441 * 3 := Nat.mul_le_mul_left _ hg
      _ ≤ 512 * (63 * 511) := by norm_num
      _ ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  omega

theorem projectiveSL_three_not_alternating [CharP F 2] {f : ℕ} (hf : 3 ≤ f)
    (hF : Nat.card F = 2 ^ f) (m : ℕ) (hm : 5 ≤ m) :
    IsEmpty (projectiveSL 3 F ≃* alternatingGroup (Fin m)) := by
  refine ⟨fun e => ?_⟩
  by_cases h10 : 10 ≤ m
  · obtain ⟨y, hy⟩ := exists_orderOf_eight_alt h10
    have h1 : e.symm y ^ 2 ^ 3 = 1 := by
      rw [← map_pow, show (2 : ℕ) ^ 3 = orderOf y by rw [hy]; norm_num, pow_orderOf_eq_one, map_one]
    have h2 := projectiveSL_pow_four_of_two_power (e.symm y) h1
    have h3 : orderOf (e.symm y) = 8 := by rw [MulEquiv.orderOf_eq]; exact hy
    have h4 : orderOf (e.symm y) ∣ 4 := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at h4
    omega
  · have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hcard : Nat.card (projectiveSL 3 F) = Nat.card (alternatingGroup (Fin m)) :=
      Nat.card_congr e.toEquiv
    have hbound : Nat.card (alternatingGroup (Fin m)) ≤ 181440 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      have hm9 : m ≤ 9 := by omega
      interval_cases m <;> decide
    have := lt_card_projectiveSL_three hf hF
    omega

end Order

end CFSG.QuasithinUnique.Id2519
