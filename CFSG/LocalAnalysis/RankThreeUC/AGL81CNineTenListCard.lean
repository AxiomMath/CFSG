module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

private theorem not_sq_dvd_mul_sq_sub_one {p : ℕ} (hp : p.Prime) :
    ¬ p ^ 2 ∣ p * (p ^ 2 - 1) := by
  intro hdvd
  have hp_pos : 0 < p := hp.pos
  rw [pow_two] at hdvd
  have h1 : p ∣ p * p - 1 := Nat.dvd_of_mul_dvd_mul_left hp_pos hdvd
  have h2 : p ∣ p * p := ⟨p, by ring⟩
  have h3 : p ∣ p * p - (p * p - 1) := Nat.dvd_sub h2 h1
  have h4 : p * p - (p * p - 1) = 1 := by
    have hpp : 0 < p * p := Nat.mul_pos hp_pos hp_pos
    omega
  rw [h4] at h3
  exact hp.not_dvd_one h3

theorem not_sq_dvd_card_of_isSLType_two {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y]
    (h : IsSLType 2 (ZMod p) Y) : ¬ p ^ 2 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card Y = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.PSL2Table.card_SL, ZMod.card]
  rw [hcard]
  exact not_sq_dvd_mul_sq_sub_one (Fact.out : p.Prime)

theorem not_sq_dvd_card_of_isPSLType_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type}
    [Group Y] (h : IsPSLType 2 (ZMod p) Y) : ¬ p ^ 2 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  have hcard : Nat.card Y * 2 = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.PSL2Table.card_PSL h2, ZMod.card]
  intro hdvd
  apply not_sq_dvd_mul_sq_sub_one hp
  rw [← hcard]
  exact dvd_mul_of_dvd_left hdvd 2

theorem not_sq_dvd_card_of_isSLType_two_five {Y : Type} [Group Y] (h : IsSLType 2 (ZMod 5) Y) :
    ¬ 3 ^ 2 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card Y = 120 := by
    rw [Nat.card_congr e.toEquiv, CFSG.PSL2Table.card_SL (F := ZMod 5), ZMod.card]
    norm_num
  rw [hcard]
  norm_num

theorem natCard_alternatingGroup_fin (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem not_dvd_card_of_isQ8D8Type {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B : Type} [Group B]
    [Finite B] (h : IsQ8D8Type B) : ¬ p ∣ Nat.card B := by
  obtain ⟨Q, E, ⟨eQ⟩, ⟨eE⟩, hcomm, hsup, -⟩ := h
  have hQcard : Nat.card Q = 2 ^ 3 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hEcard : Nat.card E = 2 ^ 3 := by
    rw [Nat.card_congr eE.toEquiv, DihedralGroup.nat_card]
    norm_num
  have hQp : IsPGroup 2 Q := IsPGroup.of_card hQcard
  have hEp : IsPGroup 2 E := IsPGroup.of_card hEcard
  have hQnorm : Q ≤ Subgroup.normalizer E := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq e he
    rw [hcomm q hq e he, mul_assoc, mul_inv_cancel, mul_one]
    exact he
  have htop : IsPGroup 2 (⊤ : Subgroup B) :=
    hsup ▸ IsPGroup.to_sup_of_normal_right' hQp hEp hQnorm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp htop
  rw [Subgroup.card_top] at hn
  intro hpdvd
  rw [hn] at hpdvd
  have hp : p.Prime := Fact.out
  have hp_eq : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpdvd)
  exact hp2 hp_eq

theorem not_sq_dvd_card_of_isExtNotation {p : ℕ} [Fact p.Prime]
    {PA PB : ∀ (V : Type) [Group V], Prop} {X : Type} [Group X] [Finite X]
    (hA : ∀ (V : Type) [Group V] [Finite V], PA V → ¬ p ^ 2 ∣ Nat.card V)
    (hB : ∀ (V : Type) [Group V] [Finite V], PB V → ¬ p ∣ Nat.card V)
    (h : IsExtNotation PA PB X) : ¬ p ^ 2 ∣ Nat.card X := by
  obtain ⟨N, hN, hBN, hAN, -⟩ := h
  haveI := hN
  intro hdvd
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N] at hdvd
  have hp : p.Prime := Fact.out
  have hcop_p : Nat.Coprime p (Nat.card N) := hp.coprime_iff_not_dvd.mpr (hB ↥N hBN)
  have hcop : Nat.Coprime (p ^ 2) (Nat.card N) :=
    (Nat.coprime_pow_left_iff (by norm_num) p (Nat.card N)).mpr hcop_p
  exact hA (X ⧸ N) hAN (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd)

theorem not_mem_center_SL3_of_orderOf {p : ℕ} [Fact p.Prime]
    {y : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)} (hy : orderOf y = p) :
    y ∉ center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) := by
  intro hyc
  obtain ⟨r, hr3, hry⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp hyc
  have hr3' : r ^ 3 = 1 := by simpa using hr3
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hry,
      ← map_pow, hr3']
    simp
  have hpdvd : p ∣ 3 := hy ▸ orderOf_dvd_of_pow_eq_one hy3
  have hp : p.Prime := Fact.out
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpdvd
  have hr_eq_one : r = 1 := by
    have h03 : r ^ 3 = r ^ p := congrArg (fun k : ℕ => r ^ k) hp3.symm
    have h3r : r ^ 3 = r := h03.trans (ZMod.pow_card r)
    rw [← h3r, hr3']
  have hyval : (↑y : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
    rw [← hry, hr_eq_one, map_one]
  have hy1 : y = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact hyval)
  have h1 : orderOf y = 1 := by rw [hy1, orderOf_one]
  rw [hy] at h1
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
