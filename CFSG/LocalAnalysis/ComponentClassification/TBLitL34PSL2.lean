module

public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup
open scoped MatrixGroups

theorem sl2Ord_mono {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem not_dvd_two_of_three_le {m : ℕ} (hm : 3 ≤ m) : ¬ m * (m ^ 2 - 1) ∣ 2 := by
  intro h
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 := sl2Ord_mono hm
  norm_num at h2
  omega

theorem eq_seven_of_dvd {m : ℕ} (hodd : Odd m) (hm : 3 ≤ m) (h3 : m ≠ 3)
    (h : m * (m ^ 2 - 1) ∣ 336) : m = 7 := by
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h8 : m ≤ 7 := by
    by_contra hlt
    have := sl2Ord_mono (show 8 ≤ m by omega)
    norm_num at this
    omega
  interval_cases m
  · exact absurd rfl h3
  · exact absurd hodd (by decide)
  · norm_num at h
  · exact absurd hodd (by decide)
  · rfl

theorem false_of_dvd_of_dvd {m : ℕ} (hodd : Odd m) (h1 : 20160 ∣ m * (m ^ 2 - 1))
    (h2 : m * (m ^ 2 - 1) ∣ 40320) : False := by
  have hpos : 0 < m * (m ^ 2 - 1) := by
    rcases Nat.eq_zero_or_pos (m * (m ^ 2 - 1)) with h0 | h0
    · rw [h0] at h2
      norm_num at h2
    · exact h0
  have hle := Nat.le_of_dvd (by norm_num) h2
  have hge := Nat.le_of_dvd hpos h1
  have hm : m ≤ 34 := by
    by_contra hlt
    have := sl2Ord_mono (show 35 ≤ m by omega)
    norm_num at this
    omega
  have hm' : 28 ≤ m := by
    by_contra hlt
    have := sl2Ord_mono (show m ≤ 27 by omega)
    norm_num at this
    omega
  interval_cases m <;> first | exact absurd hodd (by decide) | norm_num at h1

theorem card_ne_three_of_isPerfect {F : Type*} [Field F] [Finite F]
    (h : Group.IsPerfect SL(2, F)) : Nat.card F ≠ 3 := by
  intro h3
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3
  have hp : Group.IsPerfect SL(2, ZMod 3) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  set N := CFSG.ClassicalInvolution.sl2ThreeQ with hN
  have := CFSG.ClassicalInvolution.sl2ThreeQ_normal
  have hc : Nat.card (SL(2, ZMod 3) ⧸ N) = 3 := by
    have := CFSG.ClassicalInvolution.sl2ThreeQ_index
    rw [Subgroup.index] at this
    exact this
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : IsCyclic (SL(2, ZMod 3) ⧸ N) := isCyclic_of_prime_card hc
  have : IsMulCommutative (SL(2, ZMod 3) ⧸ N) := ⟨⟨fun a b => by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := SL(2, ZMod 3) ⧸ N)
    obtain ⟨i, rfl⟩ := hg a
    obtain ⟨j, rfl⟩ := hg b
    rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm]⟩⟩
  have hle := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', hp.commutator_eq_top] at hle
  have htop : N = ⊤ := eq_top_iff.mpr hle
  have h3' := CFSG.ClassicalInvolution.sl2ThreeQ_index
  rw [← hN, htop, Subgroup.index_top] at h3'
  omega

theorem card_galoisField {p n : ℕ} [Fact p.Prime] (hn : 0 < n) :
    Nat.card (GaloisField p n) = p ^ n :=
  GaloisField.card p n hn.ne'

theorem odd_card_galoisField {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) :
    Odd (Nat.card (GaloisField p n)) := by
  rw [card_galoisField hn]
  exact (hp.out.odd_of_ne_two hp2).pow

theorem eq_seven_of_card {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    (h : Nat.card (GaloisField p n) = 7) : p = 7 ∧ n = 1 := by
  rw [card_galoisField hn] at h
  exact (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h

theorem card_sl2 (F : Type*) [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F

theorem isPerfect_sl2 {X : Type} [Group X] {S : Subgroup X} (hS : ⁅S, S⁆ = S) {F : Type*}
    [Field F] (e : ↥S ⧸ pPrimeCore 2 ↥S ≃* SL(2, F)) : Group.IsPerfect SL(2, F) := by
  have hp : Group.IsPerfect ↥S := (Subgroup.isPerfect_iff (H := S)).2 hS
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

end CFSG.ComponentClassification.TBLit.L34P
