module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs
public import CFSG.RankThree.SubgroupLists.CentralizerPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

theorem arith_l2_primePow : ∀ p < 432, ∀ k < 10, (Nat.Prime p ∧ p ≠ 2 ∧ 5 ≤ p ^ k ∧
    p ^ k * ((p ^ k) ^ 2 - 1) ∣ 2 * Nat.factorial 11) →
    p ^ k ∈ ({5, 7, 9, 11} : Finset ℕ) := by
  decide +kernel

theorem card_of_kfa_psl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F)
    (h : KindFactorAll Kind.ly (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9 ∨ Nat.card F = 11 := by
  classical
  have hfin : Fintype F := Fintype.ofFinite F
  have hchar2 : ringChar F ≠ 2 := by
    intro h2
    have h0 : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.1 h2
    rw [← Nat.card_eq_fintype_card] at h0
    have h1 := Nat.odd_iff.1 hodd
    omega
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hchar2
  have hdvd := KindFactorAll.card_dvd h (Or.inr rfl)
  have hsl := natCard_sl2_eq (F := F) h2F
  rw [card_sl2_field] at hsl
  have hq : Nat.card F * (Nat.card F ^ 2 - 1) ∣ 2 * Nat.factorial 11 := by
    rw [hsl, mul_comm]
    exact mul_dvd_mul_left 2 hdvd
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hn] at hq h5 ⊢
  have hp2 : ringChar F ≠ 2 := hchar2
  set x : ℕ := ringChar F ^ (n : ℕ) with hx
  have hn0 : (n : ℕ) ≠ 0 := by
    intro h0
    rw [hx, h0, pow_zero] at h5
    omega
  have hxle : x * (x ^ 2 - 1) ≤ 2 * Nat.factorial 11 :=
    Nat.le_of_dvd (by positivity) hq
  have hx432 : x < 432 := by
    by_contra hge
    have hge := not_lt.1 hge
    have h1 : 432 * (432 ^ 2 - 1) ≤ x * (x ^ 2 - 1) := by
      apply Nat.mul_le_mul hge
      apply Nat.sub_le_sub_right
      exact Nat.pow_le_pow_left hge 2
    have h2 : 2 * Nat.factorial 11 < 432 * (432 ^ 2 - 1) := by decide
    omega
  have hpx : ringChar F ≤ x := Nat.le_self_pow hn0 _
  have hp3 : 3 ≤ ringChar F := by
    have := hp.two_le
    omega
  have hn10 : (n : ℕ) < 10 := by
    by_contra hge
    have hge := not_lt.1 hge
    have h1 : 3 ^ 10 ≤ x := by
      calc 3 ^ 10 ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hge
        _ ≤ ringChar F ^ (n : ℕ) := Nat.pow_le_pow_left hp3 _
    have : 3 ^ 10 = 59049 := by norm_num
    omega
  have := arith_l2_primePow (ringChar F) (by omega) n hn10 ⟨hp, hp2, h5, hq⟩
  simpa using this

theorem exists_involution_of_not_solvable {K : Type*} [Group K] [Finite K]
    (hK : ¬ Group.IsSolvable K) : ∃ u : K, orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_prime_orderOf_dvd_card' 2 ?_
  by_contra h
  exact hK (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)))

theorem isSection_of_injective {Y B D : Type*} [Group Y] [Group B] [Group D] (f : B →* D)
    (hf : Function.Injective f) (h : IsSection Y B) : IsSection Y D :=
  IsSection.of_le f.range (IsSection.of_equiv (MonoidHom.ofInjective hf).symm h)

theorem kfa_of_isSection {Y Y' : Type} [Group Y] [Group Y'] (hY : KindFactorAll Kind.ly Y)
    (h : IsSection Y' Y) : KindFactorAll Kind.ly Y' := by
  obtain ⟨n, hn1, hn2, ⟨U, φ, hφ⟩⟩ := hY
  exact ⟨n, hn1, hn2, IsSection.of_le U (IsSection.of_surjective φ hφ h)⟩

theorem notKFA_of_card {Y : Type} [Group Y] {p k : ℕ} (hdvd : p ^ k ∣ Nat.card Y)
    (hnd : ¬ p ^ k ∣ Nat.factorial 11) : ¬ KindFactorAll Kind.ly Y :=
  fun h => hnd (hdvd.trans (KindFactorAll.card_dvd h (Or.inr rfl)))

theorem psl2_simple {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4

theorem psl2_not_isSolvable {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  exact Group.IsPerfect.not_isSolvable _

theorem not_kfa_psl2_cube {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hF : Nat.card F = (p ^ f) ^ 3) :
    ¬ KindFactorAll Kind.ly (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  intro h
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact ((hp.odd_of_ne_two hp2).pow).pow
  have h3 : 3 ≤ p ^ f := by
    have := hp.two_le
    calc 3 ≤ p := by omega
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have h27 : 27 ≤ Nat.card F := by
    rw [hF]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left h3 3
  have := card_of_kfa_psl2 hodd (by omega) h
  omega

theorem isSection_cent_of_sub {G : Type} [Group G] (A : Subgroup G) (u : ↥A) {Q : Type}
    [Group Q] (h : IsSection Q ↥(centralizer ({u} : Set ↥A))) :
    IsSection Q ↥(centralizer ({(u : G)} : Set G)) := by
  let g : ↥(centralizer ({u} : Set ↥A)) →* G := A.subtype.comp (centralizer ({u} : Set ↥A)).subtype
  have hg : ∀ x : ↥(centralizer ({u} : Set ↥A)), g x ∈ centralizer ({(u : G)} : Set G) := by
    intro x
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hx
  have hginj : Function.Injective g := A.subtype_injective.comp (Subgroup.subtype_injective _)
  refine isSection_of_injective (g.codRestrict _ hg) ?_ h
  intro x y hxy
  have hxy' := congrArg Subtype.val hxy
  exact hginj hxy'

theorem kfa_of_cent_section {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (hfr : AFrame A zb Sb Vb) (B : Subgroup A) (u : ↥B) (hu : orderOf u = 2) {Q : Type}
    [Group Q] [IsSimpleGroup Q] (hns : ¬ Group.IsSolvable Q)
    (h : IsSection Q ↥(centralizer ({u} : Set ↥B))) : KindFactorAll Kind.ly Q := by
  have hu' : orderOf (u : A) = 2 := (Subgroup.orderOf_coe u).trans hu
  exact hfr.invsec (u : A) hu' Q hns (isSection_cent_of_sub B u h)

theorem not_isSolvable_quot_of_quasisimple {J : Type} [Group J] (hq : CFSG.IsQuasisimple J) :
    ¬ Group.IsSolvable (J ⧸ center J) := by
  intro hs
  have hcomm := (@IsSimpleGroup.comm_iff_isSolvable _ _ hq.2.1).2 hs
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact hab (hcomm a b)

theorem not_isSolvable_of_quot {J : Type} [Group J] (N : Subgroup J) [N.Normal]
    (h : ¬ Group.IsSolvable (J ⧸ N)) : ¬ Group.IsSolvable J := by
  intro hJ
  exact h inferInstance

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
