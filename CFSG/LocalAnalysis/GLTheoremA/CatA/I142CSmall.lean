module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142CAlt
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142C

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem perfectInLayer_of_card_168 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hc : Nat.card S = 168) {β : MulAut S} (hβ : β ≠ 1) : PerfectInLayer β := by
  intro P hP hperf
  suffices hP0 : P = ⊥ by
    rw [hP0]
    exact bot_le
  have hCtop : fixSubgroup β ≠ ⊤ := by
    intro htop
    apply hβ
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ fixSubgroup β := by rw [htop]; exact Subgroup.mem_top x
    rw [MulAut.one_apply]
    exact mem_fixSubgroup.1 hx
  have hPtop : P ≠ ⊤ := fun h => hCtop (top_le_iff.1 (h ▸ hP))
  by_contra hPne
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
  have hidx : P.index ≠ 1 := fun h => hPtop (Subgroup.index_eq_one.1 h)
  have hmul := Subgroup.card_mul_index P
  rw [hc] at hmul
  have hdvd : Nat.card ↥P ∣ 168 := ⟨P.index, hmul.symm⟩
  have h168 : Nat.card ↥P ≠ 168 := by
    intro h
    rw [h] at hmul
    have : P.index = 1 := by omega
    exact hidx this
  have h84 : Nat.card ↥P ≠ 84 := by
    intro h
    rw [h] at hmul
    have h2 : P.index = 2 := by omega
    haveI : P.Normal := Subgroup.normal_of_index_eq_two h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h' | h'
    · exact hPne h'
    · exact hPtop h'
  exact Group.IsPerfect.not_isSolvable ↥P (solvable_of_card_dvd_168 hdvd h84 h168)

theorem perfect_eq_bot_of_not_seven {S : Type} [Group S] [Finite S] (hc : Nat.card S = 6048)
    {x : S} (h7 : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set S))) {P : Subgroup S}
    (hP : P ≤ Subgroup.centralizer ({x} : Set S)) (hperf : ⁅P, P⁆ = P) : P = ⊥ := by
  by_contra hne
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
  have hPC : Nat.card P ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) :=
    Subgroup.card_dvd_of_le hP
  have hCS : Nat.card (Subgroup.centralizer ({x} : Set S)) ∣ 6048 := by
    rw [← hc]
    exact Subgroup.card_subgroup_dvd_card _
  have hP7 : ¬ 7 ∣ Nat.card P := fun h => h7 (h.trans hPC)
  have hcop : Nat.Coprime (Nat.card P) 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hP7).symm
  have h6 : Nat.card P ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
    norm_num
    exact hPC.trans hCS
  have hdvd : Nat.card P ∣ 2 ^ 5 * 3 ^ 3 := hcop.dvd_of_dvd_mul_right h6
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.1 hdvd
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ha
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hb
  haveI : Fintype ↥P := Fintype.ofFinite ↥P
  exact Group.IsPerfect.not_isSolvable ↥P
    (CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hab]))

theorem perfectInLayer_conj_u33 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (hc : Nat.card S = 6048)
    (hidx : (MulAut.conj : S →* MulAut S).range.index ≤ 2)
    (h7 : ∀ x : S, x ^ 3 = 1 → x ≠ 1 → ¬ 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)))
    {β : MulAut S} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) : PerfectInLayer β := by
  have hz : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hnc
  have hinj := conj_injective_of_center hz
  have hfin : Finite (MulAut S) := inferInstance
  have hO : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) := by
    change ¬ 3 ∣ (MulAut.conj : S →* MulAut S).range.index
    have hne : (MulAut.conj : S →* MulAut S).range.index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    intro h3
    have hle : (MulAut.conj : S →* MulAut S).range.index = 1 ∨
        (MulAut.conj : S →* MulAut S).range.index = 2 := by
      omega
    rcases hle with h | h <;> rw [h] at h3 <;> omega
  obtain ⟨x, rfl⟩ := exists_conj_of_pow_eq_one Nat.prime_three hO hβ3
  have hx3 : x ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hβ3
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  intro P hP hperf
  rw [CFSG.LocalAnalysis.GLTheoremA.fixSubgroup_conj_eq_centralizer'] at hP ⊢
  rw [perfect_eq_bot_of_not_seven hc (h7 x hx3 hx1) hP hperf]
  exact bot_le

end CFSG.LocalAnalysis.GLTheoremA.I142C
