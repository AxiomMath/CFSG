module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Open CFSG.QuasithinUnique

section Tools

theorem charTwo_map_mulEquiv {K A : Type*} [Group K] [Group A] (e : K ≃* A) {X : Subgroup K}
    (h : CharTwo X) : CharTwo (X.map e.toMonoidHom) := by
  rw [charTwo_iff_internal] at h ⊢
  exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
    (X.equivMapOfInjective e.toMonoidHom e.injective) h

theorem not_charTwo_of_normal_odd {A : Type*} [Group A] [Finite A] {C N : Subgroup A}
    (hNC : N ≤ C) (hn : (N.subgroupOf C).Normal) (hodd : Odd (Nat.card N)) (hN1 : N ≠ ⊥) :
    ¬ CharTwo C := by
  intro hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hint := charTwo_iff_internal.mp hC
  have hchar : CFSG.IsCharacteristicP 2 C := by
    rw [CFSG.IsCharacteristicP]
    exact hint
  have hbot := CFSG.pPrimeCore_eq_bot_of_isCharacteristicP C 2 hchar
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  have hle : N.subgroupOf C ≤ CFSG.pPrimeCore 2 C := le_sSup ⟨hn, hcop⟩
  rw [hbot] at hle
  apply hN1
  rw [eq_bot_iff]
  intro x hx
  have h1 := hle (show (⟨x, hNC hx⟩ : C) ∈ N.subgroupOf C from hx)
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

theorem not_charTwo_of_pCoreOf_eq_bot {A : Type*} [Group A] {C : Subgroup A} (hC : C ≠ ⊥)
    (hp : pCoreOf 2 C = ⊥) : ¬ CharTwo C := by
  intro h
  apply hC
  rw [eq_bot_iff]
  intro x hx
  have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 C : Set A) := by
    rw [hp, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := Subgroup.mem_bot.mp hy
    rw [hy1]
    simp
  have := h ⟨hx, hxc⟩
  rwa [hp] at this

theorem pCoreOf_eq_bot_of_involution_products {A : Type*} [Group A] [Finite A] {C : Subgroup A}
    (h : ∀ x ∈ C, x * x = 1 → x ≠ 1 →
      ∃ g ∈ C, (x * (g * x * g⁻¹)) ^ 3 = 1 ∧ x * (g * x * g⁻¹) ≠ 1) :
    pCoreOf 2 C = ⊥ := by
  by_contra hne
  set Q := pCoreOf 2 C with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 C
  have hCQ : C ≤ Subgroup.normalizer (Q : Set A) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 C
  have hQC : Q ≤ C := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 C
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hk
  have hdvd : 2 ∣ Nat.card Q := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : (x : A) * (x : A) = 1 := by
    have : (x : A) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx
      exact hx ▸ pow_orderOf_eq_one _
    simpa [sq] using this
  have hx1 : (x : A) ≠ 1 := by
    intro h1
    have : orderOf x = 1 := by
      rw [← Subgroup.orderOf_coe, h1, orderOf_one]
    rw [hx] at this
    exact absurd this (by norm_num)
  obtain ⟨g, hg, hy3, hy1⟩ := h (x : A) (hQC x.2) hx2 hx1
  have hxg : g * (x : A) * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hCQ hg) x).mp x.2
  have hyQ : (x : A) * (g * x * g⁻¹) ∈ Q := Q.mul_mem x.2 hxg
  obtain ⟨m, hm⟩ := hQ2 ⟨_, hyQ⟩
  have hm' : ((x : A) * (g * x * g⁻¹)) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hdvd3 : orderOf ((x : A) * (g * x * g⁻¹)) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
  have hdvd2 : orderOf ((x : A) * (g * x * g⁻¹)) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have h3 : orderOf ((x : A) * (g * x * g⁻¹)) = 1 ∨ orderOf ((x : A) * (g * x * g⁻¹)) = 3 :=
    (Nat.dvd_prime (by norm_num)).mp hdvd3
  rcases h3 with h3 | h3
  · exact hy1 (orderOf_eq_one_iff.mp h3)
  · rw [h3] at hdvd2
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd2 : 3 ∣ 2)
    omega

theorem map_centralizer_singleton {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (a : X) :
    (Subgroup.centralizer ({a} : Set X)).map e.toMonoidHom = Subgroup.centralizer ({e a} : Set Y) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

end Tools

end CFSG.QuasithinUnique.Ch1
