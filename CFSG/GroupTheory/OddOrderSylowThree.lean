module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Walter.Cited.HuppertPlane
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.GroupTheory

open Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem normalizer_le_centralizer_of_odd_order_sylow_three (hodd : Odd (Nat.card H))
    (P : Sylow 3 H) (hP9 : Nat.card (P : Subgroup H) ∣ 9) :
    normalizer (P : Set H) ≤ centralizer (P : Set H) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcomm : IsMulCommutative ↥(P : Subgroup H) := by
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hP9 : Nat.card (P : Subgroup H) ∣ 3 ^ 2)
    interval_cases k
    · have hcard : Nat.card ↥(P : Subgroup H) = 1 := by simpa using hk
      haveI : Subsingleton ↥(P : Subgroup H) := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact ⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩
    · have hcyc : IsCyclic ↥(P : Subgroup H) :=
        isCyclic_of_prime_card (by simpa using hk)
      exact hcyc.isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
        (G := ↥(P : Subgroup H)) (by simpa using hk)
  have hP_le_C : (P : Subgroup H) ≤ centralizer (P : Set H) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hPcomm
  let N : Subgroup H := normalizer (P : Set H)
  let C : Subgroup H := centralizer (P : Set H)
  have hPN : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
  have hPC : (P : Subgroup H) ≤ C := hP_le_C
  have hker : (P : Subgroup H).normalizerMonoidHom.ker = C.subgroupOf N := by
    simpa [N, C] using Subgroup.normalizerMonoidHom_ker (P : Subgroup H)
  let f : N →* MulAut ↥(P : Subgroup H) := (P : Subgroup H).normalizerMonoidHom
  let Q := N ⧸ f.ker
  have hcardQ : Nat.card Q = f.ker.index := (Subgroup.index_eq_card (H := f.ker)).symm
  have hQodd : Odd (Nat.card Q) := by
    rw [hcardQ]
    rw [show f.ker = C.subgroupOf N from hker]
    exact Odd.of_dvd_nat hodd
      ((Subgroup.index_dvd_card (H := C.subgroupOf N)).trans (Subgroup.card_subgroup_dvd_card N))
  have h3Q : ¬ 3 ∣ Nat.card Q := by
    rw [hcardQ]
    rw [show f.ker = C.subgroupOf N from hker]
    intro h
    change 3 ∣ C.relIndex N at h
    have h1 : C.relIndex N ∣ (P : Subgroup H).relIndex N :=
      Subgroup.relIndex_dvd_of_le_left N hPC
    have h2 : (P : Subgroup H).relIndex N ∣ (P : Subgroup H).index :=
      Subgroup.relIndex_dvd_index_of_le hPN
    exact P.not_dvd_index (h.trans (h1.trans h2))
  by_contra hle
  have hQcard : 1 < Nat.card Q := by
    by_contra hle1
    push Not at hle1
    have h1 : Nat.card Q = 1 := by
      have := Nat.card_pos (α := Q)
      omega
    have hidx : f.ker.index = 1 := by rw [← hcardQ]; exact h1
    have htop : f.ker = ⊤ := Subgroup.index_eq_one.mp hidx
    apply hle
    rw [← Subgroup.subgroupOf_eq_top]
    calc C.subgroupOf N = f.ker := hker.symm
      _ = ⊤ := htop
  haveI : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp hQcard
  obtain ⟨q, hq1⟩ := exists_ne (1 : Q)
  let φ : MulAut ↥(P : Subgroup H) := QuotientGroup.kerLift f q
  have hφne : φ ≠ 1 := by
    intro h
    exact hq1 (QuotientGroup.kerLift_injective f (by simpa [φ] using h))
  have hφdvd : orderOf φ ∣ Nat.card Q :=
    (orderOf_map_dvd (QuotientGroup.kerLift f) q).trans (orderOf_dvd_natCard q)
  have hφodd : Odd (orderOf φ) := hQodd.of_dvd_nat hφdvd
  have hφ3 : ¬ 3 ∣ orderOf φ := fun h => h3Q (h.trans hφdvd)
  have hφgt : 1 < orderOf φ := by
    have hpos := orderOf_pos φ
    have hne : orderOf φ ≠ 1 := fun h => hφne (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨r, hr, hrdvdφ⟩ := Nat.exists_prime_and_dvd hφgt.ne'
  have hrodd : Odd r := hφodd.of_dvd_nat hrdvdφ
  have hr3 : r ≠ 3 := fun h => hφ3 (h ▸ hrdvdφ)
  have hr5 : 5 ≤ r := by
    have hr2 : r ≠ 2 := by
      rintro rfl
      norm_num at hrodd
    rcases hrodd with ⟨k, hk⟩
    have := hr.two_le
    omega
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨ψz, hψzord⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers φ) r
    (by rwa [Nat.card_zpowers])
  let ψ : MulAut ↥(P : Subgroup H) := ψz
  have hψord : orderOf ψ = r := by
    rw [show orderOf ψ = orderOf ψz from Subgroup.orderOf_coe ψz, hψzord]
  have hψne : ψ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hψord
    omega
  have hψpow : ψ ^ r = 1 := by rw [← hψord]; exact pow_orderOf_eq_one ψ
  have hmod := CFSG.Walter.Huppert.card_fixedSubgroup_modEq (p := r) (σ := ψ) (k := 1)
    (by simpa using hψpow)
  have hfix_ne_top : CFSG.Walter.Huppert.fixedSubgroup ψ ≠ ⊤ := by
    intro htop
    apply hψne
    ext v
    have hv : v ∈ CFSG.Walter.Huppert.fixedSubgroup ψ := by
      rw [htop]
      exact Subgroup.mem_top v
    simpa using CFSG.Walter.Huppert.mem_fixedSubgroup.mp hv
  have hcard_lt : Nat.card (CFSG.Walter.Huppert.fixedSubgroup ψ) <
      Nat.card ↥(P : Subgroup H) := by
    have := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hfix_ne_top)
    rwa [Subgroup.card_top] at this
  have hfix_le : Nat.card (CFSG.Walter.Huppert.fixedSubgroup ψ) ≤
      Nat.card ↥(P : Subgroup H) := hcard_lt.le
  have hrdvd : r ∣ Nat.card ↥(P : Subgroup H) -
      Nat.card (CFSG.Walter.Huppert.fixedSubgroup ψ) :=
    (Nat.modEq_iff_dvd' hfix_le).mp hmod.symm
  obtain ⟨k, hk2, hkP⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hP9 : Nat.card (P : Subgroup H) ∣ 3 ^ 2)
  have hfixdvd : Nat.card (CFSG.Walter.Huppert.fixedSubgroup ψ) ∣
      Nat.card ↥(P : Subgroup H) := Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj2, hjfix⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).1 (hkP ▸ hfixdvd)
  have hjk : j < k := by
    have hlt' : 3 ^ j < 3 ^ k := by simpa [hjfix, hkP] using hcard_lt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hlt'
  rw [hkP, hjfix] at hrdvd
  have hk9 : 3 ^ k ≤ 9 := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).2 hk2
    simpa using this
  have hdiff_pos : 0 < 3 ^ k - 3 ^ j := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).2 hjk
    omega
  have hrle8 : r ≤ 8 := by
    have hle' : r ≤ 3 ^ k - 3 ^ j := Nat.le_of_dvd hdiff_pos hrdvd
    have hj1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega
  interval_cases r
  · interval_cases k
    · omega
    · have hj : j = 0 := by omega
      subst j
      norm_num at hrdvd
    · have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with rfl | rfl <;> norm_num at hrdvd
  · norm_num at hr
  · interval_cases k
    · omega
    · have hj : j = 0 := by omega
      subst j
      norm_num at hrdvd
    · have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with rfl | rfl <;> norm_num at hrdvd
  · norm_num at hr

theorem exists_normal_isPGroup_quotient_of_odd_order_sylow_three (hodd : Odd (Nat.card H))
    (P : Sylow 3 H) (hP9 : Nat.card (P : Subgroup H) ∣ 9)
    (hPne : (P : Subgroup H) ≠ ⊥) :
    ∃ N : Subgroup H, ∃ hN : N.Normal, N ≠ ⊤ ∧ (by
      letI := hN
      exact IsPGroup 3 (H ⧸ N)) := by
  have hNC := normalizer_le_centralizer_of_odd_order_sylow_three hodd P hP9
  obtain ⟨K, hK, -, hKindex, -, -, -, -, -, ⟨e, -⟩, -⟩ :=
    burnside_normal_complement P hNC
  letI : K.Normal := hK
  refine ⟨K, hK, ?_, ?_⟩
  · intro hKtop
    have hcard : Nat.card (P : Subgroup H) = 1 := by
      rw [← hKindex, hKtop]
      exact Subgroup.index_top
    exact hPne (Subgroup.card_eq_one.mp hcard)
  · exact IsPGroup.of_equiv P.isPGroup' e

end CFSG.GroupTheory
