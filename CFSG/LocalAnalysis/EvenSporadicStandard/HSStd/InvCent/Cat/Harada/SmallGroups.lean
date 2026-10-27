module

public import Mathlib.GroupTheory.Solvable
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSmallAlternating

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup
open scoped commutatorElement

theorem isMulCommutative_of_card_dvd_four {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 4) : IsMulCommutative H := by
  have h4 : Nat.card H ∣ 2 ^ 2 := by simpa using h
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
  interval_cases k
  · have h1 : Nat.card H = 1 := by simpa using hk'
    haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.1 h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · haveI : Fact (Nat.Prime (Nat.card H)) :=
      ⟨by rw [show Nat.card H = 2 by simpa using hk']; exact Nat.prime_two⟩
    haveI : IsCyclic H := isCyclic_of_prime_card (p := Nat.card H) rfl
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hk')

theorem commutator_eq_bot_of_isMulCommutative {H : Type*} [Group H] [IsMulCommutative H] :
    commutator H = ⊥ := by
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.2 fun a _ b _ => ?_
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2
    ((inferInstance : IsMulCommutative H).is_comm.comm a b)

theorem commutator_eq_bot_of_comm {H : Type*} [Group H] {N : Subgroup H}
    (hN : IsMulCommutative N) : ⁅N, N⁆ = ⊥ := by
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [Subgroup.mem_bot]
  have h := hN.is_comm.comm (⟨a, ha⟩ : N) ⟨b, hb⟩
  exact commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val h)

theorem derivedSeries_two_eq_bot_of_normal {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : IsMulCommutative N) (hQ : IsMulCommutative (H ⧸ N)) : derivedSeries H 2 = ⊥ := by
  have hle : commutator H ≤ N := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    have h := hQ.is_comm.comm (QuotientGroup.mk a) (QuotientGroup.mk b)
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' N) ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h
  rw [eq_bot_iff, ← commutator_eq_bot_of_comm hN]
  exact Subgroup.commutator_mono hle hle

theorem derivedSeries_two_alternatingGroup_four :
    derivedSeries (alternatingGroup (Fin 4)) 2 = ⊥ := by
  have hmul : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 → a * b * (a * b) = 1 := by
    decide +kernel
  have hinv : ∀ a : alternatingGroup (Fin 4), a * a = 1 → a⁻¹ * a⁻¹ = 1 := by decide +kernel
  have hcomm : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 → a * b = b * a := by
    decide +kernel
  have hcom : ∀ a b : alternatingGroup (Fin 4), ⁅a, b⁆ * ⁅a, b⁆ = 1 := by decide +kernel
  let V : Subgroup (alternatingGroup (Fin 4)) :=
    { carrier := {x | x * x = 1}
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := by simp
      inv_mem' := fun {a} ha => hinv a ha }
  have hV : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (hcomm a b a.2 b.2)⟩⟩
  have hle : commutator (alternatingGroup (Fin 4)) ≤ V :=
    Subgroup.commutator_le.2 fun a _ b _ => hcom a b
  rw [derivedSeries_succ, derivedSeries_one, eq_bot_iff, ← commutator_eq_bot_of_comm hV]
  exact Subgroup.commutator_mono hle hle

theorem derivedSeries_two_eq_bot_of_card_dvd_twelve {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 12) : derivedSeries H 2 = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdiv : Nat.card H ∈ Nat.divisors 12 := by simpa using h
  have hc : Nat.card H = 1 ∨ Nat.card H = 2 ∨ Nat.card H = 3 ∨ Nat.card H = 4 ∨
      Nat.card H = 6 ∨ Nat.card H = 12 := by
    have h12 : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
    rw [h12] at hdiv
    simpa using hdiv
  have hcommCase : IsMulCommutative H → derivedSeries H 2 = ⊥ := by
    intro hcm
    rw [eq_bot_iff, ← commutator_eq_bot_of_isMulCommutative (H := H)]
    exact (derivedSeries_antitone (G := H) (by norm_num : 1 ≤ 2))
  have hsyl : Nat.card H = 6 ∨ Nat.card H = 12 → derivedSeries H 2 = ⊥ := by
    intro hH
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 H))
    have hfac : (Nat.card H).factorization 3 = 1 := by
      rcases hH with hH | hH <;> rw [hH]
      · rw [show 6 = 2 * 3 by norm_num,
          Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 2 3),
          Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
      · rw [show 12 = 3 * 4 by norm_num,
          Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
          Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
    have hP : Nat.card (P : Subgroup H) = 3 := by
      have h1 := P.card_eq_multiplicity
      rw [hfac] at h1
      simpa using h1
    have hidx : (P : Subgroup H).index * 3 = Nat.card H := by
      have h1 := (P : Subgroup H).card_mul_index
      rw [hP] at h1
      omega
    have hdvd : Nat.card (Sylow 3 H) ∣ (P : Subgroup H).index := Sylow.card_dvd_index P
    have hmod : Nat.card (Sylow 3 H) % 3 = 1 := by
      have h1 := card_sylow_modEq_one 3 H
      simpa [Nat.ModEq] using h1
    have hPcomm : IsMulCommutative (P : Subgroup H) := by
      haveI : Fact (Nat.Prime (Nat.card (P : Subgroup H))) := ⟨by rw [hP]; exact Nat.prime_three⟩
      haveI : IsCyclic (P : Subgroup H) :=
        isCyclic_of_prime_card (p := Nat.card (P : Subgroup H)) rfl
      infer_instance
    have hn : Nat.card (Sylow 3 H) = 1 ∨ (Nat.card H = 12 ∧ Nat.card (Sylow 3 H) = 4) := by
      rcases hH with hH | hH
      · left
        have hi : (P : Subgroup H).index = 2 := by omega
        rw [hi] at hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        have hpos : 0 < Nat.card (Sylow 3 H) := Nat.card_pos
        omega
      · have hi : (P : Subgroup H).index = 4 := by omega
        rw [hi] at hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        have hpos : 0 < Nat.card (Sylow 3 H) := Nat.card_pos
        have h4 : Nat.card (Sylow 3 H) ∈ Nat.divisors 4 := by simpa using hdvd
        have h4' : Nat.divisors 4 = {1, 2, 4} := by decide
        rw [h4'] at h4
        simp only [Finset.mem_insert, Finset.mem_singleton] at h4
        rcases h4 with h4 | h4 | h4
        · left; exact h4
        · omega
        · right; exact ⟨hH, h4⟩
    rcases hn with hn | ⟨hH12, hn⟩
    · haveI : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.1 hn).1
      haveI : (P : Subgroup H).Normal := Sylow.normal_of_subsingleton P
      refine derivedSeries_two_eq_bot_of_normal (P : Subgroup H) hPcomm ?_
      have hq : Nat.card (H ⧸ (P : Subgroup H)) ∣ 4 := by
        rw [← Subgroup.index_eq_card]
        rcases hH with hH | hH
        · have hi : (P : Subgroup H).index = 2 := by omega
          rw [hi]; norm_num
        · have hi : (P : Subgroup H).index = 4 := by omega
          rw [hi]
      exact isMulCommutative_of_card_dvd_four hq
    · obtain ⟨e⟩ := CFSG.Glauberman.Dickson.huppert_II_8_17_b_order_twelve_four_sylow_three
        hH12 hn
      have h1 := map_derivedSeries_le_derivedSeries e.toMonoidHom 2
      rw [derivedSeries_two_alternatingGroup_four, le_bot_iff] at h1
      rw [eq_bot_iff]
      intro x hx
      have hx' : e.toMonoidHom x ∈ (derivedSeries H 2).map e.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact e.injective (by simpa using hx')
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact hcommCase (isMulCommutative_of_card_dvd_four (by rw [hc]; norm_num))
  · exact hcommCase (isMulCommutative_of_card_dvd_four (by rw [hc]; norm_num))
  · haveI : Fact (Nat.Prime (Nat.card H)) := ⟨by rw [hc]; exact Nat.prime_three⟩
    haveI : IsCyclic H := isCyclic_of_prime_card (p := Nat.card H) rfl
    exact hcommCase inferInstance
  · exact hcommCase (isMulCommutative_of_card_dvd_four (by rw [hc]))
  · exact hsyl (Or.inl hc)
  · exact hsyl (Or.inr hc)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
