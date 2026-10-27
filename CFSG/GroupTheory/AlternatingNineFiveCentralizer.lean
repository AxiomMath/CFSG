module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator
import CFSG.GroupTheory.TwoReflections
import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Basic
import CFSG.Quasithin.H13.GoldschmidtC137SQFrat

public section

namespace CFSG.GroupTheory.AlternatingNineFiveCentralizer

open Equiv Equiv.Perm
open scoped commutatorElement

private abbrev A9 : Type := alternatingGroup (Fin 9)

private def x : A9 := ⟨c[0, 1, 2, 3, 4], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def a : A9 := ⟨c[5, 6, 7], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def b : A9 := ⟨c[5, 6] * c[7, 8], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def c : A9 := ⟨c[5, 7] * c[6, 8], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def u : A9 := ⁅a, b⁆

private def v : A9 := ⁅a, c⁆

private theorem x_pow_five : x ^ 5 = 1 := Subtype.ext (by decide)

private theorem x_ne_one : x ≠ 1 := by decide

private theorem x_orderOf : orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime x_pow_five x_ne_one

private theorem a_comm_x : a * x = x * a := Subtype.ext (by decide)

private theorem b_comm_x : b * x = x * b := Subtype.ext (by decide)

private theorem c_comm_x : c * x = x * c := Subtype.ext (by decide)

private theorem u_sq_one : u ^ 2 = 1 := Subtype.ext (by decide)

private theorem v_sq_one : v ^ 2 = 1 := Subtype.ext (by decide)

private theorem u_ne_one : u ≠ 1 := by decide

private theorem v_ne_one : v ≠ 1 := by decide

private theorem u_ne_v : u ≠ v := by decide

private theorem card_alternatingNine_factorization :
    (Nat.card A9).factorization 5 = 1 := by
  have hpprime : Nat.Prime 5 := by decide
  have hcard : Nat.card A9 = 181440 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hdvd : 5 ∣ Nat.card A9 := by rw [hcard]; decide
  have h1 : 1 ≤ (Nat.card A9).factorization 5 :=
    (hpprime.dvd_iff_one_le_factorization (by rw [hcard]; decide)).mp hdvd
  have hnot : ¬ 5 ^ 2 ∣ Nat.card A9 := by rw [hcard]; decide
  have hlt : (Nat.card A9).factorization 5 < 2 := by
    by_contra h
    have h2 : 2 ≤ (Nat.card A9).factorization 5 := by omega
    exact hnot ((hpprime.pow_dvd_iff_le_factorization (by rw [hcard]; decide)).mpr h2)
  omega

private noncomputable def pbar [Fact (Nat.Prime 5)] : Sylow 5 A9 :=
  Sylow.ofCard (Subgroup.zpowers x) (by
    rw [Nat.card_zpowers, x_orderOf, card_alternatingNine_factorization]
    decide)

private theorem coe_pbar [Fact (Nat.Prime 5)] :
    (pbar : Subgroup A9) = Subgroup.zpowers x := by
  rw [pbar, Sylow.coe_ofCard]

private lemma exists_sylow_map_eq {X : Type} [Group X] [Finite X]
    [Fact (Nat.Prime 5)] (φ : X →* alternatingGroup (Fin 9))
    (hφ : Function.Surjective φ) :
    ∃ S : Sylow 5 X, (S : Subgroup X) ≠ ⊥ ∧
      ((S : Subgroup X).map φ = (pbar : Subgroup A9)) := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective (p := 5) (f := φ) hφ pbar
  have hImage : ((S : Subgroup X).map φ) = (pbar : Subgroup A9) := by
    rw [← Sylow.coe_mapSurjective hφ S]
    exact congrArg (fun T : Sylow 5 A9 => (T : Subgroup A9)) hS
  have hxP : x ∈ (pbar : Subgroup A9) := by
    rw [coe_pbar]
    exact Subgroup.mem_zpowers x
  have hPne : (pbar : Subgroup A9) ≠ ⊥ := by
    intro hbot
    exact x_ne_one (Subgroup.mem_bot.mp (hbot ▸ hxP))
  have hSne : (S : Subgroup X) ≠ ⊥ := by
    intro hbot
    have hbot' : (pbar : Subgroup A9) = ⊥ := by
      rw [← hImage, hbot, Subgroup.map_bot]
    exact hPne hbot'
  exact ⟨S, hSne, hImage⟩

private lemma exists_central_order_five {X : Type} [Group X] [Finite X]
    [Fact (Nat.Prime 5)]
    (hX : ∀ s : X, orderOf s = 5 →
      IsCyclic (Subgroup.centralizer ({s} : Set X)))
    (S : Sylow 5 X) (hSne : (S : Subgroup X) ≠ ⊥) :
    ∃ s : X, orderOf s = 5 ∧ s ∈ (S : Subgroup X) ∧ IsCyclic (S : Subgroup X) := by
  classical
  let Z : Subgroup (S : Subgroup X) := Subgroup.center (S : Subgroup X)
  have hSnt : Nontrivial (S : Subgroup X) :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup X)).mpr hSne
  letI : Nontrivial (S : Subgroup X) := hSnt
  have hZnt : Nontrivial Z := IsPGroup.center_nontrivial (Sylow.isPGroup' S)
  have hZpg : IsPGroup 5 Z := (Sylow.isPGroup' S).to_subgroup Z
  obtain ⟨k, hkpos, hkcard⟩ := hZpg.nontrivial_iff_card.mp hZnt
  have hdiv : 5 ∣ Nat.card Z := by
    rw [hkcard]
    exact dvd_pow_self 5 (Nat.ne_of_gt hkpos)
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := Z) 5 hdiv
  let s : X := ((z : (S : Subgroup X)) : X)
  have hsord : orderOf s = 5 := by
    dsimp [s]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzord]
  have hsS : s ∈ (S : Subgroup X) := (z : (S : Subgroup X)).2
  have hSC : (S : Subgroup X) ≤ Subgroup.centralizer ({s} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    have hzy : (⟨y, hy⟩ : (S : Subgroup X)) * (z : Z) = (z : Z) * ⟨y, hy⟩ :=
      Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
    exact congrArg (fun w : (S : Subgroup X) => (w : X)) hzy.symm
  haveI : IsCyclic (Subgroup.centralizer ({s} : Set X)) := hX s hsord
  have hScyc : IsCyclic (S : Subgroup X) :=
    isCyclic_of_injective (Subgroup.inclusion hSC) (Subgroup.inclusion_injective hSC)
  exact ⟨s, hsord, hsS, hScyc⟩

private lemma commutator_mem_centralizer {X : Type} [Group X] [Finite X]
    (S : Subgroup X) [IsCyclic S] {s : X} (hs : s ∈ S) {n₁ n₂ : X}
    (hn₁ : n₁ ∈ Subgroup.normalizer (S : Set X))
    (hn₂ : n₂ ∈ Subgroup.normalizer (S : Set X)) :
    ⁅n₁, n₂⁆ ∈ Subgroup.centralizer ({s} : Set X) := by
  have hcomm : ⁅Subgroup.normalizer (S : Set X), Subgroup.normalizer (S : Set X)⁆ ≤
      Subgroup.centralizer ({s} : Set X) := by
    refine (CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer S
      (Subgroup.normalizer (S : Set X)) (Subgroup.normalizer (S : Set X))
      le_rfl le_rfl).trans ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs)
  exact Subgroup.commutator_le.mp hcomm n₁ hn₁ n₂ hn₂

private lemma exists_lift_normalizer_of_commutes {X : Type} [Group X] [Finite X]
    [Fact (Nat.Prime 5)] (φ : X →* alternatingGroup (Fin 9))
    (hφ : Function.Surjective φ) (S : Sylow 5 X)
    (hImage : ((S : Subgroup X).map φ = (pbar : Subgroup A9)))
    (n : A9) (hn : n * x = x * n) :
    ∃ m ∈ Subgroup.normalizer (S : Set X), φ m = n := by
  have hnN : n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set A9) :=
    CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq (by
      rw [hn, mul_assoc, mul_inv_cancel, mul_one])
  have hnN' : n ∈ Subgroup.normalizer
      (((S : Subgroup X).map φ : Subgroup A9) : Set A9) := by
    rwa [hImage, coe_pbar]
  exact CFSG.Quasithin.H13.U3.GC137.SQ.exists_mem_normalizer_map_eq φ hφ S hnN'

private lemma image_not_two_involutions {X : Type} [Group X] [Finite X]
    (C : Subgroup X) [IsCyclic C] (φ : X →* alternatingGroup (Fin 9))
    (hu : u ∈ C.map φ) (hv : v ∈ C.map φ) : False := by
  classical
  let D : Subgroup A9 := C.map φ
  have hDcyc : IsCyclic D :=
    isCyclic_of_surjective (φ.subgroupMap C) (φ.subgroupMap_surjective C)
  letI : IsCyclic D := hDcyc
  let uD : D := ⟨u, hu⟩
  let vD : D := ⟨v, hv⟩
  have huD_sq : uD ^ 2 = 1 := by
    apply Subtype.ext
    exact u_sq_one
  have hvD_sq : vD ^ 2 = 1 := by
    apply Subtype.ext
    exact v_sq_one
  have huD_ne : uD ≠ 1 := by
    intro h
    exact u_ne_one (congrArg (fun y : D => (y : A9)) h)
  have hvD_ne : vD ≠ 1 := by
    intro h
    exact v_ne_one (congrArg (fun y : D => (y : A9)) h)
  have huvD : uD ≠ vD := by
    intro h
    exact u_ne_v (congrArg (fun y : D => (y : A9)) h)
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact huvD (CFSG.EvenSporadicStandard.ThStd.eq_of_orderOf_eq_two_of_isCyclic
    (orderOf_eq_prime huD_sq huD_ne) (orderOf_eq_prime hvD_sq hvD_ne))

theorem not_surjective_of_isCyclic_centralizer {X : Type} [Group X] [Finite X]
    (hX : ∀ s : X, orderOf s = 5 → IsCyclic (Subgroup.centralizer ({s} : Set X)))
    (φ : X →* alternatingGroup (Fin 9)) : ¬ Function.Surjective φ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hφ
  obtain ⟨S, hSne, hImage⟩ := exists_sylow_map_eq φ hφ
  obtain ⟨s, hsord, hsS, hScyc⟩ := exists_central_order_five hX S hSne
  let C : Subgroup X := Subgroup.centralizer ({s} : Set X)
  have hCcyc : IsCyclic C := hX s hsord
  letI : IsCyclic C := hCcyc
  letI : IsCyclic (S : Subgroup X) := hScyc
  obtain ⟨na, hnaN, hna⟩ := exists_lift_normalizer_of_commutes φ hφ S hImage a a_comm_x
  obtain ⟨nb, hnbN, hnb⟩ := exists_lift_normalizer_of_commutes φ hφ S hImage b b_comm_x
  obtain ⟨nc, hncN, hnc⟩ := exists_lift_normalizer_of_commutes φ hφ S hImage c c_comm_x
  have hc1 : ⁅na, nb⁆ ∈ C := commutator_mem_centralizer S hsS hnaN hnbN
  have hc2 : ⁅na, nc⁆ ∈ C := commutator_mem_centralizer S hsS hnaN hncN
  have hmapc1 : φ ⁅na, nb⁆ = u := by
    rw [map_commutatorElement, hna, hnb]
    rfl
  have hmapc2 : φ ⁅na, nc⁆ = v := by
    rw [map_commutatorElement, hna, hnc]
    rfl
  have huD : u ∈ C.map φ := by
    rw [← hmapc1]
    exact Subgroup.mem_map_of_mem φ hc1
  have hvD : v ∈ C.map φ := by
    rw [← hmapc2]
    exact Subgroup.mem_map_of_mem φ hc2
  exact image_not_two_involutions C φ huD hvD

end CFSG.GroupTheory.AlternatingNineFiveCentralizer
