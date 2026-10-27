module

public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
public import CFSG.LocalAnalysis.ComponentInitial.StandardCriterion
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.Assembly (IsComponentOf IsElemAbelian)

variable {G : Type*} [Group G]

theorem card_le_pow_pRank_of_le [Finite G] {p : ℕ} [hp : Fact p.Prime] {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ CFSG.Assembly.pRank p H := by
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    calc k ≤ p ^ k := (Nat.lt_pow_self hp.out.one_lt).le
      _ = Nat.card E := hk.symm
      _ ≤ Nat.card G := card_le_card_group E
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos (le_csSup hbdd ⟨E, hEH, hE, hk⟩)

theorem pRank_le_of_forall_card_le {H : Type*} [Group H] {p r : ℕ} (hp : 1 < p)
    (h : ∀ A : Subgroup H, IsElementaryAbelian p A → Nat.card A ≤ p ^ r) : CFSG.pRank p H ≤ r :=
  csSup_le' fun _ ⟨A, hA, hk⟩ => (Nat.pow_le_pow_iff_right hp).mp (hk ▸ h A hA)

theorem map_conj_le_centralizer_of_commutator_eq_bot {J : Subgroup G} {g : G}
    (hg : ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    J.map (MulAut.conj g).toMonoidHom ≤ centralizer (J : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro j hj
  have h := commutator_mem_commutator hj hx
  rw [hg, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem pRank_le_one_of_map_conj_le_centralizer [Finite G] {J : Subgroup G} {g : G}
    (hJg : J.map (MulAut.conj g).toMonoidHom ≤ centralizer (J : Set G))
    (hr : CFSG.Assembly.pRank 2 (centralizer (J : Set G)) ≤ 1) : CFSG.pRank 2 J ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine pRank_le_of_forall_card_le one_lt_two fun A hA => ?_
  set E := (A.map J.subtype).map (MulAut.conj g).toMonoidHom
  have hEC : E ≤ centralizer (J : Set G) :=
    (map_mono (map_le_iff_le_comap.mpr fun x _ => x.2)).trans hJg
  have hE : IsElemAbelian 2 E :=
    isElemAbelian_map (isElemAbelian_map (isElemAbelian_iff_isElementaryAbelian.mpr hA) _) _
  have hcard : Nat.card E = Nat.card A := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective J.subtype_injective]
  rw [← hcard]
  exact (card_le_pow_pRank_of_le hEC hE).trans (Nat.pow_le_pow_right two_pos hr)

variable [Finite G]

theorem rank_one_centralizer_standard_or_quaternion {a : G} {J : Subgroup G}
    (ha : orderOf a = 2) (hJ : IsComponentOf J (centralizer {a}))
    (hr : CFSG.Assembly.pRank 2 (centralizer (J : Set G)) = 1) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup J ∨
      ∃ z : G, orderOf z = 2 ∧ z ∈ J ∧ z ∈ centralizer (J : Set G) ∧
        IsComponentOf J (centralizer {z}) ∧
        ∃ r : ℕ, 3 ≤ r ∧ ∃ T : Sylow 2 J,
          Nonempty ((T : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (J : Set G) with hC
  have hC2 : ∀ E : Subgroup G, E ≤ C → IsElemAbelian 2 E → Nat.card E ≤ 2 := fun E hEC hE =>
    (card_le_pow_pRank_of_le hEC hE).trans (by rw [hr, pow_one])
  have hcomp : ∀ t ∈ C, orderOf t = 2 → IsComponentOf J (centralizer {t}) := fun _ htC ht =>
    isComponentOf_centralizer_of_no_four_group ha hJ (fun E hEC hE _ => hC2 E hEC hE) htC ht
  by_cases hLg : ∀ g : G, ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥
  · left
    have haC : a ∈ C := mem_centralizer_of_le_centralizer_singleton hJ.1
    have heven : Even (Nat.card C) := by
      have h := orderOf_dvd_natCard (⟨a, haC⟩ : C)
      rw [orderOf_mk, ha] at h
      exact even_iff_two_dvd.mpr h
    exact (involution_component_standard_criterion hJ.2.2 heven hLg).2 hcomp
  · right
    push Not at hLg
    obtain ⟨g, hg⟩ := hLg
    have hrJ : CFSG.pRank 2 J ≤ 1 :=
      pRank_le_one_of_map_conj_le_centralizer (map_conj_le_centralizer_of_commutator_eq_bot hg)
        hr.le
    have hQ : CFSG.IsQuasisimple J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ.2.2
    obtain ⟨-, ⟨z, hz, -⟩, hcen, hquat⟩ := quasisimple_rank_one_unique_central_involution hQ hrJ
    have hzC : (z : G) ∈ C := by
      rw [hC, mem_centralizer_iff]
      intro j hj
      exact congrArg Subtype.val (mem_center_iff.mp (hcen z hz) ⟨j, hj⟩)
    have hz2 : orderOf (z : G) = 2 := by rw [orderOf_coe, hz]
    obtain ⟨r, hr3, hT⟩ := hquat default
    exact ⟨z, hz2, z.2, hzC, hcomp _ hzC hz2, r, hr3, default, hT⟩

end CFSG.LocalAnalysis.ComponentInitial
