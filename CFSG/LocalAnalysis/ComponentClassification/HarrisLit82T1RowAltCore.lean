module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltComm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltPerm
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup Equiv Equiv.Perm Equiv.Perm.OnCycleFactors CFSG.OddStandard.AltNoHe
open scoped commutatorElement MatrixGroups

section Core

variable {α : Type*} [Fintype α] [DecidableEq α] {G : Type*} [Group G] {ε : G →* Perm α} {t : G}

theorem quotP_eq_one_of_odd (hinj : Function.Injective ε)
    (hsurj : ∀ p ∈ alternatingGroup α, ∃ x, ε x = p) (ht2 : ε t * ε t = 1)
    {L : Subgroup (centralizer ({t} : Set G))} (hL : L.IsSubnormal)
    (hD : ∀ w ∈ jointKer ε t, w ∈ L → ∀ x ∈ L, ⁅w, x⁆ = 1) {x : centralizer ({t} : Set G)}
    (hxL : x ∈ L) (hodd : Odd (orderOf x)) : quotP ε t x = 1 := by
  by_cases h3 : 3 ≤ (ε t).cycleFactorsFinset.card
  · refine quotP_eq_one_of_forall_commute hinj hsurj ht2 h3 ?_
    obtain ⟨r, hr⟩ := exists_iterate_commutatorElement_mem hL hxL
    refine commute_of_iterate_commutatorElement_eq_one (N := jointKer ε t)
      (fun n hn => jointKer_normal.conj_mem n hn x) (fun n hn => jointKer_mul_self hinj ht2 hn)
      hodd (r := r + 1) fun n hn => ?_
    rw [Function.iterate_succ_apply']
    exact hD _ (iterate_commutatorElement_mem_of_normal jointKer_normal x hn r) (hr n) x hxL
  · exact quotP_eq_one_of_card_le_two (by omega) hodd

omit [Fintype α] [DecidableEq α] in
theorem exists_apply_ne (ht1 : ε t ≠ 1) : ∃ a, ε t a ≠ a := by
  by_contra h
  push Not at h
  exact ht1 (Equiv.ext h)

theorem exists_odd_pow {M : Type*} [Monoid M] {x : M} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Odd (orderOf (x ^ 2 ^ a)) := by
  obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd hx.orderOf_pos.ne'
  refine ⟨a, hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)⟩
  rw [← pow_mul, ← hxm, pow_orderOf_eq_one]

theorem false_of_perfect [Finite G] (hinj : Function.Injective ε)
    (hsurj : ∀ p ∈ alternatingGroup α, ∃ x, ε x = p) (ht1 : ε t ≠ 1) (ht2 : ε t * ε t = 1)
    {L : Subgroup (centralizer ({t} : Set G))} (hL : L.IsSubnormal) (hLp : Group.IsPerfect ↥L)
    {u : centralizer ({t} : Set G)} (hu : (u : G) = t) (huL : u ∈ L)
    (hD : ∀ w ∈ jointKer ε t, w ∈ L → ∀ x ∈ L, ⁅w, x⁆ = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : ∀ x ∈ L, quotP ε t x = 1 := by
    let f := (quotP ε t).comp L.subtype
    have h2 : IsPGroup 2 f.range := by
      rintro ⟨_, ⟨x, rfl⟩⟩
      obtain ⟨a, ha⟩ := exists_odd_pow (isOfFinOrder_of_finite x)
      refine ⟨a, Subtype.ext ?_⟩
      have hodd : Odd (orderOf (((x ^ 2 ^ a : ↥L)) : centralizer ({t} : Set G))) := by
        rwa [Subgroup.orderOf_coe]
      have h1 := quotP_eq_one_of_odd hinj hsurj ht2 hL hD (x ^ 2 ^ a).2 hodd
      simpa [f] using h1
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    have hsub : Subsingleton f.range := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isNilpotent (G := f.range) h2.isNilpotent
    intro x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩ : f.range) 1)
  set H := (fixingSubgroup (Perm α) ((ε t).support : Set α)).comap
    (ε.comp (centralizer ({t} : Set G)).subtype) with hH
  have hLH : L ≤ H := by
    rw [← L.commutator_eq_self, Subgroup.commutator_le]
    intro x hx y hy
    rw [hH, Subgroup.mem_comap, mem_fixingSubgroup_iff]
    intro a ha
    exact commutatorElement_apply_eq_self ht2 (hP x hx) (hP y hy) (mem_support.mp ha)
  obtain ⟨a, ha⟩ := exists_apply_ne ht1
  have h := (mem_fixingSubgroup_iff _).mp (hLH huL) a (mem_support.mpr ha)
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hu, Perm.smul_def] at h
  exact ha h

theorem exists_slTwoThree_pair :
    ∃ g q : SL(2, ZMod 3), g ^ 3 = 1 ∧ ⁅q, g⁆ ^ 2 = -1 ∧ ⁅q, g ^ 2⁆ ^ 2 = -1 :=
  ⟨⟨!![1, 1; 0, 1], by decide⟩, ⟨!![0, 2; 1, 0], by decide⟩, by decide, by decide, by decide⟩

theorem eq_one_of_odd_of_mul_self {M : Type*} [Monoid M] {w : M} (hodd : Odd (orderOf w))
    (h : w * w = 1) : w = 1 := by
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

end Core

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
