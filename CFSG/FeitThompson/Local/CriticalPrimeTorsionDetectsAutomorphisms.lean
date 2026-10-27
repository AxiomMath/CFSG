module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Local.CentralFrattiniPowerHomomorphism
import CFSG.FeitThompson.Local.PointwiseStabilizerSelfCentralizingPGroup
import CFSG.FeitThompson.Local.PrimePowerHomTorsionDetectsAutomorphisms

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {P : Type*} [Group P]

theorem centralizer_eq_map_center_iff_centralizer_le (C : Subgroup P) :
    Subgroup.centralizer (C : Set P) = (Subgroup.center C).map C.subtype ↔
      Subgroup.centralizer (C : Set P) ≤ C := by
  rw [map_center_subtype_eq_inf_centralizer]
  refine ⟨fun h => h ▸ inf_le_left, fun h => le_antisymm (le_inf h le_rfl) inf_le_right⟩

theorem mem_fixingSubgroup_pow_eq_one_iff {C : Subgroup P} {a : MulAut P} :
    a ∈ fixingSubgroup (MulAut P) {x : P | x ∈ C ∧ x ^ p = 1} ↔
      ∀ x ∈ C, x ^ p = 1 → a x = x := by
  simp [mem_fixingSubgroup_iff, MulAut.smul_def, and_imp]

theorem apply_eq_self_of_mem_of_pow_eq_one [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (C : Subgroup P) [C.Characteristic]
    (hΦ : frattini C ≤ Subgroup.center C) {a : MulAut P}
    (ha : ∀ x ∈ C, x ^ p = 1 → a x = x) {n : ℕ} (hn : Nat.Coprime n p) (han : a ^ n = 1) :
    ∀ c ∈ C, a c = c := by
  set a' : MulAut C := MulAut.characteristic C a with ha'def
  have han' : a' ^ n = 1 := by rw [ha'def, ← map_pow, han, map_one]
  have hfix' : ∀ h : C, h ^ p = 1 → a' h = h := by
    intro h hh
    have hcoe : (h : P) ^ p = 1 := by rw [← Subgroup.coe_pow, hh, Subgroup.coe_one]
    refine Subtype.ext ?_
    rw [ha'def, MulAut.characteristic_apply_apply_coe]
    exact ha _ h.2 hcoe
  have h1 : a' = 1 :=
    eq_one_of_isPGroup_of_coprime_pow_eq_one (hP.to_subgroup C)
      (mul_pow_of_frattini_le_center_of_isPGroup hp hodd (hP.to_subgroup C) hΦ) hfix' hn han'
  intro c hc
  have h2 : a' ⟨c, hc⟩ = ⟨c, hc⟩ := by rw [h1]; rfl
  simpa [ha'def, MulAut.characteristic_apply_apply_coe] using
    congrArg (fun x : C => (x : P)) h2

theorem isPGroup_fixingSubgroup_pow_eq_one_of_critical [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (C : Subgroup P) [C.Characteristic]
    (hΦ : frattini C ≤ Subgroup.center C)
    (hCP : Subgroup.centralizer (C : Set P) = (Subgroup.center C).map C.subtype) :
    IsPGroup p (fixingSubgroup (MulAut P) {x : P | x ∈ C ∧ x ^ p = 1}) := by
  have := Fact.mk hp
  have hle : Subgroup.centralizer (C : Set P) ≤ C :=
    (centralizer_eq_map_center_iff_centralizer_le C).mp hCP
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hp.primeFactors]
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hqp, hqdvd, -⟩ := hq
  simp only [Finset.mem_singleton]
  by_contra hne
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨a, hao⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  have haq : (a : MulAut P) ^ q = 1 := by
    rw [← Subgroup.coe_pow, ← hao, pow_orderOf_eq_one, Subgroup.coe_one]
  have hfix : ∀ x ∈ C, x ^ p = 1 → (a : MulAut P) x = x :=
    mem_fixingSubgroup_pow_eq_one_iff.mp a.2
  have hmem : (a : MulAut P) ∈ fixingSubgroup (MulAut P) (C : Set P) :=
    mem_fixingSubgroup_mulAut_iff.mpr
      (apply_eq_self_of_mem_of_pow_eq_one hp hodd hP C hΦ hfix
        ((Nat.coprime_primes hqp hp).mpr hne) haq)
  obtain ⟨k, hk⟩ :=
    (IsPGroup.iff_orderOf.mp (isPGroup_fixingSubgroup_mulAut hp hP C hle))
      ⟨(a : MulAut P), hmem⟩
  have h1 : orderOf (a : MulAut P) = p ^ k :=
    (Subgroup.orderOf_coe
      (⟨(a : MulAut P), hmem⟩ : fixingSubgroup (MulAut P) (C : Set P))).trans hk
  have hqk : q = p ^ k := by rw [← hao, ← Subgroup.orderOf_coe a]; exact h1
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero] at hqk; exact hqp.one_lt.ne' hqk
  · exact hne ((Nat.prime_dvd_prime_iff_eq hp hqp).mp (hqk ▸ dvd_pow_self p hkpos.ne')).symm

theorem exists_natCard_fixingSubgroup_pow_eq_one_eq_pow [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (C : Subgroup P) [C.Characteristic]
    (hΦ : frattini C ≤ Subgroup.center C)
    (hCP : Subgroup.centralizer (C : Set P) = (Subgroup.center C).map C.subtype) :
    ∃ n : ℕ, Nat.card (fixingSubgroup (MulAut P) {x : P | x ∈ C ∧ x ^ p = 1}) = p ^ n := by
  have := Fact.mk hp
  exact IsPGroup.iff_card.mp
    (isPGroup_fixingSubgroup_pow_eq_one_of_critical hp hodd hP C hΦ hCP)

end

end CFSG.FeitThompson
