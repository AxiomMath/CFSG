module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Equiv Equiv.Perm
open scoped commutatorElement

theorem hom_eq_one_of_perfect_solvable {H K : Type*} [Group H] [Group K] [Group.IsPerfect H]
    [Group.IsSolvable K] (f : H →* K) : f = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Group.IsSolvable f.range := inferInstance
  have hsub : Subsingleton f.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  ext h
  have := Subsingleton.elim (⟨f h, h, rfl⟩ : f.range) 1
  simpa using congrArg Subtype.val this

theorem fixes_of_perfect_of_card_le_four {α : Type*} {H : Subgroup (Perm α)} (hH : ⁅H, H⁆ = H)
    (p : α → Prop) (hp : ∀ h ∈ H, ∀ x, p x ↔ p (h x)) [Finite {x // p x}]
    (hcard : Nat.card {x // p x} ≤ 4) : ∀ h ∈ H, ∀ x, p x → h x = x := by
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  let f : H →* Perm {x // p x} :=
    MonoidHom.mk' (fun h => (h : Perm α).subtypePerm (fun x => (hp h h.2 x).symm)) (by intro a b; ext x; rfl)
  have : Group.IsSolvable (Perm {x // p x}) := Equiv.Perm.isSolvable hcard
  have hf := hom_eq_one_of_perfect_solvable f
  intro h hh x hx
  have := congrArg (fun g : Perm {x // p x} => (g ⟨x, hx⟩ : α)) (DFunLike.congr_fun hf ⟨h, hh⟩)
  simpa [f] using this

theorem fixes_of_commute_three {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α ≤ 10)
    {H : Subgroup (Perm α)} (hH : ⁅H, H⁆ = H) {g : Perm α} (hg : g ^ 3 = 1)
    (hgH : ∀ h ∈ H, Commute g h) : ∀ h ∈ H, ∀ x, g x ≠ x → h x = x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  have hct := cycleType_of_pow_prime_eq_one hg
  have hcardCT : Nat.card g.cycleFactorsFinset ≤ 3 := by
    have h1 : g.cycleType.sum = 3 * Multiset.card g.cycleType := by
      conv_lhs => rw [hct]
      simp [mul_comm]
    have h2 : g.cycleType.sum ≤ 10 := (sum_cycleType_le g).trans hα
    have h3 : Nat.card g.cycleFactorsFinset = Multiset.card g.cycleType := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, cycleType_def, Multiset.card_map]; rfl
    omega
  have hHC : H ≤ Subgroup.centralizer ({g} : Set (Perm α)) := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hgH h hh).symm.eq
  let ρ : H →* Perm g.cycleFactorsFinset :=
    (OnCycleFactors.toPermHom g).comp (Subgroup.inclusion hHC)
  have : Group.IsSolvable (Perm g.cycleFactorsFinset) := Equiv.Perm.isSolvable (by omega)
  have hρ := hom_eq_one_of_perfect_solvable ρ
  intro h hh x hx
  have hc : g.cycleOf x ∈ g.cycleFactorsFinset :=
    cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)
  have hcomm : Commute (g.cycleOf x) h := by
    have h1 : (ρ ⟨h, hh⟩) ⟨g.cycleOf x, hc⟩ = ⟨g.cycleOf x, hc⟩ := by
      rw [hρ]; rfl
    have h2 := congrArg Subtype.val h1
    have h3 : h * g.cycleOf x * h⁻¹ = g.cycleOf x := h2
    exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  have hsupp : (g.cycleOf x).support.card = 3 := by
    have hmem : (g.cycleOf x).support.card ∈ g.cycleType := by
      rw [cycleType_def]
      exact Multiset.mem_map_of_mem _ hc
    exact pow_prime_eq_one_iff.mp hg _ hmem
  have hxc : g.cycleOf x x ≠ x := by rwa [cycleOf_apply_self]
  have hp : ∀ h ∈ H, ∀ y, g.cycleOf x y ≠ y ↔ g.cycleOf x (h y) ≠ h y := by
    intro h hh y
    have hcm : Commute (g.cycleOf x) h := by
      have h1 : (ρ ⟨h, hh⟩) ⟨g.cycleOf x, hc⟩ = ⟨g.cycleOf x, hc⟩ := by
        rw [hρ]; rfl
      have h3 : h * g.cycleOf x * h⁻¹ = g.cycleOf x := congrArg Subtype.val h1
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    have : g.cycleOf x (h y) = h (g.cycleOf x y) := by
      have := hcm.eq
      exact (congrArg (fun f : Perm α => f y) this)
    rw [this]
    exact (h.injective.ne_iff).symm
  have hcard4 : Nat.card {y // g.cycleOf x y ≠ y} ≤ 4 := by
    have : Nat.card {y // g.cycleOf x y ≠ y} = (g.cycleOf x).support.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    omega
  exact fixes_of_perfect_of_card_le_four hH (fun y => g.cycleOf x y ≠ y) hp hcard4 h hh x hxc

theorem card_le_three_of_perfect_centralizer {H Q : Subgroup (Perm (Fin 10))} (hH : ⁅H, H⁆ = H)
    (hH0 : H ≠ ⊥) (hQ : IsPGroup 3 Q) (hQH : ∀ q ∈ Q, ∀ h ∈ H, Commute q h) :
    Nat.card Q ≤ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let pF : Fin 10 → Prop := fun x => ∀ h ∈ H, h x = x
  have hpF : ∀ h ∈ H, ∀ x, pF x ↔ pF (h x) := by
    intro h hh x
    constructor
    · intro hx
      have hhx : h x = x := hx h hh
      rw [hhx]; exact hx
    · intro hx
      have h1 : h⁻¹ (h x) = h x := hx h⁻¹ (H.inv_mem hh)
      have h2 : x = h x := by simpa using h1
      rw [h2]; exact hx
  have hsum : Nat.card {x // pF x} + Nat.card {x // ¬ pF x} = 10 := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl pF)]
    simp
  have hmoved : 5 ≤ Nat.card {x // ¬ pF x} := by
    by_contra hlt
    have hfin : Finite {x // ¬ pF x} := inferInstance
    have key := fixes_of_perfect_of_card_le_four hH (fun x => ¬ pF x)
      (fun h hh x => not_congr (hpF h hh x)) (by omega)
    apply hH0
    rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    refine Equiv.ext fun x => ?_
    by_cases hx : pF x
    · exact hx h hh
    · exact key h hh x hx
  have hF5 : Nat.card {x // pF x} ≤ 5 := by omega
  have hqF : ∀ q ∈ Q, ∀ x, pF x ↔ pF (q x) := by
    intro q hq x
    have hc : ∀ h ∈ H, q (h x) = h (q x) := fun h hh =>
      congrArg (fun f : Perm (Fin 10) => f x) (hQH q hq h hh).eq
    constructor
    · intro hx h hh
      rw [← hc h hh, hx h hh]
    · intro hx h hh
      apply q.injective
      rw [hc h hh, hx h hh]
  let r : Q →* Perm {x // pF x} :=
    MonoidHom.mk' (fun q => (q : Perm (Fin 10)).subtypePerm (fun x => (hqF q q.2 x).symm))
      (by intro a b; ext x; rfl)
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro q hq
    by_contra hq1
    obtain ⟨k, hk⟩ := hQ q
    have hdvd : orderOf q ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hq1 (orderOf_eq_one_iff.mp (by simpa using hj))
    have h3 : 3 ∣ Nat.card (Subgroup.zpowers q) := by
      rw [Nat.card_zpowers, hj]
      exact dvd_pow_self 3 hj0
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers q) 3 h3
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
    have hry : r (y : Q) = 1 := by rw [← hm, map_zpow, hq, one_zpow]
    have hy3 : (y : Q) ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      exact congrArg Subtype.val this
    have hy1 : (y : Q) ≠ 1 := by
      intro h1
      have : y = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hy
      omega
    set g : Perm (Fin 10) := ((y : Q) : Perm (Fin 10)) with hg
    have hg3 : g ^ 3 = 1 := congrArg Subtype.val hy3
    have hg1 : g ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
    obtain ⟨x, hx⟩ : ∃ x, g x ≠ x := by
      by_contra hall
      exact hg1 (Equiv.ext fun x => by_contra fun hne => hall ⟨x, hne⟩)
    have hpx := fixes_of_commute_three (by simp) hH hg3 (fun h hh => hQH g (y : Q).2 h hh) 
    have hxF : pF x := fun h hh => hpx h hh x hx
    have := congrArg (fun f : Perm {x // pF x} => (f ⟨x, hxF⟩ : Fin 10)) hry
    exact hx (by simpa [r, hg] using this)
  have hdvd : Nat.card Q ∣ 120 := by
    have h1 := Subgroup.card_dvd_of_injective r hr
    rw [Nat.card_perm] at h1
    exact h1.trans (by
      have := Nat.factorial_dvd_factorial hF5
      simpa [Nat.factorial] using this)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hQ
  rw [hj] at hdvd ⊢
  by_contra hlt
  have hj2 : 2 ≤ j := by
    by_contra h1
    have h1 := not_le.mp h1
    interval_cases j <;> simp at hlt
  have : 3 ^ 2 ∣ 120 := (Nat.pow_dvd_pow 3 hj2).trans hdvd
  norm_num at this

end CFSG.HardMathSupport.Curtis.UnitaryLevi
