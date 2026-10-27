module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCyc

open Equiv Equiv.Perm Subgroup
open scoped Nat commutatorElement

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem zpow_zpow_apply (c : Perm α) (a b : ℤ) (x : α) :
    (c ^ a) ((c ^ b) x) = (c ^ (a + b)) x := by
  rw [zpow_add, Perm.mul_apply]

theorem exists_zpow_of_commute {g c : Perm α} (hc : c.IsCycle) (hgc : Commute g c) :
    ∃ i : ℤ, ∀ x ∈ c.support, g x = (c ^ i) x := by
  obtain ⟨a, ha⟩ := hc.nonempty_support
  have hga : g a ∈ c.support := (mem_support_iff_of_commute hgc a).mpr ha
  obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp hga)
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨j, rfl⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp hx)
  have h1 : g ((c ^ j) a) = (c ^ j) (g a) := by
    have := congrArg (fun π : Perm α => π a) (hgc.zpow_right j).eq
    simpa only [Perm.mul_apply] using this
  rw [h1, ← hi, zpow_zpow_apply, zpow_zpow_apply, add_comm]

theorem fix_of_commute_of_mul_self {g c : Perm α} (hc : c.IsCycle) (hodd : Odd c.support.card)
    (hgc : Commute g c) (hg : g * g = 1) : ∀ x ∈ c.support, g x = x := by
  obtain ⟨i, hi⟩ := exists_zpow_of_commute hc hgc
  have h2 : c ^ (2 * i) = 1 := by
    ext x
    rw [Perm.one_apply]
    by_cases hx : x ∈ c.support
    · have hgx : g x ∈ c.support := (mem_support_iff_of_commute hgc x).mpr hx
      have h := congrArg (fun π : Perm α => π x) hg
      simp only [Perm.mul_apply, Perm.one_apply] at h
      rw [hi _ hgx, hi x hx, zpow_zpow_apply] at h
      rwa [two_mul]
    · exact zpow_apply_eq_self_of_apply_eq_self (notMem_support.mp hx) _
  have hdvd : (c.support.card : ℤ) ∣ 2 * i := by
    rw [← hc.orderOf]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2
  have hcop : IsCoprime (c.support.card : ℤ) 2 := by
    obtain ⟨m, hm⟩ := hodd
    refine ⟨1, -(m : ℤ), ?_⟩
    rw [hm]
    push_cast
    ring
  have hdvd' : (orderOf c : ℤ) ∣ i := by
    rw [hc.orderOf]
    exact hcop.dvd_of_dvd_mul_left hdvd
  intro x hx
  rw [hi x hx, orderOf_dvd_iff_zpow_eq_one.mp hdvd', Perm.one_apply]

theorem fix_of_perfect {c : Perm α} (hc : c.IsCycle) {I : Subgroup (Perm α)} (hI : ⁅I, I⁆ = I)
    (hIc : I ≤ centralizer ({c} : Set (Perm α))) : ∀ g ∈ I, ∀ x ∈ c.support, g x = x := by
  have hpow : ∀ g ∈ I, ∃ i : ℤ, (∀ x ∈ c.support, g x = (c ^ i) x) ∧
      ∀ x ∈ c.support, g⁻¹ x = (c ^ (-i)) x := by
    intro g hg
    obtain ⟨i, hi⟩ := exists_zpow_of_commute hc (mem_centralizer_singleton_iff.mp (hIc hg))
    refine ⟨i, hi, fun x hx => ?_⟩
    rw [Perm.inv_eq_iff_eq, hi _ (zpow_apply_mem_support.mpr hx), zpow_zpow_apply,
      add_neg_cancel, zpow_zero, Perm.one_apply]
  let W : Subgroup (Perm α) :=
    { carrier := {g | ∀ x ∈ c.support, g x = x}
      one_mem' := fun _ _ => rfl
      mul_mem' := fun {g h} hg hh x hx => by rw [Perm.mul_apply, hh x hx, hg x hx]
      inv_mem' := fun {g} hg x hx => by rw [Perm.inv_eq_iff_eq, hg x hx] }
  have hW : I ≤ W := by
    rw [← hI, Subgroup.commutator_le]
    intro g hg h hh x hx
    obtain ⟨i, hi, hi'⟩ := hpow g hg
    obtain ⟨j, hj, hj'⟩ := hpow h hh
    rw [commutatorElement_def]
    simp only [Perm.mul_apply]
    have m1 : (c ^ (-j)) x ∈ c.support := zpow_apply_mem_support.mpr hx
    have m2 : (c ^ (-i)) ((c ^ (-j)) x) ∈ c.support := zpow_apply_mem_support.mpr m1
    have m3 : (c ^ j) ((c ^ (-i)) ((c ^ (-j)) x)) ∈ c.support :=
      zpow_apply_mem_support.mpr m2
    rw [hj' x hx, hi' _ m1, hj _ m2, hi _ m3, zpow_zpow_apply, zpow_zpow_apply, zpow_zpow_apply]
    have : ∀ k : ℤ, k = 0 → (c ^ k) x = x := fun k hk => by
      rw [hk, zpow_zero, Perm.one_apply]
    exact this _ (by ring)
  exact fun g hg => hW hg

theorem mem_zpowers_of_commute {g c : Perm α} (hc : c.IsCycle) (hgc : Commute g c)
    (hg : ∀ x, x ∉ c.support → g x = x) : g ∈ zpowers c := by
  obtain ⟨i, hi⟩ := exists_zpow_of_commute hc hgc
  refine mem_zpowers_iff.mpr ⟨i, ?_⟩
  ext x
  by_cases hx : x ∈ c.support
  · exact (hi x hx).symm
  · rw [hg x hx, zpow_apply_eq_self_of_apply_eq_self (notMem_support.mp hx)]

theorem support_subset_of_invariant {c : Perm α} (hc : c.IsCycle) {B : Finset α}
    (hB : ∀ x ∈ B, c x ∈ B) {a : α} (ha : a ∈ c.support) (haB : a ∈ B) : c.support ⊆ B := by
  have hpow : ∀ n : ℕ, (c ^ n) a ∈ B := by
    intro n
    induction n with
    | zero => simpa using haB
    | succ n ih => rw [pow_succ', Perm.mul_apply]; exact hB _ ih
  intro x hx
  obtain ⟨i, -, rfl⟩ := hc.exists_pow_eq (mem_support.mp ha) (mem_support.mp hx)
  exact hpow i

theorem maps_or_disjoint {c g : Perm α} (hc : c.IsCycle) (hcomm : Commute (g * c * g⁻¹) c) :
    (∀ x ∈ c.support, g x ∈ c.support) ∨ ∀ x ∈ c.support, g x ∉ c.support := by
  have hsupp : (g * c * g⁻¹).support = c.support.map g.toEmbedding := support_conj
  have hmem : ∀ x ∈ c.support, g x ∈ (g * c * g⁻¹).support := fun x hx => by
    rw [hsupp]
    exact Finset.mem_map_of_mem _ hx
  by_cases h : ∃ a ∈ c.support, a ∈ (g * c * g⁻¹).support
  · left
    obtain ⟨a, ha, haτ⟩ := h
    have hsub := support_subset_of_invariant hc (B := (g * c * g⁻¹).support)
      (fun x hx => (mem_support_iff_of_commute hcomm.symm x).mpr hx) ha haτ
    have hcard : (g * c * g⁻¹).support.card = c.support.card := by rw [hsupp, Finset.card_map]
    have heq : c.support = (g * c * g⁻¹).support :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
    intro x hx
    rw [heq]
    exact hmem x hx
  · right
    intro x hx hgx
    exact h ⟨g x, hgx, hmem x hx⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCyc
