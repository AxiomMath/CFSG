module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalCores

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem fitting_characteristic :
    (fittingSubgroup G).Characteristic ∧ (fittingSubgroup G).Normal ∧
      ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → N ≤ fittingSubgroup G :=
  ⟨fittingSubgroup_characteristic, fittingSubgroup_normal, fun _ hN hnil => le_sSup ⟨hN, hnil⟩⟩

theorem pCore_commute_of_mem_primeFactors :
    Pairwise fun p q : (Nat.card G).primeFactors =>
      ∀ x y : G, x ∈ pCore (p : ℕ) G → y ∈ pCore (q : ℕ) G → Commute x y := by
  intro p q hpq x y hx hy
  have hne : (p : ℕ) ≠ q := fun h => hpq (Subtype.ext h)
  have hcomm := (distinct_prime_cores_commute (G := G) (Nat.prime_of_mem_primeFactors p.2)
    (Nat.prime_of_mem_primeFactors q.2) hne).2
  have hmem : ⁅x, y⁆ ∈ ⁅pCore (p : ℕ) G, pCore (q : ℕ) G⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem fittingSubgroup_eq_iSup_pCore [Finite G] :
    fittingSubgroup G = ⨆ p : (Nat.card G).primeFactors, pCore (p : ℕ) G := by
  rw [fitting_eq_sup_pCore]
  apply le_antisymm
  · exact iSup_le fun p => le_iSup_of_le p.1 le_rfl
  · exact iSup_le fun p => le_iSup_of_le ⟨p, Finset.mem_attach _ _⟩ le_rfl

theorem fitting_product_prime_cores [Finite G] :
    ∃ e : ((p : (Nat.card G).primeFactors) → pCore (p : ℕ) G) ≃* fittingSubgroup G,
      ∀ (p : (Nat.card G).primeFactors) (x : (q : (Nat.card G).primeFactors) → pCore (q : ℕ) G),
        (∀ q, q ≠ p → x q = 1) → (e x : G) = x p := by
  classical
  let H : (Nat.card G).primeFactors → Subgroup G := fun p => pCore (p : ℕ) G
  have hcomm : Pairwise fun p q => ∀ x y : G, x ∈ H p → y ∈ H q → Commute x y :=
    pCore_commute_of_mem_primeFactors
  have : ∀ p, Fintype (H p) := fun p => Fintype.ofFinite _
  have hcoprime : Pairwise fun p q => Nat.Coprime (Fintype.card (H p)) (Fintype.card (H q)) := by
    intro p q hpq
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact IsPGroup.coprime_card_of_ne _ _ (fun h => hpq (Subtype.ext h)) _ _ pCore_isPGroup
      pCore_isPGroup
  have hind : iSupIndep H := Subgroup.independent_of_coprime_order hcomm hcoprime
  let ϕ := Subgroup.noncommPiCoprod hcomm
  have hrange : ϕ.range = fittingSubgroup G := by
    rw [Subgroup.noncommPiCoprod_range, fittingSubgroup_eq_iSup_pCore]
  have hmem : ∀ x, ϕ x ∈ fittingSubgroup G := fun x => hrange ▸ ⟨x, rfl⟩
  let ϕ' := ϕ.codRestrict (fittingSubgroup G) hmem
  have hinj : Function.Injective ϕ' := fun x y h =>
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hind (congrArg Subtype.val h)
  have hsurj : Function.Surjective ϕ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  refine ⟨MulEquiv.ofBijective ϕ' ⟨hinj, hsurj⟩, fun p x hx => ?_⟩
  have hx' : x = Pi.mulSingle p (x p) := by
    funext q
    by_cases hq : q = p
    · subst hq
      simp
    · rw [hx q hq, Pi.mulSingle_eq_of_ne hq]
  change ϕ x = x p
  rw [hx']
  simp only [ϕ, Subgroup.noncommPiCoprod_mulSingle, Pi.mulSingle_eq_same]

theorem fitting_nilpotent [Finite G] :
    Group.IsNilpotent (fittingSubgroup G) ∧ (fittingSubgroup G).Normal ∧
      (∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → N ≤ fittingSubgroup G) ∧
      ∀ M : Subgroup G, M.Normal → Group.IsNilpotent M →
        (∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → N ≤ M) → M = fittingSubgroup G :=
  ⟨fittingSubgroup_nilpotent, fittingSubgroup_normal, fitting_characteristic.2.2,
    fun _ hM hMnil hmax => le_antisymm (fitting_characteristic.2.2 _ hM hMnil)
      (hmax _ fittingSubgroup_normal fittingSubgroup_nilpotent)⟩

end CFSG.LocalCores
