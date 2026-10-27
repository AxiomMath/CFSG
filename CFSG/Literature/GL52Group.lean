module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Rank
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.kerRepresentation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.Literature.GL52

open CFSG

variable {G : Type*} [Group G]

theorem card_mul_le_card_sup [Finite G] {H K : Subgroup G} (h : H ⊓ K = ⊥) :
    Nat.card H * Nat.card K ≤ Nat.card ↥(H ⊔ K) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨p.1 * p.2, mul_mem (le_sup_left (a := H) p.1.2) (le_sup_right (a := H) p.2.2)⟩)
    fun p q hpq => ?_
  have e : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
  have h1 : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
  have hm : (q.1 : G)⁻¹ * p.1 ∈ H ⊓ K :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem q.1.2) p.1.2, h1 ▸ mul_mem q.2.2 (inv_mem p.2.2)⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hm
  have h2 : (p.2 : G) = q.2 := by
    rw [← hm] at e
    exact mul_left_cancel e
  exact Prod.ext (Subtype.ext hm.symm) (Subtype.ext h2)

theorem sup_eq_of_card [Finite G] {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L)
    (h : H ⊓ K = ⊥) (hc : Nat.card L ≤ Nat.card H * Nat.card K) : H ⊔ K = L :=
  Subgroup.eq_of_le_of_card_ge (sup_le hH hK) (hc.trans (card_mul_le_card_sup h))

theorem card_isConj_mul_card_centralizer [Finite G] (x : G) :
    Nat.card {y : G // IsConj x y} * Nat.card (Subgroup.centralizer {x}) = Nat.card G := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, mul_comm]
  have h1 := (MulAction.stabilizer (ConjAct G) x).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have h2 : Nat.card {y : G // IsConj x y} = (MulAction.orbit (ConjAct G) x).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [isConj_comm]
      exact ConjAct.mem_orbit_conjAct.symm)
  rw [h2]
  exact h1

theorem isConj_of_card_le [Finite G] (x : G) (S : G → Prop) (hx : S x)
    (hS : ∀ g y, S y → S (g * y * g⁻¹))
    (hc : Nat.card {y : G // S y} ≤ Nat.card {y : G // IsConj x y}) (y : G) (hy : S y) :
    IsConj x y := by
  classical
  have hsub : ∀ z, IsConj x z → S z := by
    intro z hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 hz
    exact hS c x hx
  have : Fintype G := Fintype.ofFinite G
  have e1 := Nat.card_eq_fintype_card (α := {y : G // S y})
  have e2 := Nat.card_eq_fintype_card (α := {y : G // IsConj x y})
  rw [e1, e2, Fintype.card_subtype, Fintype.card_subtype] at hc
  have hle : (Finset.univ.filter fun z => IsConj x z) ⊆ Finset.univ.filter S := by
    intro z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsub z
  have heq := Finset.eq_of_subset_of_card_le hle hc
  have : y ∈ Finset.univ.filter S := by simp [hy]
  rw [← heq] at this
  simpa using this

section Sylow

variable [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem card_sylow_of_factorization (h : (Nat.card G).factorization p = 1) (P : Sylow p G) :
    Nat.card P = p := by
  rw [P.card_eq_multiplicity, h, pow_one]

@[expose] noncomputable def zpowersSylow (h : (Nat.card G).factorization p = 1) (g : G)
    (hg : orderOf g = p) : Sylow p G :=
  Sylow.ofCard (Subgroup.zpowers g) (by rw [Nat.card_zpowers, hg, h, pow_one])

theorem orderOf_eq_of_mem_sylow (h : (Nat.card G).factorization p = 1) (P : Sylow p G)
    {x : G} (hx : x ∈ P) (hx1 : x ≠ 1) : orderOf x = p := by
  have hd : orderOf x ∣ p := by
    have := Subgroup.orderOf_dvd_natCard (P : Subgroup G) hx
    rwa [card_sylow_of_factorization h P] at this
  rcases (Nat.dvd_prime hp.out).1 hd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.1 h1) hx1
  · exact h1

theorem zpowersSylow_eq (h : (Nat.card G).factorization p = 1) (P : Sylow p G) {x : G}
    (hx : x ∈ P) (hx1 : x ≠ 1) :
    zpowersSylow h x (orderOf_eq_of_mem_sylow h P hx hx1) = P := by
  apply Sylow.ext
  rw [zpowersSylow, Sylow.coe_ofCard]
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx) ?_
  rw [card_sylow_of_factorization h P, Nat.card_zpowers, orderOf_eq_of_mem_sylow h P hx hx1]

theorem card_orderOf_eq_prime (h : (Nat.card G).factorization p = 1) :
    Nat.card {g : G // orderOf g = p} = (p - 1) * Nat.card (Sylow p G) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (Sylow p G) := Fintype.ofFinite _
  let e : {g : G // orderOf g = p} ≃ Σ P : Sylow p G, {x : G // x ∈ P ∧ x ≠ 1} :=
    { toFun := fun g => ⟨zpowersSylow h g.1 g.2, ⟨g.1, by
          change (g : G) ∈ ((zpowersSylow h g.1 g.2 : Sylow p G) : Subgroup G)
          rw [zpowersSylow, Sylow.coe_ofCard]; exact Subgroup.mem_zpowers _, by
          intro h1
          have h2 := g.2
          rw [h1, orderOf_one] at h2
          exact hp.out.one_lt.ne h2⟩⟩
      invFun := fun x => ⟨x.2.1, orderOf_eq_of_mem_sylow h x.1 x.2.2.1 x.2.2.2⟩
      left_inv := fun g => rfl
      right_inv := by
        rintro ⟨P, x, hx, hx1⟩
        exact Sigma.subtype_ext (zpowersSylow_eq h P hx hx1) rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  have hfib : ∀ P : Sylow p G, Nat.card {x : G // x ∈ P ∧ x ≠ 1} = p - 1 := by
    intro P
    have e2 : {x : G // x ∈ P ∧ x ≠ 1} ≃ {y : (P : Subgroup G) // ¬ y = 1} :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h1 => x.2.2 (congrArg Subtype.val h1)⟩
        invFun := fun y => ⟨y.1, y.1.2, fun h1 => y.2 (Subtype.ext h1)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    have : Fintype (P : Subgroup G) := Fintype.ofFinite _
    rw [Nat.card_congr e2, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, card_sylow_of_factorization h P]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  rw [Nat.card_eq_fintype_card]

theorem card_normalizer_mul_card_sylow (P : Sylow p G) :
    Nat.card (Subgroup.normalizer (P : Set G)) * Nat.card (Sylow p G) = Nat.card G := by
  rw [P.card_eq_index_normalizer]
  exact (Subgroup.normalizer (P : Set G)).card_mul_index

end Sylow

theorem eq_zpowers_of_card_prime [Finite G] {q : ℕ} (hq : q.Prime) {R : Subgroup G}
    (hR : Nat.card R = q) {x : G} (hx : x ∈ R) (hx1 : x ≠ 1) : R = Subgroup.zpowers x := by
  have hd : orderOf x ∣ q := hR ▸ Subgroup.orderOf_dvd_natCard R hx
  have ho : orderOf x = q := by
    rcases (Nat.dvd_prime hq).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hx1
    · exact h1
  refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx) ?_).symm
  rw [hR, Nat.card_zpowers, ho]

end CFSG.Literature.GL52
