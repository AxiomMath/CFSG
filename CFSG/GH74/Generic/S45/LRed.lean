module

public import CFSG.GH74.Generic.S45.LAltLift

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Subgroup CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

theorem exists_induced_quotient {K : Type} [Group K] (hKp : Group.IsPerfect K) (y : MulAut K)
    (hy : orderOf y = 2) :
    ∃ yb : MulAut (K ⧸ Subgroup.center K),
      (∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k)) ∧ yb ≠ 1 ∧ yb * yb = 1 := by
  have : Group.IsPerfect K := hKp
  refine ⟨centerQuotientHom K y, fun k => onCenterQuotient_apply_mk y k, ?_, ?_⟩
  · intro h
    have h2 : y = 1 := onCenterQuotient_eq_one_imp y h
    rw [h2, orderOf_one] at hy
    omega
  · have hyy : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy, pow_two] at this
      exact this
    rw [← map_mul, hyy, map_one]

theorem not_inner_of_not_inner {K : Type} [Group K] (y : MulAut K)
    (yb : MulAut (K ⧸ Subgroup.center K))
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    (hni : ∀ s : K ⧸ Subgroup.center K, yb ≠ MulAut.conj s) :
    ∀ k : K, y ≠ MulAut.conj k := by
  intro k hk
  apply hni (QuotientGroup.mk k)
  refine MulEquiv.ext fun a => ?_
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective a
  rw [hyb, hk]
  rfl

theorem not_four_dvd_of_perfect_fixed {K : Type} [Group K] (y : MulAut K)
    (hno4 : ∀ m : K, y m = m → ¬ 4 ∣ orderOf m) (yb : MulAut (K ⧸ Subgroup.center K))
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    (X : Subgroup (K ⧸ Subgroup.center K)) (hX : ⁅X, X⁆ = X) (hXfix : ∀ x ∈ X, yb x = x) :
    ∀ x ∈ X, ¬ 4 ∣ orderOf x := by
  intro x hx h4
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
  obtain ⟨D, -, hDsurj, hDfix⟩ := exists_fixed_perfect_lift y (QuotientGroup.mk' (Subgroup.center K))
    hker X (by rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
               exact le_top) hX (by
      intro k hk
      show (QuotientGroup.mk (y k) : K ⧸ Subgroup.center K) = QuotientGroup.mk k
      rw [← hyb k]
      exact hXfix _ hk)
  obtain ⟨k, hkD, rfl⟩ := hDsurj x hx
  have hdvd := orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center K)) k
  exact hno4 k (hDfix k hkD) (dvd_trans h4 hdvd)

theorem eq_conj_of_induced_eq_conj {K : Type} [Group K] (hKp : Group.IsPerfect K) (y : MulAut K)
    (yb : MulAut (K ⧸ Subgroup.center K))
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k)) (k₀ : K)
    (h : yb = MulAut.conj (QuotientGroup.mk k₀)) : y = MulAut.conj k₀ := by
  have : Group.IsPerfect K := hKp
  have h1 : centerQuotientHom K y = yb := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    exact (onCenterQuotient_apply_mk y k).trans (hyb k).symm
  have h2 : centerQuotientHom K (MulAut.conj k₀) = MulAut.conj (QuotientGroup.mk k₀) :=
    CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj k₀
  apply centerQuotientHom_injective K
  rw [h1, h2, h]

theorem card_dvd_of_map_le {K G : Type*} [Group K] [Group G] {L : Subgroup K} (π : K →* G)
    (hπ : Function.Injective (π.comp L.subtype)) (H : Subgroup G) (h : ∀ l ∈ L, π l ∈ H) :
    Nat.card ↥L ∣ Nat.card ↥H := by
  have hle : L.map π ≤ H := by
    rintro _ ⟨l, hl, rfl⟩
    exact h l hl
  let e : ↥L ≃* ↥(L.map π) :=
    MulEquiv.ofBijective (π.subgroupMap L)
      ⟨fun a b hab => hπ (by
        have h1 := Subtype.ext_iff.1 hab
        exact h1), π.subgroupMap_surjective L⟩
  rw [Nat.card_congr e.toEquiv]
  exact Subgroup.card_dvd_of_le hle

end CFSG.GH74.Generic.S45.LAlt
