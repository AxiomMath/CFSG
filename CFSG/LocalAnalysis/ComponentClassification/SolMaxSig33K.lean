module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33J

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

structure Sol33 (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (n : ℕ) (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) (E : Subgroup X)
    (D : Finset (Fin n)) (y : X) : Prop where
  nonab : ∃ a b : X, a * b ≠ b * a
  kProper : Assembly.KProper Blueprint.Catalog X
  unbal : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥
  notU : ¬ OutcomeLocal.UOutcome X
  pair : Sol78.IsSolomonPair t J n
  le : E ≤ J
  klein : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  card : D.card = 4
  supp : ∀ (x : X) (hx : x ∈ J), x ∈ E → (coreImage θ hx).support ⊆ D
  hy : orderOf y = 2
  hyE : y ∈ centralizer (E : Set X)
  hyK : y ∈ UnbalancedLayer.coreActionKernel J
  hyJ : y ∉ J
  hty : t * y = y * t

theorem four_le_card_support_of_mem_alternatingGroup {m : ℕ} {σ : Perm (Fin m)}
    (hσA : σ ∈ alternatingGroup (Fin m)) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    4 ≤ σ.support.card := by
  classical
  have h2 : 2 ∣ σ.support.card := Perm.two_dvd_card_support (by rw [sq]; exact hσ2)
  have h0 : σ.support.card ≠ 0 := by
    intro h
    exact hσ1 (Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h))
  have h2' : σ.support.card ≠ 2 := by
    intro h
    have hsw := Perm.card_support_eq_two.mp h
    have hs := hsw.sign_eq
    rw [Perm.mem_alternatingGroup] at hσA
    rw [hσA] at hs
    exact absurd hs (by decide)
  omega

namespace Sol33

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem mul_self_of_mem_E {e : X} (he : e ∈ E) : e * e = 1 := by
  rw [← sq]
  exact (card_sq_of_klein S.klein).2 e he

theorem y_mul_self : y * y = 1 := by rw [← sq, ← S.hy, pow_orderOf_eq_one]

theorem comm_E {e₁ e₂ : X} (h₁ : e₁ ∈ E) (h₂ : e₂ ∈ E) : e₁ * e₂ = e₂ * e₁ :=
  congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
    ⟨e₁, h₁⟩ ⟨e₂, h₂⟩)

theorem y_comm {e : X} (he : e ∈ E) : e * y = y * e :=
  mem_centralizer_iff.mp S.hyE e he

theorem y_not_mem_E : y ∉ E := fun h => S.hyJ (S.le h)

theorem elementary : IsElementaryAbelian 2 ↥(E ⊔ zpowers y) :=
  (Sol78.four_sup_zpowers_elementary S.klein S.hy S.hyE S.y_not_mem_E).1

theorem mem_cases {b : X} (hb : b ∈ E ⊔ zpowers y) : ∃ e ∈ E, b = e ∨ b = e * y := by
  have hyN : zpowers y ≤ normalizer (E : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : y * h * y⁻¹ = h := by rw [← S.y_comm hh]; group
      rw [h1]
      exact hh
    · intro hh
      have h1 : y * h * y⁻¹ = h := by
        have h2 : y * (y * h * y⁻¹) * y⁻¹ = y * h * y⁻¹ := by
          rw [show y * h * y⁻¹ = (y * h * y⁻¹) by rfl] at hh
          rw [← S.y_comm hh]
          group
        calc y * h * y⁻¹ = y⁻¹ * (y * (y * h * y⁻¹) * y⁻¹) * y := by group
          _ = y⁻¹ * (y * h * y⁻¹) * y := by rw [h2]
          _ = h := by group
      rw [← h1]
      exact hh
  have h1 : (↑(E ⊔ zpowers y) : Set X) = (E : Set X) * (zpowers y : Set X) :=
    coe_mul_of_right_le_normalizer_left E (zpowers y) hyN
  have hb' : b ∈ (↑(E ⊔ zpowers y) : Set X) := hb
  rw [h1] at hb'
  obtain ⟨e, he, u, hu, hbe⟩ := hb'
  have hbe' : e * u = b := hbe
  refine ⟨e, he, ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers S.y_mul_self hu with h | h
  · left
    rw [← hbe', h, mul_one]
  · right
    rw [← hbe', h]

theorem mul_self_of_mem {b : X} (hb : b ∈ E ⊔ zpowers y) : b * b = 1 := by
  have h1 := S.elementary.exponent_dvd_p
  have h2 : (⟨b, hb⟩ : ↥(E ⊔ zpowers y)) ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := h1
    rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
  have h3 := congrArg Subtype.val h2
  simpa [sq] using h3

theorem comm_of_mem {b₁ b₂ : X} (h₁ : b₁ ∈ E ⊔ zpowers y) (h₂ : b₂ ∈ E ⊔ zpowers y) :
    b₁ * b₂ = b₂ * b₁ :=
  congrArg Subtype.val (S.elementary.toIsMulCommutative.is_comm.comm ⟨b₁, h₁⟩ ⟨b₂, h₂⟩)

theorem mem_normalizer {b : X} (hb : b ∈ E ⊔ zpowers y) : b ∈ normalizer (J : Set X) := by
  have h1 : E ⊔ zpowers y ≤ normalizer (J : Set X) :=
    sup_le (fun e he => le_normalizer (S.le he)) (zpowers_le.mpr S.hyK.1)
  exact h1 hb

theorem t_comm {b : X} (hb : b ∈ E ⊔ zpowers y) : t * b = b * t := by
  have hJt : ∀ x ∈ J, x * t = t * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (S.pair.1.2.1 hx)
  obtain ⟨e, he, h | h⟩ := S.mem_cases hb
  · rw [h]
    exact (hJt e (S.le he)).symm
  · rw [h, ← mul_assoc, ← hJt e (S.le he), mul_assoc, S.hty, mul_assoc]

theorem t_mul_self : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]

theorem support_eq {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    (coreImage θ (S.le he)).support = D := by
  classical
  have hsub := S.supp e (S.le he) he
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [S.card]
  refine four_le_card_support_of_mem_alternatingGroup (coreImage_mem θ (S.le he)) ?_ ?_
  · have h1 : (⟨e, S.le he⟩ : ↥J) * ⟨e, S.le he⟩ = 1 := Subtype.ext (S.mul_self_of_mem_E he)
    have h2 : θ ((⟨e, S.le he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        θ ((⟨e, S.le he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  · intro h
    have h1 : θ ((⟨e, S.le he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := Subtype.ext h
    rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h1
    have h2 : orderOf (⟨⟨e, S.le he⟩, h1⟩ : pPrimeCore 2 ↥J) ∣ Nat.card (pPrimeCore 2 ↥J) :=
      orderOf_dvd_natCard _
    have h3 : orderOf (⟨⟨e, S.le he⟩, h1⟩ : pPrimeCore 2 ↥J) = orderOf e := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    have h4 : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact S.mul_self_of_mem_E he) he1
    rw [h3, h4] at h2
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr h2)

end Sol33

end CFSG.ComponentClassification.SolMax
