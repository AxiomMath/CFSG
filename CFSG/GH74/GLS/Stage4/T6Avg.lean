module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup

theorem t6_avg_aux {M ι : Type*} [CommGroup M] [Group ι] [Fintype ι] (φ : ι → M →* M)
    (hφ : ∀ h h' x, φ (h * h') x = φ h (φ h' x)) (S : Subgroup M)
    (hS : ∀ h b, (φ h b)⁻¹ * b ∈ S) (b : M) :
    ∃ c : M, (∀ h, φ h c = c) ∧ ∃ d ∈ S, c * d = b ^ Fintype.card ι := by
  refine ⟨∏ h, φ h b, fun h => ?_, ∏ h, (φ h b)⁻¹ * b, Subgroup.prod_mem _ fun h _ => hS h b, ?_⟩
  · rw [map_prod]
    simp_rw [← hφ]
    exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
  · rw [← Finset.prod_mul_distrib]
    simp

theorem t6_avg {G : Type} [Group G] [Finite G] {A H₁ : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hHA : ∀ h ∈ H₁, ∀ x ∈ A, h * x * h⁻¹ ∈ A)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H₁)) :
    ∀ a ∈ A, ∃ c ∈ A, ∃ d ∈ Subgroup.closure {y : G | ∃ h ∈ H₁, ∃ x ∈ A, y = h * x * h⁻¹ * x⁻¹},
      (∀ h ∈ H₁, h * c * h⁻¹ = c) ∧ a = c * d := by
  classical
  intro a ha
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y => Subtype.ext (hAab x x.2 y y.2) }
  let _ : Fintype H₁ := Fintype.ofFinite H₁
  let φ : H₁ → A →* A := fun h =>
    { toFun := fun x => ⟨h * x * h⁻¹, hHA h h.2 x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change (h : G) * (x * y) * (h : G)⁻¹ = ((h : G) * x * (h : G)⁻¹) * ((h : G) * y * (h : G)⁻¹)
        group) }
  have hφ : ∀ h h' x, φ (h * h') x = φ h (φ h' x) := fun h h' x => Subtype.ext (by
    change ((h * h' : H₁) : G) * x * ((h * h' : H₁) : G)⁻¹ =
      (h : G) * ((h' : G) * x * (h' : G)⁻¹) * (h : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)
  let S : Subgroup A :=
    (Subgroup.closure {y : G | ∃ h ∈ H₁, ∃ x ∈ A, y = h * x * h⁻¹ * x⁻¹}).subgroupOf A
  have hS : ∀ h b, (φ h b)⁻¹ * b ∈ S := fun h b => by
    rw [Subgroup.mem_subgroupOf]
    apply Subgroup.subset_closure
    refine ⟨h, h.2, (b : G)⁻¹, A.inv_mem b.2, ?_⟩
    change ((h : G) * (b : G) * (h : G)⁻¹)⁻¹ * b = _
    group
  obtain ⟨b, hb⟩ := (Nat.Coprime.pow_left_bijective (n := Nat.card H₁) hcop).2 ⟨a, ha⟩
  obtain ⟨c, hc, d, hd, hcd⟩ := t6_avg_aux φ hφ S hS b
  refine ⟨c, c.2, d, hd, fun h hh => ?_, ?_⟩
  · have := congrArg Subtype.val (hc ⟨h, hh⟩)
    exact this
  · have h1 : ((b ^ Fintype.card H₁ : A) : G) = a := by
      rw [← Nat.card_eq_fintype_card]
      exact congrArg Subtype.val hb
    rw [← h1, ← hcd]
    rfl

theorem t6_sylow_of_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hP : IsPGroup p ↥P) (hN : ¬ p ∣ P.relIndex (Subgroup.normalizer (P : Set G))) : ¬ p ∣ P.index := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hG : Nat.card P * P.index = Nat.card G := P.card_mul_index
  have h1 : p ^ (n + 1) ∣ Nat.card G := by
    rw [← hG, hn, pow_succ]
    exact mul_dvd_mul_left _ hdvd
  have h2 := Sylow.prime_pow_dvd_card_normalizer h1 hn
  have hle : P ≤ normalizer (P : Set G) := Subgroup.le_normalizer
  have h3 := Subgroup.relIndex_mul_card P (normalizer (P : Set G))
  rw [inf_eq_left.mpr hle, hn] at h3
  rw [← h3, pow_succ, mul_comm (P.relIndex _)] at h2
  exact hN (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos n) h2)

end CFSG.GH74.GLS.Stage4.Rest.T6
