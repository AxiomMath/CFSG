module

public import Mathlib.GroupTheory.PGroup

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.AF

variable {G : Type} [Group G]

theorem exists_conj_of_inv_mul_mem [Finite G] {t u : G} (ht : t * t = 1) (hu : u * u = 1)
    {O : Subgroup G} (hodd : Odd (Nat.card O)) (h : t⁻¹ * u ∈ O) :
    ∃ o ∈ O, u = o * t * o⁻¹ := by
  set n : G := t⁻¹ * u with hn
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hnO : n ∈ O := h
  have hnord : Odd (orderOf n) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hnO)
  have hu' : u = t * n := by rw [hn, hti, ← mul_assoc, ht, one_mul]
  have h1 : t * n * t⁻¹ = n⁻¹ := by
    have h2 : (t * n) * (t * n) = 1 := by rw [← hu']; exact hu
    have h3 : t * n * t = n⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc t * n * t * n = (t * n) * (t * n) := by group
        _ = 1 := h2
    rw [hti]
    exact h3
  obtain ⟨k, hk⟩ := hnord.exists_bit1
  set s : G := n ^ (k + 1) with hs
  have hss : s * s = n := by
    rw [hs, ← pow_add]
    have : k + 1 + (k + 1) = orderOf n + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hsO : s ∈ O := O.pow_mem hnO _
  have h4 : t * s * t⁻¹ = s⁻¹ := by
    rw [hs, ← conj_pow, h1, inv_pow]
  refine ⟨s⁻¹, O.inv_mem hsO, ?_⟩
  have h5 : t * s = s⁻¹ * t := by
    calc t * s = (t * s * t⁻¹) * t := by group
      _ = s⁻¹ * t := by rw [h4]
  have h6 : s * s⁻¹ = 1 := mul_inv_cancel s
  calc u = t * n := hu'
    _ = (t * n * t⁻¹) * t := by group
    _ = n⁻¹ * t := by rw [h1]
    _ = (s * s)⁻¹ * t := by rw [hss]
    _ = s⁻¹ * (s⁻¹ * t) := by group
    _ = s⁻¹ * (t * s) := by rw [h5]
    _ = s⁻¹ * t * s := by group
    _ = s⁻¹ * t * s⁻¹⁻¹ := by rw [inv_inv]

theorem exists_fixed_conj_of_isPGroup [Finite G] {O R : Subgroup G} {t : G} (ht : t * t = 1)
    (hodd : Odd (Nat.card O)) (hR : IsPGroup 2 R)
    (hRn : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O) (hrt : ∀ r ∈ R, t⁻¹ * (r * t * r⁻¹) ∈ O) :
    ∃ o ∈ O, ∀ r ∈ R, r * (o * t * o⁻¹) * r⁻¹ = o * t * o⁻¹ := by
  classical
  let X : Set G := {u | ∃ o ∈ O, u = o * t * o⁻¹}
  have hXR : ∀ r ∈ R, ∀ u ∈ X, r * u * r⁻¹ ∈ X := by
    rintro r hr _ ⟨o, ho, rfl⟩
    have ht' : (r * t * r⁻¹) * (r * t * r⁻¹) = 1 := by
      calc r * t * r⁻¹ * (r * t * r⁻¹) = r * (t * t) * r⁻¹ := by group
        _ = 1 := by rw [ht]; group
    obtain ⟨o₁, ho₁, h₁⟩ := exists_conj_of_inv_mul_mem ht ht' hodd (hrt r hr)
    refine ⟨(r * o * r⁻¹) * o₁, O.mul_mem (hRn r hr o ho) ho₁, ?_⟩
    calc r * (o * t * o⁻¹) * r⁻¹ = (r * o * r⁻¹) * (r * t * r⁻¹) * (r * o * r⁻¹)⁻¹ := by group
      _ = (r * o * r⁻¹) * (o₁ * t * o₁⁻¹) * (r * o * r⁻¹)⁻¹ := by rw [← h₁]
      _ = ((r * o * r⁻¹) * o₁) * t * ((r * o * r⁻¹) * o₁)⁻¹ := by group
  let _ : MulAction O G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp O.subtype)
  have hsmulO : ∀ (o : O) (g : G), o • g = (o : G) * g * (o : G)⁻¹ := fun o g => rfl
  have horb : MulAction.orbit O t = X := by
    ext u
    constructor
    · rintro ⟨o, rfl⟩
      exact ⟨o, o.2, hsmulO o t⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨o, ho⟩, hsmulO ⟨o, ho⟩ t⟩
  have hXodd : Odd (Nat.card X) := by
    rw [← horb, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer O t)]
    exact hodd.of_dvd_nat (Subgroup.index_dvd_card _)
  let _ : MulAction R G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp R.subtype)
  have hsmulR : ∀ (r : R) (g : G), r • g = (r : G) * g * (r : G)⁻¹ := fun r g => rfl
  let S : SubMulAction R G :=
    { carrier := X
      smul_mem' := fun r u hu => by
        rw [hsmulR]
        exact hXR r r.2 u hu }
  have hmod := IsPGroup.card_modEq_card_fixedPoints (G := R) (p := 2) hR S
  have hS : Nat.card S = Nat.card X := rfl
  have hfix : Odd (Nat.card (MulAction.fixedPoints R S)) := by
    rw [hS] at hmod
    have h1 : Nat.card X % 2 = 1 := Nat.odd_iff.mp hXodd
    have h2 : Nat.card (MulAction.fixedPoints R S) % 2 = 1 := by
      unfold Nat.ModEq at hmod
      omega
    exact Nat.odd_iff.mpr h2
  obtain ⟨⟨⟨x, hxX⟩, hxfix⟩⟩ := (Nat.card_pos_iff.mp hfix.pos).1
  obtain ⟨o, ho, rfl⟩ := hxX
  refine ⟨o, ho, fun r hr => ?_⟩
  have h := congrArg Subtype.val (hxfix ⟨r, hr⟩)
  rw [SubMulAction.val_smul, hsmulR] at h
  exact h

end CFSG.ClassicalInvolution.Q3.Q3T8.AF
