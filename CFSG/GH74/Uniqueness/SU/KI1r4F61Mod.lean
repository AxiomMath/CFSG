module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61Lie

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG.GH74.KGroups CFSG.GH74.Uniqueness.SU.K.R3

theorem StrictFix.of_outer {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a)
    (h : ∀ α : MulAut K, α ^ 2 = 1 → (¬ ∃ g : K, α = MulAut.conj g) →
      ∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4) :
    StrictFix K := by
  intro α hα
  by_cases hin : ∃ g : K, α = MulAut.conj g
  · obtain ⟨g, rfl⟩ := hin
    exact four_group_fixed_of_inner hnab g hα
  · exact h α hα hin

@[expose] def ModE4 {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)) : Prop :=
  ∃ u v : Equiv.Perm (Fin n), u ∈ P ∧ v ∈ P ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u ^ 2 = 1 ∧ v ^ 2 = 1 ∧
    u * v = v * u ∧ g * u = u * g ∧ g * v = v * g

@[expose] def fixedSub (K : Type) [Group K] (α : MulAut K) : Subgroup K where
  carrier := {k | α k = k}
  one_mem' := map_one α
  mul_mem' := fun {a b} ha hb => by
    have ha' : α a = a := ha
    have hb' : α b = b := hb
    show α (a * b) = a * b
    rw [map_mul, ha', hb']
  inv_mem' := fun {a} ha => by
    have ha' : α a = a := ha
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha']

theorem mem_fixedSub {K : Type} [Group K] {α : MulAut K} {k : K} :
    k ∈ fixedSub K α ↔ α k = k := Iff.rfl

theorem eq_one_or_eq_of_mem_zpowers_sq {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hx' : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hx]
  have hk : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2]
    rw [zpow_add, zpow_mul, hx', one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem ModE4.one {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {g : Equiv.Perm (Fin n)}
    (h : ModE4 P g) : ModE4 P 1 := by
  obtain ⟨u, v, hu, hv, hu1, hv1, huv, hu2, hv2, huv', -, -⟩ := h
  exact ⟨u, v, hu, hv, hu1, hv1, huv, hu2, hv2, huv', by rw [one_mul, mul_one],
    by rw [one_mul, mul_one]⟩

theorem ModE4.conj {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {g : Equiv.Perm (Fin n)}
    (h : ModE4 P g) {c : Equiv.Perm (Fin n)} (hc : c ∈ P) : ModE4 P (c * g * c⁻¹) := by
  obtain ⟨u, v, hu, hv, hu1, hv1, huv, hu2, hv2, huv', hgu, hgv⟩ := h
  refine ⟨c * u * c⁻¹, c * v * c⁻¹, P.mul_mem (P.mul_mem hc hu) (P.inv_mem hc),
    P.mul_mem (P.mul_mem hc hv) (P.inv_mem hc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hu1 (by simpa using h1)
  · intro h1
    exact hv1 (by simpa using h1)
  · intro h1
    exact huv (by simpa using h1)
  · rw [conj_pow, hu2]
    group
  · rw [conj_pow, hv2]
    group
  · calc c * u * c⁻¹ * (c * v * c⁻¹) = c * (u * v) * c⁻¹ := by group
      _ = c * (v * u) * c⁻¹ := by rw [huv']
      _ = c * v * c⁻¹ * (c * u * c⁻¹) := by group
  · calc c * g * c⁻¹ * (c * u * c⁻¹) = c * (g * u) * c⁻¹ := by group
      _ = c * (u * g) * c⁻¹ := by rw [hgu]
      _ = c * u * c⁻¹ * (c * g * c⁻¹) := by group
  · calc c * g * c⁻¹ * (c * v * c⁻¹) = c * (g * v) * c⁻¹ := by group
      _ = c * (v * g) * c⁻¹ := by rw [hgv]
      _ = c * v * c⁻¹ * (c * g * c⁻¹) := by group

theorem strictFix_of_model {K : Type} [Group K] [Finite K] {n : ℕ}
    (M : AutModel K (Equiv.Perm (Fin n))) (h : ∀ g ∈ M.A, g ^ 2 = 1 → ModE4 M.P g) :
    StrictFix K := by
  intro α hα
  classical
  obtain ⟨g, hgdef⟩ : ∃ g : Equiv.Perm (Fin n), g = (M.Φ α : Equiv.Perm (Fin n)) := ⟨_, rfl⟩
  have hgA : g ∈ M.A := hgdef ▸ (M.Φ α).2
  have hg2 : g ^ 2 = 1 := by rw [hgdef, ← M.Φ_pow, hα, M.Φ_one]
  have hspec : ∀ x : K, ((M.e (α x) : M.P) : Equiv.Perm (Fin n)) =
      g * (M.e x : Equiv.Perm (Fin n)) * g⁻¹ := fun x => by
    rw [hgdef]
    exact M.spec α x
  have hfix : ∀ x : K, g * (M.e x : Equiv.Perm (Fin n)) = (M.e x : Equiv.Perm (Fin n)) * g →
      α x = x := by
    intro x hx
    apply M.e.injective
    apply Subtype.ext
    rw [hspec x]
    calc g * (M.e x : Equiv.Perm (Fin n)) * g⁻¹ =
          (M.e x : Equiv.Perm (Fin n)) * g * g⁻¹ := by rw [hx]
      _ = (M.e x : Equiv.Perm (Fin n)) := by group
  obtain ⟨u, v, hu, hv, hu1, hv1, huv, hu2, hv2, huv', hgu, hgv⟩ := h g hgA hg2
  obtain ⟨x, hx⟩ := M.e.surjective ⟨u, hu⟩
  obtain ⟨y, hy⟩ := M.e.surjective ⟨v, hv⟩
  have hxu : (M.e x : Equiv.Perm (Fin n)) = u := congrArg Subtype.val hx
  have hyv : (M.e y : Equiv.Perm (Fin n)) = v := congrArg Subtype.val hy
  have hxsq : x ^ 2 = 1 := by
    apply M.e.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hxu, hu2, map_one, Subgroup.coe_one]
  have hysq : y ^ 2 = 1 := by
    apply M.e.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hyv, hv2, map_one, Subgroup.coe_one]
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hu1
    rw [← hxu, map_one, Subgroup.coe_one]
  have hxy : x ≠ y := by
    rintro rfl
    exact huv (by rw [← hxu, ← hyv])
  have hcomm : x * y = y * x := by
    apply M.e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hxu, hyv]
    exact huv'
  have hya : y ∉ zpowers x := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers_sq hxsq hmem with h | h
    · apply hv1
      rw [← hyv, h, map_one, Subgroup.coe_one]
    · exact hxy h.symm
  have hxf : α x = x := hfix x (by rw [hxu]; exact hgu)
  have hyf : α y = y := hfix y (by rw [hyv]; exact hgv)
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := x) (y := y)
    hxsq hysq hx1 hya hcomm
  have hle : zpowers x ⊔ zpowers y ≤ fixedSub K α :=
    sup_le (Subgroup.zpowers_le.2 hxf) (Subgroup.zpowers_le.2 hyf)
  exact ⟨zpowers x ⊔ zpowers y, fun v hv => hle hv, hel, by rw [hcard]; norm_num⟩

end CFSG.GH74.Uniqueness.SU.K.R4
