module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped commutatorElement

section Generic

variable {E X : Type*} [Group E] [Group X] {π : E →* X} {F : Type*} [Field F]

theorem pair_eq_one_of_scale_left (hcen : π.ker ≤ Subgroup.center E)
    (hπ : Function.Surjective π) {V V' : Type*} [AddCommGroup V] [Module F V] (ρ : V → X)
    (ρ' : V' → X) (hρ : ∀ v w, ρ (v + w) = ρ v * ρ w)
    (hcomm : ∀ v w, ρ v * ρ' w = ρ' w * ρ v) {α : F} (hα : α ≠ 1) {g : E}
    (hg : ∀ v, π g * ρ v * (π g)⁻¹ = ρ (α • v)) (hg' : ∀ w, π g * ρ' w * (π g)⁻¹ = ρ' w)
    (v : V) (w : V') {a b : E} (ha : π a = ρ v) (hb : π b = ρ' w) : ⁅a, b⁆ = 1 := by
  classical
  let _ := centerCommGroup E
  choose L hL using fun s : F => hπ (ρ (s • v))
  have hcm : ∀ s, Commute (π (L s)) (π b) := fun s => by
    rw [hL, hb]
    exact hcomm _ _
  have hc : ∀ s, ⁅L s, b⁆ ∈ Subgroup.center E := fun s => comm_mem_center_of_commute_map hcen
    (hcm s)
  let f : F → Subgroup.center E := fun s => ⟨⁅L s, b⁆, hc s⟩
  have hf : ∀ s s', f (s + s') = f s * f s' := by
    intro s s'
    apply Subtype.ext
    have hadd : π (L (s + s')) = π (L s * L s') := by
      rw [map_mul, hL, hL, hL, add_smul, hρ]
    change ⁅L (s + s'), b⁆ = ⁅L s, b⁆ * ⁅L s', b⁆
    rw [comm_eq_of_map_eq hcen hadd rfl, comm_mul_left_of_central (hc s')]
    exact Subgroup.mem_center_iff.1 (hc s) _
  have hs : ∀ s, f (α * s) = f s := by
    intro s
    apply Subtype.ext
    change ⁅L (α * s), b⁆ = ⁅L s, b⁆
    refine comm_eq_of_conj hcen g (hcm s) ?_ ?_
    · rw [hL, hL, hg, smul_smul]
    · rw [hb, hg']
  have h1 := eq_one_of_scale f hf hα hs 1
  have h2 : ⁅L 1, b⁆ = 1 := congrArg Subtype.val h1
  have h3 : ⁅a, b⁆ = ⁅L 1, b⁆ :=
    comm_eq_of_map_eq hcen (by rw [ha, hL, one_smul]) rfl
  rw [h3, h2]

theorem pair_eq_one_of_scale_right (hcen : π.ker ≤ Subgroup.center E)
    (hπ : Function.Surjective π) {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] [Module F V']
    (ρ : V → X) (ρ' : V' → X) (hρ' : ∀ v w, ρ' (v + w) = ρ' v * ρ' w)
    (hcomm : ∀ v w, ρ v * ρ' w = ρ' w * ρ v) {β : F} (hβ : β ≠ 1) {g : E}
    (hg : ∀ v, π g * ρ v * (π g)⁻¹ = ρ v) (hg' : ∀ w, π g * ρ' w * (π g)⁻¹ = ρ' (β • w))
    (v : V) (w : V') {a b : E} (ha : π a = ρ v) (hb : π b = ρ' w) : ⁅a, b⁆ = 1 := by
  have h := pair_eq_one_of_scale_left hcen hπ ρ' ρ hρ' (fun w v => (hcomm v w).symm) hβ hg' hg
    w v hb ha
  rw [← commutatorElement_inv, h, inv_one]

theorem pair_eq_one_of_scalar (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : V → X) (hρ : ∀ v w, ρ (v + w) = ρ v * ρ w)
    (hcomm : ∀ v w, ρ v * ρ w = ρ w * ρ v)
    (h5 : ∃ a : F, a ≠ 0 ∧ a + 1 ≠ 0 ∧ a ^ 2 + a + 1 ≠ 0)
    (htor : ∀ a : F, a ≠ 0 → ∃ g : E, ∀ v, π g * ρ v * (π g)⁻¹ = ρ (a • v)) (v w : V) {a b : E}
    (ha : π a = ρ v) (hb : π b = ρ w) : ⁅a, b⁆ = 1 := by
  classical
  let _ := centerCommGroup E
  choose L hL using fun v : V => hπ (ρ v)
  have hc : ∀ u u', ⁅L u, L u'⁆ ∈ Subgroup.center E := fun u u' =>
    comm_mem_center_of_commute_map hcen (by rw [hL, hL]; exact hcomm u u')
  let B : V → V → Subgroup.center E := fun u u' => ⟨⁅L u, L u'⁆, hc u u'⟩
  have hB : ∀ u u', ((B u u' : Subgroup.center E) : E) = ⁅L u, L u'⁆ := fun _ _ => rfl
  have hadd : ∀ u u' : V, π (L (u + u')) = π (L u * L u') := by
    intro u u'
    rw [map_mul, hL, hL, hL, hρ]
  have hcomm' : ∀ u u', Commute (π (L u)) (π (L u')) := fun u u' => by
    rw [hL, hL]
    exact hcomm u u'
  have hadd₁ : ∀ x x' y, B (x + x') y = B x y * B x' y := by
    intro x x' y
    apply Subtype.ext
    rw [Subgroup.coe_mul, hB, hB, hB, comm_eq_of_map_eq hcen (hadd x x') rfl,
      comm_mul_left_of_central (hc x' y)]
    exact Subgroup.mem_center_iff.1 (hc x y) _
  have hadd₂ : ∀ x y y', B x (y + y') = B x y * B x y' := by
    intro x y y'
    apply Subtype.ext
    rw [Subgroup.coe_mul, hB, hB, hB, comm_eq_of_map_eq hcen rfl (hadd y y'),
      comm_mul_right_of_central (hc x y')]
  have hinv : ∀ s : F, s ≠ 0 → ∀ x y, B (s • x) (s • y) = B x y := by
    intro s hs x y
    obtain ⟨g, hg⟩ := htor s hs
    apply Subtype.ext
    rw [hB, hB]
    refine comm_eq_of_conj hcen g (hcomm' x y) ?_ ?_
    · rw [hL, hL, hg]
    · rw [hL, hL, hg]
  have hone := eq_one_of_scalar_invariant (F := F) (V := V) (W := Subgroup.center E) h5 B hadd₁
    hadd₂ hinv v w
  have h1 : ⁅L v, L w⁆ = 1 := congrArg Subtype.val hone
  have h2 : ⁅a, b⁆ = ⁅L v, L w⁆ :=
    comm_eq_of_map_eq hcen (by rw [ha, hL]) (by rw [hb, hL])
  rw [h2, h1]

end Generic

end CFSG.ClassicalInvolution.WeakCT
