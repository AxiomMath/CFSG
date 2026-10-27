module

public import CFSG.LargeExtraspecial.AS35WAlt

public section

namespace CFSG.LargeExtraspecial

open Subgroup Equiv Equiv.Perm CFSG.GH74.GLS.Layer3

namespace AS35W

@[expose] def gA8 : Perm (Fin 8) :=
  swap (pt le_rfl 0) (pt le_rfl 1) * swap (pt le_rfl 2) (pt le_rfl 3)

@[expose] def gB8 : Perm (Fin 8) :=
  swap (pt le_rfl 0) (pt le_rfl 1) * swap (pt le_rfl 4) (pt le_rfl 5)

@[expose] def gC8 : Perm (Fin 8) :=
  swap (pt le_rfl 0) (pt le_rfl 1) * swap (pt le_rfl 6) (pt le_rfl 7)

@[expose] def x8 : Perm (Fin 8) := swap 0 2 * swap 1 3 * (swap 4 6 * swap 5 7)

@[expose] def c8 : Perm (Fin 8) := swap 1 2 * swap 5 6

theorem gA8_mem : gA8 ∈ yB (le_refl 8) := subset_closure (by simp [gA8])

theorem gB8_mem : gB8 ∈ yB (le_refl 8) := subset_closure (by simp [gB8])

theorem gC8_mem : gC8 ∈ yB (le_refl 8) := subset_closure (by simp [gC8])

set_option maxRecDepth 20000 in
theorem sig8 : ∀ i j : Fin 8, (gA8 i = i ↔ gA8 j = j) → (gB8 i = i ↔ gB8 j = j) →
    (gC8 i = i ↔ gC8 j = j) → j = i ∨ j = yPerm le_rfl i := by
  decide

set_option maxRecDepth 20000 in
theorem y8_facts : yPerm (le_refl 8) * yPerm le_rfl = 1 ∧ ∀ i, yPerm (le_refl 8) i ≠ i := by
  decide

set_option maxRecDepth 20000 in
theorem x8_facts : x8 * yPerm le_rfl = yPerm le_rfl * x8 ∧ x8 * gA8 * x8⁻¹ = gA8 ∧
    x8 * gB8 * x8⁻¹ = gB8 * yPerm le_rfl ∧ x8 * gC8 * x8⁻¹ = gC8 * yPerm le_rfl ∧
    c8 * yPerm le_rfl * c8⁻¹ = x8 ∧ x8 ≠ yPerm le_rfl := by
  decide

theorem sign_x8 : sign x8 = 1 := by
  rw [x8, map_mul, map_mul, map_mul, sign_swap (by decide), sign_swap (by decide),
    sign_swap (by decide), sign_swap (by decide)]
  rfl

theorem sign_c8 : sign c8 = 1 := by
  rw [c8, map_mul, sign_swap (by decide), sign_swap (by decide)]
  rfl

theorem yB8_comm {β : Perm (Fin 8)} (hβ : β ∈ yB (le_refl 8)) :
    β * yPerm le_rfl = yPerm le_rfl * β := by
  have hs := yB_commute_swaps (le_refl 8) hβ
  have hy : yPerm (le_refl 8) =
      swap (pt le_rfl 0) (pt le_rfl 1) * swap (pt le_rfl 2) (pt le_rfl 3) *
        (swap (pt le_rfl 4) (pt le_rfl 5) * swap (pt le_rfl 6) (pt le_rfl 7)) := rfl
  rw [hy]
  exact (((hs _ (by simp [ySwaps])).mul_right (hs _ (by simp [ySwaps]))).mul_right
    ((hs _ (by simp [ySwaps])).mul_right (hs _ (by simp [ySwaps])))).eq

theorem conj_y8 {g : Perm (Fin 8)} (hg : g * yPerm le_rfl = yPerm le_rfl * g) :
    g * yPerm le_rfl * g⁻¹ = yPerm le_rfl := by
  rw [hg, mul_inv_cancel_right]

@[expose] def P8 : Subgroup (Perm (Fin 8)) where
  carrier := {g | g * yPerm le_rfl = yPerm le_rfl * g ∧ ∀ β ∈ yB (le_refl 8),
    g * β * g⁻¹ = β ∨ g * β * g⁻¹ = β * yPerm le_rfl}
  one_mem' := ⟨by simp, fun β _ => Or.inl (by simp)⟩
  mul_mem' := by
    rintro g h ⟨hg, hgB⟩ ⟨hh, hhB⟩
    refine ⟨by rw [mul_assoc, hh, ← mul_assoc, hg, mul_assoc], fun β hβ => ?_⟩
    have e : g * h * β * (g * h)⁻¹ = g * (h * β * h⁻¹) * g⁻¹ := by group
    rw [e]
    rcases hhB β hβ with h1 | h1 <;> rw [h1]
    · exact hgB β hβ
    · have e2 : g * (β * yPerm le_rfl) * g⁻¹ = g * β * g⁻¹ * (g * yPerm le_rfl * g⁻¹) := by
        group
      rw [e2, conj_y8 hg]
      rcases hgB β hβ with h2 | h2 <;> rw [h2]
      · exact Or.inr rfl
      · left
        rw [mul_assoc, y8_facts.1, mul_one]
  inv_mem' := by
    rintro g ⟨hg, hgB⟩
    have hg' : g⁻¹ * yPerm le_rfl = yPerm le_rfl * g⁻¹ :=
      (show Commute g (yPerm le_rfl) from hg).inv_left.eq
    refine ⟨hg', fun β hβ => ?_⟩
    have hβ' := conj_mem_yB (le_refl 8) (by norm_num) hg' hβ
    rw [inv_inv] at hβ' ⊢
    have e : g * (g⁻¹ * β * g) * g⁻¹ = β := by group
    rcases hgB _ hβ' with h1 | h1 <;> rw [e] at h1
    · exact Or.inl h1.symm
    · right
      calc g⁻¹ * β * g = g⁻¹ * β * g * (yPerm le_rfl * yPerm le_rfl) := by
            rw [y8_facts.1, mul_one]
        _ = g⁻¹ * β * g * yPerm le_rfl * yPerm le_rfl := by simp only [mul_assoc]
        _ = β * yPerm le_rfl := by rw [← h1]

theorem conj_mem_P8 {c : Perm (Fin 8)} (hc : c * yPerm le_rfl = yPerm le_rfl * c)
    {g : Perm (Fin 8)} (hg : g ∈ P8) : c * g * c⁻¹ ∈ P8 := by
  obtain ⟨hgy, hgB⟩ := hg
  have hcy : Commute c (yPerm le_rfl) := hc
  refine ⟨((hcy.mul_left hgy).mul_left hcy.inv_left).eq, fun β hβ => ?_⟩
  have hc' : c⁻¹ * yPerm le_rfl = yPerm le_rfl * c⁻¹ := hcy.inv_left.eq
  have hβ' := conj_mem_yB (le_refl 8) (by norm_num) hc' hβ
  rw [inv_inv] at hβ'
  have e : c * g * c⁻¹ * β * (c * g * c⁻¹)⁻¹ = c * (g * (c⁻¹ * β * c) * g⁻¹) * c⁻¹ := by group
  rw [e]
  rcases hgB _ hβ' with h1 | h1 <;> rw [h1]
  · left
    group
  · right
    have e2 : c * (c⁻¹ * β * c * yPerm le_rfl) * c⁻¹ = β * (c * yPerm le_rfl * c⁻¹) := by group
    rw [e2, conj_y8 hc]

theorem mul_self_eq_one_of_comm {σ : Perm (Fin 8)} (ha : σ * gA8 = gA8 * σ)
    (hb : σ * gB8 = gB8 * σ) (hc : σ * gC8 = gC8 * σ) : σ * σ = 1 := by
  have h1 : ∀ i (τ : Perm (Fin 8)), σ * τ = τ * σ → (τ i = i ↔ τ (σ i) = σ i) := by
    intro i τ hτ
    have e : τ (σ i) = σ (τ i) := by
      have := congrArg (fun π : Perm (Fin 8) => π i) hτ
      simpa using this.symm
    rw [e]
    exact ⟨fun h => by rw [h], fun h => σ.injective h⟩
  have key : ∀ i, σ i = i ∨ σ i = yPerm le_rfl i := fun i =>
    sig8 i (σ i) (h1 i _ ha) (h1 i _ hb) (h1 i _ hc)
  ext i
  simp only [Perm.coe_mul, Function.comp_apply, Perm.coe_one, id_eq]
  have hyy : yPerm (le_refl 8) (yPerm le_rfl i) = i := by
    rw [← Perm.mul_apply, y8_facts.1, Perm.one_apply]
  rcases key i with h | h
  · rw [h, h]
  · rcases key (yPerm le_rfl i) with h' | h'
    · exact absurd (σ.injective (h.trans h'.symm)).symm (y8_facts.2 i)
    · rw [h, h', hyy]

theorem sq_sq_of_mem_P8 {g : Perm (Fin 8)} (hg : g ∈ P8) : g * g * (g * g) = 1 := by
  obtain ⟨hgy, hgB⟩ := hg
  have hcomm : ∀ β ∈ yB (le_refl 8), g * g * β = β * (g * g) := by
    intro β hβ
    have e : g * g * β * (g * g)⁻¹ = β := by
      have e1 : g * g * β * (g * g)⁻¹ = g * (g * β * g⁻¹) * g⁻¹ := by group
      rw [e1]
      rcases hgB β hβ with h1 | h1 <;> rw [h1]
      · exact h1
      · have e2 : g * (β * yPerm le_rfl) * g⁻¹ = g * β * g⁻¹ * (g * yPerm le_rfl * g⁻¹) := by
          group
        rw [e2, conj_y8 hgy, h1, mul_assoc, y8_facts.1, mul_one]
    calc g * g * β = g * g * β * (g * g)⁻¹ * (g * g) := by group
      _ = β * (g * g) := by rw [e]
  exact mul_self_eq_one_of_comm (hcomm _ gA8_mem) (hcomm _ gB8_mem) (hcomm _ gC8_mem)

theorem x8_mem_P8 : x8 ∈ P8 := by
  obtain ⟨hxy, hxa, hxb, hxc, -, -⟩ := x8_facts
  refine ⟨hxy, fun β hβ => ?_⟩
  induction hβ using closure_induction with
  | mem β hβ =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl | rfl
    · exact Or.inl hxa
    · exact Or.inr hxb
    · exact Or.inr hxc
  | one => exact Or.inl (by simp)
  | mul β₁ β₂ hβ₁ _ ih₁ ih₂ =>
    have e : x8 * (β₁ * β₂) * x8⁻¹ = x8 * β₁ * x8⁻¹ * (x8 * β₂ * x8⁻¹) := by group
    have hc := yB8_comm hβ₁
    have hyy := y8_facts.1
    rw [e]
    rcases ih₁ with h1 | h1 <;> rcases ih₂ with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl rfl
    · exact Or.inr (by rw [mul_assoc])
    · right
      calc β₁ * yPerm le_rfl * β₂ = β₁ * (yPerm le_rfl * β₂) := by rw [mul_assoc]
        _ = β₁ * (β₂ * yPerm le_rfl) := by rw [(yB8_comm ‹_›).symm]
        _ = β₁ * β₂ * yPerm le_rfl := by rw [mul_assoc]
    · left
      calc β₁ * yPerm le_rfl * (β₂ * yPerm le_rfl) = β₁ * (yPerm le_rfl * β₂) * yPerm le_rfl := by
            simp only [mul_assoc]
        _ = β₁ * (β₂ * yPerm le_rfl) * yPerm le_rfl := by rw [(yB8_comm ‹_›).symm]
        _ = β₁ * β₂ * (yPerm le_rfl * yPerm le_rfl) := by simp only [mul_assoc]
        _ = β₁ * β₂ := by rw [hyy, mul_one]
  | inv β hβ ih =>
    have e : x8 * β⁻¹ * x8⁻¹ = (x8 * β * x8⁻¹)⁻¹ := by group
    rw [e]
    rcases ih with h1 | h1 <;> rw [h1]
    · exact Or.inl rfl
    · right
      have hc := yB8_comm (inv_mem hβ)
      have hyi : (yPerm (le_refl 8))⁻¹ = yPerm le_rfl :=
        inv_eq_of_mul_eq_one_right y8_facts.1
      rw [mul_inv_rev, hyi, hc]

theorem false_of_altY8 (hz : W2Data (alternatingGroup (Fin 8)) (altY le_rfl)) : False := by
  set A := alternatingGroup (Fin 8)
  set P : Subgroup A := P8.comap A.subtype
  have hPC : P ≤ centralizer ({altY le_rfl} : Set A) := fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hx.1
  have hPn : ∀ c ∈ centralizer ({altY le_rfl} : Set A), ∀ p ∈ P, c * p * c⁻¹ ∈ P := by
    intro c hc p hp
    exact conj_mem_P8 (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)) hp
  have hP2 : IsPGroup 2 P := fun x => ⟨2, by
    apply Subtype.ext
    apply Subtype.ext
    have h := sq_sq_of_mem_P8 x.2
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [show 2 ^ 2 = 2 + 2 from rfl, pow_add, sq]
    exact h⟩
  obtain ⟨-, -, -, -, hconj, hne⟩ := x8_facts
  have hx8 : x8 ∈ A := mem_alternatingGroup.2 sign_x8
  have hc8 : c8 ∈ A := mem_alternatingGroup.2 sign_c8
  refine hz.false_of_conj_mem hPC hPn hP2 (x := ⟨x8, hx8⟩) x8_mem_P8 ?_ ?_
  · intro h
    exact hne (congrArg Subtype.val h)
  · exact isConj_iff.2 ⟨⟨c8, hc8⟩, Subtype.ext hconj⟩

theorem w2Good_alternating_eight : W2Good (alternatingGroup (Fin 8)) := by
  intro z hz
  exfalso
  rcases alt_inv_cases le_rfl (by norm_num) z hz.orderOf_eq with h | h
  · exact false_of_isConj_altX le_rfl (by norm_num) hz h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hz' := hz.map (MulAut.conj c⁻¹)
    have e : MulAut.conj c⁻¹ z = altY le_rfl := by
      rw [MulAut.conj_apply, ← hc]
      group
    rw [e] at hz'
    exact false_of_altY8 hz'

end AS35W

end CFSG.LargeExtraspecial
