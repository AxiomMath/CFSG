module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.QuasithinUnique.A5.Delta5

open CFSG.QuasithinUnique Equiv

@[expose] def mkSub (s : Finset (Perm (Fin 5))) (h1 : (1 : Perm (Fin 5)) ∈ s)
    (hm : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) (hi : ∀ a ∈ s, a⁻¹ ∈ s) : Subgroup (Perm (Fin 5)) where
  carrier := ↑s
  mul_mem' := fun {a b} ha hb => hm a ha b hb
  one_mem' := h1
  inv_mem' := fun {a} ha => hi a ha

theorem mkSub_card (s : Finset (Perm (Fin 5))) (h1 : (1 : Perm (Fin 5)) ∈ s)
    (hm : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) (hi : ∀ a ∈ s, a⁻¹ ∈ s) :
    Nat.card (mkSub s h1 hm hi) = s.card := by
  have h : ((mkSub s h1 hm hi : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5))) = ↑s := rfl
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

@[expose] def Eset : Finset (Perm (Fin 5)) := {1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3}

theorem Eset_one : (1 : Perm (Fin 5)) ∈ Eset := by decide +kernel

theorem Eset_mul : ∀ a ∈ Eset, ∀ b ∈ Eset, a * b ∈ Eset := by decide +kernel

theorem Eset_inv : ∀ a ∈ Eset, a⁻¹ ∈ Eset := by decide +kernel

@[expose] def Estd : Subgroup (Perm (Fin 5)) := mkSub Eset Eset_one Eset_mul Eset_inv

theorem mem_Estd (σ : Perm (Fin 5)) : σ ∈ Estd ↔ σ ∈ Eset := Iff.rfl

theorem Eset_card : Eset.card = 4 := by decide +kernel

theorem Estd_card : Nat.card Estd = 4 := (mkSub_card _ _ _ _).trans Eset_card

theorem closure_swaps :
    Subgroup.closure ({swap 0 1, swap 2 3} : Set (Perm (Fin 5))) = Estd := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · show swap 0 1 ∈ Eset; decide +kernel
    · show swap 2 3 ∈ Eset; decide +kernel
  · intro σ hσ
    have h : σ ∈ Eset := hσ
    simp only [Eset, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

@[expose] def Dset : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun σ => ∀ x ∈ Eset, σ * x * σ⁻¹ ∈ Eset

theorem Dset_card : Dset.card = 8 := by decide +kernel

theorem Dset_one : (1 : Perm (Fin 5)) ∈ Dset := by decide +kernel

theorem Dset_mul : ∀ a ∈ Dset, ∀ b ∈ Dset, a * b ∈ Dset := by decide +kernel

theorem Dset_inv : ∀ a ∈ Dset, a⁻¹ ∈ Dset := by decide +kernel

@[expose] def Dstd : Subgroup (Perm (Fin 5)) := mkSub Dset Dset_one Dset_mul Dset_inv

theorem mem_Dstd (σ : Perm (Fin 5)) : σ ∈ Dstd ↔ σ ∈ Dset := Iff.rfl

theorem mem_Dset (σ : Perm (Fin 5)) : σ ∈ Dset ↔ ∀ x ∈ Eset, σ * x * σ⁻¹ ∈ Eset := by
  simp [Dset]

theorem Estd_le_Dstd : Estd ≤ Dstd := by
  have : ∀ σ ∈ Eset, σ ∈ Dset := by decide +kernel
  exact fun σ hσ => this σ hσ

theorem Dstd_card : Nat.card Dstd = 8 := (mkSub_card _ _ _ _).trans Dset_card

@[expose] def z0 : Fin 5 → ZMod 2 := ![1, 1, 1, 1, 0]

theorem fixed_Dset : ∀ v : Fin 5 → ZMod 2, isEven v → (∀ σ ∈ Dset, pact σ v = v) →
    v = 0 ∨ v = z0 := by
  decide +kernel

@[expose] def S4std : Subgroup (Perm (Fin 5)) := MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)

theorem mem_S4std (σ : Perm (Fin 5)) : σ ∈ S4std ↔ σ 4 = 4 := by
  simp [S4std, MulAction.mem_stabilizer_iff]

@[expose] def S4set : Finset (Perm (Fin 5)) := Finset.univ.filter fun σ => σ 4 = 4

theorem mem_S4set (σ : Perm (Fin 5)) : σ ∈ S4set ↔ σ 4 = 4 := by simp [S4set]

theorem Dset_le_S4 : ∀ σ ∈ Dset, σ 4 = 4 := by decide +kernel

theorem z0_fixed : ∀ σ : Perm (Fin 5), σ 4 = 4 → pact σ z0 = z0 := by decide +kernel

theorem swap_conj_form : ∀ σ : Perm (Fin 5), σ 4 ≠ 4 → ∃ d ∈ S4set, ∃ s ∈ S4set,
    swap 3 4 = d * σ * s * σ⁻¹ * d := by
  decide +kernel

theorem swap_cases : ∀ i j : Fin 5, i ≠ j →
    swap i j ∈ S4set ∨ ∃ e ∈ S4set, swap i j = e * swap 3 4 * e⁻¹ := by
  decide +kernel

theorem S4_max (X : Subgroup (Perm (Fin 5))) (hX : S4std ≤ X) (σ : Perm (Fin 5)) (hσ : σ ∈ X)
    (h4 : σ 4 ≠ 4) : X = ⊤ := by
  have hS4 : ∀ d ∈ S4set, d ∈ X := fun d hd => hX ((mem_S4std d).mpr ((mem_S4set d).mp hd))
  have h34 : swap 3 4 ∈ X := by
    obtain ⟨d, hd, s, hs, e⟩ := swap_conj_form σ h4
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hS4 d hd) hσ) (hS4 s hs)) (inv_mem hσ)) (hS4 d hd)
  rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
  rintro τ ⟨i, j, hij, rfl⟩
  rcases swap_cases i j hij with h | ⟨e, he, h⟩
  · exact hS4 _ h
  · rw [h]
    exact mul_mem (mul_mem (hS4 e he) h34) (inv_mem (hS4 e he))

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem swaps_conj_fin : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∃ ρ : Perm (Fin 5), ρ * swap a b * ρ⁻¹ = swap 0 1 ∧ ρ * swap c d * ρ⁻¹ = swap 2 3 := by
  decide +kernel

theorem swaps_conj (τ₁ τ₂ : Perm (Fin 5)) (h₁ : τ₁.IsSwap) (h₂ : τ₂.IsSwap)
    (hd : τ₁.Disjoint τ₂) :
    ∃ ρ : Perm (Fin 5), ρ * τ₁ * ρ⁻¹ = swap 0 1 ∧ ρ * τ₂ * ρ⁻¹ = swap 2 3 := by
  obtain ⟨a, b, hab, rfl⟩ := h₁
  obtain ⟨c, d, hcd, rfl⟩ := h₂
  have ha : swap c d a = a :=
    (hd a).resolve_left (by rw [swap_apply_left]; exact hab.symm)
  have hb : swap c d b = b :=
    (hd b).resolve_left (by rw [swap_apply_right]; exact hab)
  have key2 : ∀ x : Fin 5, swap c d x = x → x ≠ c ∧ x ≠ d := by
    intro x hx
    constructor
    · rintro rfl; rw [swap_apply_left] at hx; exact hcd hx.symm
    · rintro rfl; rw [swap_apply_right] at hx; exact hcd hx
  obtain ⟨hac, had⟩ := key2 a ha
  obtain ⟨hbc, hbd⟩ := key2 b hb
  exact swaps_conj_fin a b c d hab hcd hac had hbc hbd

end CFSG.QuasithinUnique.A5.Delta5
