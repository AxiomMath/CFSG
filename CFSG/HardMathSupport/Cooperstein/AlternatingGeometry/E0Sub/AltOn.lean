module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm MulAction

theorem range_ofSubtype_eq_fixingSubgroup {N : ℕ} (Ω₁ : Finset (Fin N)) :
    (Perm.ofSubtype : Perm ↥Ω₁ →* Perm (Fin N)).range =
      fixingSubgroup (Perm (Fin N)) ((Ω₁ : Set (Fin N))ᶜ) := by
  ext g
  rw [Perm.mem_range_ofSubtype_iff, mem_fixingSubgroup_compl_iff_movedBy_subset]
  refine ⟨fun h x hx => h (mem_support.2 hx), fun h x hx => h ?_⟩
  simpa using mem_support.1 hx

theorem map_ofSubtype_alternatingGroup_eq_altOn {N : ℕ} (Ω₁ : Finset (Fin N)) :
    (alternatingGroup ↥Ω₁).map (Perm.ofSubtype : Perm ↥Ω₁ →* Perm (Fin N)) = altOn Ω₁ := by
  rw [alternatingGroup.map_ofSubtype, range_ofSubtype_eq_fixingSubgroup, altOn, inf_comm]

@[expose] noncomputable def altOnEquiv {N : ℕ} (Ω₁ : Finset (Fin N)) :
    altOn Ω₁ ≃* alternatingGroup ↥Ω₁ :=
  (MulEquiv.subgroupCongr (map_ofSubtype_alternatingGroup_eq_altOn Ω₁).symm).trans
    ((alternatingGroup ↥Ω₁).equivMapOfInjective _ Perm.ofSubtype_injective).symm

@[simp] theorem coe_altOnEquiv_symm_apply {N : ℕ} (Ω₁ : Finset (Fin N))
    (f : alternatingGroup ↥Ω₁) :
    (((altOnEquiv Ω₁).symm f : altOn Ω₁) : Perm (Fin N)) = Perm.ofSubtype (f : Perm ↥Ω₁) :=
  rfl

theorem card_altOn {N : ℕ} {Ω₁ : Finset (Fin N)} (h : Ω₁.card = 6) :
    Nat.card (altOn Ω₁) = 360 := by
  have : Nontrivial ↥Ω₁ := Fintype.one_lt_card_iff_nontrivial.1 (by simp [h])
  rw [Nat.card_congr (altOnEquiv Ω₁).toEquiv, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_coe, h]
  decide

theorem commutator_altOn {N : ℕ} {Ω₁ : Finset (Fin N)} (h : 5 ≤ Ω₁.card) :
    ⁅altOn Ω₁, altOn Ω₁⁆ = altOn Ω₁ := by
  rw [← map_ofSubtype_alternatingGroup_eq_altOn, ← Subgroup.map_commutator,
    commutator_alternatingGroup_eq_self (by simpa using h)]

theorem isSimpleGroup_altOn {N : ℕ} {Ω₁ : Finset (Fin N)} (h : 5 ≤ Ω₁.card) :
    IsSimpleGroup (altOn Ω₁) :=
  have : IsSimpleGroup (alternatingGroup ↥Ω₁) := alternatingGroup.isSimpleGroup (by simpa using h)
  (altOnEquiv Ω₁).isSimpleGroup

theorem swap_mul_swap_mem_altOn {N : ℕ} {Ω₁ : Finset (Fin N)} {a b c : Fin N}
    (ha : a ∈ Ω₁) (hb : b ∈ Ω₁) (hc : c ∈ Ω₁) (hab : a ≠ b) (hbc : b ≠ c) (_hac : a ≠ c) :
    swap a b * swap b c ∈ altOn Ω₁ := by
  refine Subgroup.mem_inf.2 ⟨?_, (mem_fixingSubgroup_iff _).2 fun x hx => ?_⟩
  · rw [mem_alternatingGroup, map_mul, sign_swap hab, sign_swap hbc]
    rfl
  · have hx' : x ∉ Ω₁ := hx
    have hxa : x ≠ a := fun h => hx' (h ▸ ha)
    have hxb : x ≠ b := fun h => hx' (h ▸ hb)
    have hxc : x ≠ c := fun h => hx' (h ▸ hc)
    rw [Perm.smul_def, Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxc,
      swap_apply_of_ne_of_ne hxa hxb]

theorem altOn_apply_of_not_mem {N : ℕ} {Ω₁ : Finset (Fin N)} {σ : Perm (Fin N)}
    (hσ : σ ∈ altOn Ω₁) {x : Fin N} (hx : x ∉ Ω₁) : σ x = x :=
  (mem_fixingSubgroup_iff _).1 (Subgroup.mem_inf.1 hσ).2 x hx

theorem altOn_apply_mem {N : ℕ} {Ω₁ : Finset (Fin N)} {σ : Perm (Fin N)}
    (hσ : σ ∈ altOn Ω₁) {x : Fin N} (hx : x ∈ Ω₁) : σ x ∈ Ω₁ := by
  by_contra h
  have h1 : σ x = x := σ.injective (altOn_apply_of_not_mem hσ h)
  exact h (by rwa [h1])

theorem le_normalizer_altOn {N : ℕ} {Ω₁ : Finset (Fin N)} {g : Perm (Fin N)}
    (hg : ∀ x, x ∈ Ω₁ ↔ g x ∈ Ω₁) :
    g ∈ Subgroup.normalizer (altOn Ω₁ : Set (Perm (Fin N))) := by
  have key : ∀ g : Perm (Fin N), (∀ x, x ∈ Ω₁ ↔ g x ∈ Ω₁) →
      ∀ n ∈ altOn Ω₁, g * n * g⁻¹ ∈ altOn Ω₁ := by
    intro g hg n hn
    refine Subgroup.mem_inf.2 ⟨?_, (mem_fixingSubgroup_iff _).2 fun x hx => ?_⟩
    · rw [mem_alternatingGroup, map_mul, map_mul, map_inv,
        mem_alternatingGroup.1 (Subgroup.mem_inf.1 hn).1]
      simp
    · have hx' : x ∉ Ω₁ := hx
      have hgx : g⁻¹ x ∉ Ω₁ := fun h => hx' (by simpa using (hg _).1 h)
      rw [Perm.smul_def, Perm.mul_apply, Perm.mul_apply, altOn_apply_of_not_mem hn hgx]
      simp
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  refine ⟨key g hg n, fun h => ?_⟩
  have hg' : ∀ x, x ∈ Ω₁ ↔ g⁻¹ x ∈ Ω₁ := fun x => by simpa using (hg (g⁻¹ x)).symm
  simpa [mul_assoc] using key g⁻¹ hg' _ h

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
