module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.AltCocycle

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm

variable {m n : ℕ}

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem perm_apply_inv_apply {α : Type*} (σ : Perm α) (x : α) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

theorem perm_inv_apply_apply {α : Type*} (σ : Perm α) (x : α) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

theorem inv_apply_of_apply {α : Type*} {σ : Perm α} {a b : α} (h : σ a = b) : σ⁻¹ b = a := by
  rw [Perm.inv_eq_iff_eq, h]

theorem sign_viaEmbedding (ι : Fin m ↪ Fin n) (σ : Perm (Fin m)) :
    sign (viaEmbedding σ ι) = sign σ := by
  classical
  rw [viaEmbedding]
  convert sign_extendDomain σ (Equiv.ofInjective ι.1 ι.2)

@[expose] noncomputable def altLift (ι : Fin m ↪ Fin n) :
    alternatingGroup (Fin m) →* alternatingGroup (Fin n) :=
  ((viaEmbeddingHom ι).comp (alternatingGroup (Fin m)).subtype).codRestrict _ fun σ => by
    rw [mem_alternatingGroup, MonoidHom.comp_apply, viaEmbeddingHom_apply, sign_viaEmbedding]
    exact σ.2

theorem coe_altLift (ι : Fin m ↪ Fin n) (σ : alternatingGroup (Fin m)) :
    (altLift ι σ : Perm (Fin n)) = viaEmbedding (σ : Perm (Fin m)) ι :=
  rfl

theorem altLift_apply_apply (ι : Fin m ↪ Fin n) (σ : alternatingGroup (Fin m)) (i : Fin m) :
    (altLift ι σ : Perm (Fin n)) (ι i) = ι ((σ : Perm (Fin m)) i) :=
  viaEmbedding_apply _ _ _

theorem altLift_apply_of_notMem (ι : Fin m ↪ Fin n) (σ : alternatingGroup (Fin m)) {x : Fin n}
    (hx : x ∉ Set.range ι) : (altLift ι σ : Perm (Fin n)) x = x :=
  viaEmbedding_apply_of_notMem _ _ _ hx

theorem altLift_injective (ι : Fin m ↪ Fin n) : Function.Injective (altLift ι) := by
  intro σ τ h
  apply Subtype.ext
  exact viaEmbeddingHom_injective ι (congrArg Subtype.val h)

theorem altLift_trans {k : ℕ} (ι₁ : Fin k ↪ Fin m) (ι₂ : Fin m ↪ Fin n) :
    altLift (ι₁.trans ι₂) = (altLift ι₂).comp (altLift ι₁) := by
  refine MonoidHom.ext fun σ => Subtype.ext (Equiv.ext fun x => ?_)
  change (altLift (ι₁.trans ι₂) σ : Perm (Fin n)) x = (altLift ι₂ (altLift ι₁ σ) : Perm (Fin n)) x
  by_cases hx : x ∈ Set.range ι₂
  · obtain ⟨j, rfl⟩ := hx
    rw [altLift_apply_apply ι₂]
    by_cases hj : j ∈ Set.range ι₁
    · obtain ⟨i, rfl⟩ := hj
      rw [altLift_apply_apply ι₁]
      exact altLift_apply_apply (ι₁.trans ι₂) σ i
    · rw [altLift_apply_of_notMem ι₁ σ hj]
      refine altLift_apply_of_notMem (ι₁.trans ι₂) σ ?_
      rintro ⟨i, hi⟩
      exact hj ⟨i, ι₂.injective hi⟩
  · rw [altLift_apply_of_notMem ι₂ _ hx]
    refine altLift_apply_of_notMem (ι₁.trans ι₂) σ ?_
    rintro ⟨i, rfl⟩
    exact hx ⟨ι₁ i, rfl⟩

theorem exists_notMem_of_card_lt (s : Finset (Fin n)) (h : s.card < n) : ∃ x, x ∉ s := by
  by_contra hx
  push Not at hx
  have h1 : (Finset.univ : Finset (Fin n)) ⊆ s := fun x _ => hx x
  have h2 := Finset.card_le_card h1
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem exists_range_iff_ne (ι : Fin m ↪ Fin n) (hmn : m + 1 = n) :
    ∃ ω : Fin n, ∀ x, x ∈ Set.range ι ↔ x ≠ ω := by
  classical
  have hcard : (Finset.univ.map ι).card = m := by simp
  obtain ⟨ω, hω⟩ := exists_notMem_of_card_lt (Finset.univ.map ι) (by omega)
  refine ⟨ω, fun x => ⟨?_, fun hx => ?_⟩⟩
  · rintro ⟨i, rfl⟩ rfl
    exact hω (Finset.mem_map_of_mem ι (Finset.mem_univ i))
  · by_contra hx'
    have hsub : Finset.univ.map ι ⊆ (Finset.univ.erase ω).erase x := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hy
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      refine ⟨?_, ?_⟩
      · rintro h
        exact hx' ⟨i, h⟩
      · rintro h
        exact hω (h ▸ hy)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp [hx]), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, hcard] at h1
    omega

theorem exists_altLift_eq (ι : Fin m ↪ Fin n) {ω : Fin n} (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω)
    (g : alternatingGroup (Fin n)) (hg : (g : Perm (Fin n)) ω = ω) :
    ∃ σ : alternatingGroup (Fin m), altLift ι σ = g := by
  have hmem : ∀ i, (g : Perm (Fin n)) (ι i) ∈ Set.range ι := fun i => by
    rw [hι]
    intro h
    have h' : (g : Perm (Fin n)) (ι i) = (g : Perm (Fin n)) ω := by rw [h, hg]
    exact (hι (ι i)).1 ⟨i, rfl⟩ ((g : Perm (Fin n)).injective h')
  choose f hf using hmem
  have hfinj : Function.Injective f := fun i j h => by
    have h1 : (g : Perm (Fin n)) (ι i) = (g : Perm (Fin n)) (ι j) := by rw [← hf i, ← hf j, h]
    exact ι.injective ((g : Perm (Fin n)).injective h1)
  set σ₀ : Perm (Fin m) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj) with hσ₀
  have hσ₀g : viaEmbedding σ₀ ι = (g : Perm (Fin n)) := by
    ext x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [viaEmbedding_apply, hσ₀, Equiv.ofBijective_apply, hf]
    · rw [viaEmbedding_apply_of_notMem _ _ _ hx]
      have hxω : x = ω := by
        by_contra h
        exact hx ((hι x).2 h)
      rw [hxω, hg]
  have hσA : σ₀ ∈ alternatingGroup (Fin m) := by
    rw [mem_alternatingGroup, ← sign_viaEmbedding ι, hσ₀g]
    exact g.2
  exact ⟨⟨σ₀, hσA⟩, Subtype.ext hσ₀g⟩

theorem swap_mul_swap_apply_left {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) : (swap a b * swap b c) a = b := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hac, swap_apply_left]

theorem swap_mul_swap_apply_mid {α : Type*} [DecidableEq α] {a b c : α} (hac : a ≠ c)
    (hbc : b ≠ c) : (swap a b * swap b c) b = c := by
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]

theorem swap_mul_swap_apply_right {α : Type*} [DecidableEq α] (a b c : α) :
    (swap a b * swap b c) c = a := by
  rw [Perm.mul_apply, swap_apply_right, swap_apply_right]

theorem swap_mul_swap_mem (α : Type*) [Fintype α] [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hbc : b ≠ c) : swap a b * swap b c ∈ alternatingGroup α := by
  rw [mem_alternatingGroup, map_mul, sign_swap hab, sign_swap hbc]
  decide

theorem exists_alt_apply_eq (hn : 3 ≤ n) (a b : Fin n) :
    ∃ g : alternatingGroup (Fin n), (g : Perm (Fin n)) a = b := by
  by_cases hab : a = b
  · exact ⟨1, hab⟩
  obtain ⟨c, hc⟩ := exists_notMem_of_card_lt ({a, b} : Finset (Fin n))
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨⟨swap a b * swap b c, swap_mul_swap_mem _ hab (Ne.symm hc.2)⟩, ?_⟩
  exact swap_mul_swap_apply_left hab (Ne.symm hc.1)

theorem exists_alt_apply_eq_apply_eq (hn : 5 ≤ n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : alternatingGroup (Fin n), (g : Perm (Fin n)) a = c ∧ (g : Perm (Fin n)) b = d := by
  obtain ⟨g₁, hg₁⟩ := exists_alt_apply_eq (by omega) a c
  have hb : (g₁ : Perm (Fin n)) b ≠ c := fun h =>
    hab ((g₁ : Perm (Fin n)).injective (hg₁.trans h.symm))
  obtain ⟨g₂, hg₂A, hg₂c, hg₂b⟩ := exists_alt_fix_apply_eq hn hb (Ne.symm hcd)
  refine ⟨⟨g₂, hg₂A⟩ * g₁, ?_, ?_⟩
  · change g₂ ((g₁ : Perm (Fin n)) a) = c
    rw [hg₁, hg₂c]
  · exact hg₂b

theorem eq_top_of_isThreeCycle_mem (hn : 5 ≤ n) (S : Subgroup (alternatingGroup (Fin n)))
    (hS : ∀ g s, s ∈ S → g * s * g⁻¹ ∈ S) {t : alternatingGroup (Fin n)}
    (ht : (t : Perm (Fin n)).IsThreeCycle) (htS : t ∈ S) : S = ⊤ := by
  have h3 : ∀ u : alternatingGroup (Fin n), (u : Perm (Fin n)).IsThreeCycle → u ∈ S := by
    intro u hu
    have hcard : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
    obtain ⟨c, hc⟩ := isConj_iff.1 (alternatingGroup.isThreeCycle_isConj hcard ht hu)
    rw [← hc]
    exact hS c t htS
  have hle : Subgroup.closure {σ : Perm (Fin n) | σ.IsThreeCycle} ≤
      S.map (alternatingGroup (Fin n)).subtype := by
    rw [Subgroup.closure_le]
    intro σ hσ
    exact ⟨⟨σ, IsThreeCycle.mem_alternatingGroup hσ⟩, h3 _ hσ, rfl⟩
  rw [closure_three_cycles_eq_alternating] at hle
  rw [eq_top_iff]
  intro g _
  obtain ⟨s, hs, hsg⟩ := hle g.2
  rw [← Subtype.ext hsg]
  exact hs

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
