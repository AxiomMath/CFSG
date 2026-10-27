module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup

section Align

variable {G Mg Mn : Type*} {n : ℕ}

theorem exists_twist_aligned_of_edge (ext : Fin n → Mn → Mg)
    (hinj : ∀ k, Function.Injective (ext k)) {β : Mn → Mn} {κ : Mg → Mg}
    (hβ : ∀ a, β (β a) = a) (hext : ∀ k a, ext k (β a) = κ (ext k a)) (φ : Fin n → Mn → G)
    (hφ : ∀ k, Function.Injective (φ k)) (o : Fin n)
    (hedge : ∀ k l, k ≠ l → ∃ δ : Bool, ∀ a b, ext k a = ext l b →
      φ k a = φ l (if δ then β b else b))
    (htri : ∀ k l, k ≠ o → l ≠ o → k ≠ l → ∃ a b c, ext o a = ext k b ∧ ext o a = ext l c ∧
      κ (ext o a) ≠ ext o a) :
    ∃ ε : Fin n → Bool, ∀ k l a b, ext k a = ext l b →
      φ k (if ε k then β a else a) = φ l (if ε l then β b else b) := by
  classical
  choose δ hδ using hedge
  have hext' : ∀ k (x : Bool) a,
      ext k (if x then β a else a) = if x then κ (ext k a) else ext k a := by
    intro k x a
    cases x
    · rfl
    · exact hext k a
  have htw : ∀ (x y : Bool) a, (if x then β (if y then β a else a) else (if y then β a else a)) =
      if xor x y then β a else a := by
    intro x y a
    cases x <;> cases y <;> simp [hβ]
  have hed : ∀ k l (hkl : k ≠ l) (x : Bool) a b, ext k a = ext l b →
      φ k (if x then β a else a) = φ l (if xor (δ k l hkl) x then β b else b) := by
    intro k l hkl x a b hab
    have h1 : ext k (if x then β a else a) = ext l (if x then β b else b) := by
      rw [hext', hext', hab]
    rw [hδ k l hkl _ _ h1, htw]
  have hcoc : ∀ k l (hko : k ≠ o) (hlo : l ≠ o) (hkl : k ≠ l),
      δ k o hko = xor (δ l o hlo) (δ k l hkl) := by
    intro k l hko hlo hkl
    obtain ⟨a, b, c, hab, hac, hκ⟩ := htri k l hko hlo hkl
    have e1 := hed k o hko false b a hab.symm
    have e2 := hed k l hkl false b c (hab.symm.trans hac)
    have e3 := hed l o hlo (δ k l hkl) c a hac.symm
    simp only [Bool.false_eq_true, ite_false, Bool.xor_false] at e1 e2
    rw [e2] at e1
    rw [e3] at e1
    have e4 := hφ o e1
    by_contra hne
    apply hκ
    have hβa : β a = a := by
      revert e4 hne
      cases δ k o hko <;> cases xor (δ l o hlo) (δ k l hkl) <;> simp
      · exact fun h => h.symm
    rw [← hext, hβa]
  refine ⟨fun k => if h : k = o then false else δ k o h, fun k l a b hab => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rw [hinj k hab]
  by_cases hko : k = o
  · subst hko
    have hlk : l ≠ k := Ne.symm hkl
    have h1 := hed l k hlk (δ l k hlk) b a hab.symm
    simp only [Bool.xor_self, Bool.false_eq_true, ite_false] at h1
    simp only [dite_true, hlk, dite_false, Bool.false_eq_true, ite_false]
    exact h1.symm
  by_cases hlo : l = o
  · subst hlo
    have h1 := hed k l hkl (δ k l hkl) a b hab
    simp only [Bool.xor_self, Bool.false_eq_true, ite_false] at h1
    simp only [hko, dite_false, dite_true, Bool.false_eq_true, ite_false]
    exact h1
  have h1 := hed k l hkl (δ k o hko) a b hab
  have h2 : xor (δ k l hkl) (δ k o hko) = δ l o hlo := by
    rw [hcoc k l hko hlo hkl]
    cases δ k l hkl <;> cases δ l o hlo <;> rfl
  rw [h2] at h1
  simp only [hko, hlo, dite_false]
  exact h1

end Align

section Edge

variable {G Mg Mn M2 : Type*} [Group G] [Group Mg] [Group Mn] [Group M2]

theorem commutator_map_top_eq_of_perfect {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hperf : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤) :
    ⁅(⊤ : Subgroup A).map f, (⊤ : Subgroup A).map f⁆ = (⊤ : Subgroup A).map f := by
  rw [← Subgroup.map_commutator, hperf]

theorem exists_edge_twist_of_overlap [Finite M2] {ek el : Mn →* Mg}
    (hek : Function.Injective ek) (hel : Function.Injective el) {φk φl : Mn →* G}
    (hφk : Function.Injective φk) (hφl : Function.Injective φl) {xk xl : G}
    (hrk : φk.range ≤ centralizer {xk})
    (hrl : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer {xl} → P ≤ φl.range)
    {yk yl : Mn} (hyk : φl yk = xk) (hyl : φk yl = xl)
    (hLa : el.range ≤ centralizer {ek yl})
    (hLb : ∀ P : Subgroup Mg, ⁅P, P⁆ = P → P ≤ centralizer {el yk} → P ≤ ek.range)
    {e2 : M2 →* Mn} (he2 : Function.Injective e2) (hnest : ∀ a, ek a ∈ el.range ↔ a ∈ e2.range)
    (hperf : ⁅(⊤ : Subgroup M2), (⊤ : Subgroup M2)⁆ = ⊤) {β : Mn → Mn} {κ : Mg → Mg}
    (hβk : ∀ a, ek (β a) = κ (ek a)) (hβl : ∀ a, el (β a) = κ (el a)) {β2 : M2 → M2}
    (hβ2 : ∀ x, e2 (β2 x) = β (e2 x)) {F2 : Set M2}
    (hagree : ∀ x ∈ F2, ∀ b, el b = ek (e2 x) → φk (e2 x) = φl b) {t : G}
    (hN3k : ∀ a, φk (β a) = t * φk a * t⁻¹) (hN3l : ∀ b, φl (β b) = t * φl b * t⁻¹)
    (htw : ∀ α : MulAut M2, (∀ x ∈ F2, α x = x) → (∀ x, α (β2 x) = β2 (α x)) →
      α = 1 ∨ ∀ x, α x = β2 x) :
    ∃ δ : Bool, ∀ a b, ek a = el b → φk a = φl (if δ then β b else b) := by
  have hS : (⊤ : Subgroup M2).map (φk.comp e2) ≤ φl.range := by
    refine hrl _ (commutator_map_top_eq_of_perfect _ hperf) ?_
    rintro _ ⟨x, -, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hyl, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply hek
    have hx : ek (e2 x) ∈ el.range := (hnest _).2 ⟨x, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (hLa hx)
    rw [map_mul, map_mul, h1]
  set τ0 : M2 →* φl.range := (φk.comp e2).codRestrict φl.range fun x =>
    hS (Subgroup.mem_map_of_mem _ (Subgroup.mem_top x))
    with hτ0
  set τ : M2 →* Mn := (MonoidHom.ofInjective hφl).symm.toMonoidHom.comp τ0 with hτdef
  have hτ : ∀ x, φl (τ x) = φk (e2 x) := by
    intro x
    have h := (MonoidHom.ofInjective hφl).apply_symm_apply (τ0 x)
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  set σ : M2 →* Mg := ek.comp e2 with hσdef
  have hσinj : Function.Injective σ := hek.comp he2
  have hP : ∀ x, el (τ x) ∈ σ.range := by
    intro x
    have hle : (⊤ : Subgroup M2).map (el.comp τ) ≤ ek.range := by
      refine hLb _ (commutator_map_top_eq_of_perfect _ hperf) ?_
      rintro _ ⟨x', -, rfl⟩
      rw [mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul]
      congr 1
      apply hφl
      rw [map_mul, map_mul, hyk, hτ]
      have hm : φk (e2 x') ∈ φk.range := ⟨_, rfl⟩
      exact mem_centralizer_singleton_iff.1 (hrk hm)
    obtain ⟨a', ha'⟩ := hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_top x))
    have ha'' : ek a' ∈ el.range := ⟨τ x, ha'.symm⟩
    obtain ⟨x', rfl⟩ := (hnest a').1 ha''
    exact ⟨x', ha'⟩
  set α0 : M2 →* M2 := (MonoidHom.ofInjective hσinj).symm.toMonoidHom.comp
    ((el.comp τ).codRestrict σ.range hP) with hα0
  have hα0 : ∀ x, ek (e2 (α0 x)) = el (τ x) := by
    intro x
    have h := (MonoidHom.ofInjective hσinj).apply_symm_apply
      ((el.comp τ).codRestrict σ.range hP x)
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hα0inj : Function.Injective α0 := by
    intro x x' h
    have h1 : el (τ x) = el (τ x') := by rw [← hα0, ← hα0, h]
    have h2 := congrArg φl (hel h1)
    rw [hτ, hτ] at h2
    exact he2 (hφk h2)
  set α : MulAut M2 := MulEquiv.ofBijective α0 (Finite.injective_iff_bijective.1 hα0inj)
    with hαdef
  have hα : ∀ x, ek (e2 (α x)) = el (τ x) := hα0
  have hfix : ∀ x ∈ F2, α x = x := by
    intro x hx
    obtain ⟨b, hb⟩ := (hnest (e2 x)).2 ⟨x, rfl⟩
    have h1 := hagree x hx b hb
    have h2 : τ x = b := hφl (by rw [hτ, h1])
    exact hσinj (by
      change ek (e2 (α x)) = ek (e2 x)
      rw [hα, h2, hb])
  have hcomm : ∀ x, α (β2 x) = β2 (α x) := by
    intro x
    have h1 : τ (β2 x) = β (τ x) := by
      apply hφl
      rw [hτ, hβ2, hN3k, hN3l, hτ]
    apply hσinj
    change ek (e2 (α (β2 x))) = ek (e2 (β2 (α x)))
    rw [hα, h1, hβl, ← hα, hβ2, hβk]
  rcases htw α hfix hcomm with h1 | h1
  · refine ⟨false, fun a b hab => ?_⟩
    have ha : ek a ∈ el.range := ⟨b, hab.symm⟩
    obtain ⟨x, rfl⟩ := (hnest a).1 ha
    have h2 : α x = x := by rw [h1]; rfl
    have h3 : el (τ x) = el b := by rw [← hα, h2, hab]
    rw [← hτ, hel h3]
    rfl
  · refine ⟨true, fun a b hab => ?_⟩
    have ha : ek a ∈ el.range := ⟨b, hab.symm⟩
    obtain ⟨x, rfl⟩ := (hnest a).1 ha
    have h3 : el (τ x) = el (β b) := by rw [← hα, h1, hβ2, hβk, hab, hβl]
    rw [← hτ, hel h3]
    rfl

end Edge

end CFSG.SeitzReduction.SymplecticPilot
