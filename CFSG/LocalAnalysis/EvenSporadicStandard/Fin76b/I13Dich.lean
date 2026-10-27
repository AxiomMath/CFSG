module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Subgroup

set_option maxRecDepth 100000 in
theorem perm_five_central (s : Perm (Fin 5))
    (hs : ∀ a ∈ alternatingGroup (Fin 5), s * a = a * s) : s = 1 := by
  have h3 : ∀ s : Perm (Fin 5),
      s * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * s →
      s * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * s →
      s * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * s →
      s * (swap 0 1 * swap 1 3) = (swap 0 1 * swap 1 3) * s → s = 1 := by
    decide
  have hmem : ∀ a b : Fin 5, ∀ c : Fin 5, a ≠ b → b ≠ c → a ≠ c →
      swap a b * swap b c ∈ alternatingGroup (Fin 5) := by
    intro a b c hab hbc hac
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hbc]
    decide
  exact h3 s (hs _ (hmem 0 1 2 (by decide) (by decide) (by decide)))
    (hs _ (hmem 1 2 3 (by decide) (by decide) (by decide)))
    (hs _ (hmem 2 3 4 (by decide) (by decide) (by decide)))
    (hs _ (hmem 0 1 3 (by decide) (by decide) (by decide)))

theorem dichotomy_S5 (H : Subgroup (Perm (Fin 5) × Perm (Fin 5)))
    (hsw : ∀ a b, (a, b) ∈ H → (b, a) ∈ H)
    (hdg : ∀ s ∈ alternatingGroup (Fin 5), (s, s) ∈ H)
    (hodd : ∀ s, (s, s) ∈ H → s ∈ alternatingGroup (Fin 5)) :
    (∀ a b, (a, b) ∈ H ↔ a ∈ alternatingGroup (Fin 5) ∧ b = a) ∨
    (∀ a b, (a, b) ∈ H ↔ a ∈ alternatingGroup (Fin 5) ∧ b ∈ alternatingGroup (Fin 5)) := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  set A := alternatingGroup (Fin 5) with hA
  let N : Subgroup (Perm (Fin 5)) := H.comap (MonoidHom.inl (Perm (Fin 5)) (Perm (Fin 5)))
  have hN : ∀ a, a ∈ N ↔ (a, 1) ∈ H := fun a => Iff.rfl
  have hNconj : ∀ a ∈ N, ∀ g ∈ A, g * a * g⁻¹ ∈ N := by
    intro a ha g hg
    rw [hN] at ha ⊢
    have := H.mul_mem (H.mul_mem (hdg g hg) ha) (H.inv_mem (hdg g hg))
    simpa [Prod.mk_mul_mk, Prod.inv_mk] using this
  have hnormA : ∀ g ∈ A, ∀ a : Perm (Fin 5), a * g * a⁻¹ ∈ A := by
    intro g hg a
    exact Subgroup.Normal.conj_mem (inferInstance : (alternatingGroup (Fin 5)).Normal) g hg a
  have hnormal : ((N ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    exact ⟨hNconj k hk.1 g g.2, (g * ⟨k, hk.2⟩ * g⁻¹).2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ A).subgroupOf A) with h1 | h1
  ·
    left
    have hNA : ∀ a ∈ N, a ∈ A → a = 1 := by
      intro a ha haA
      have : (⟨a, haA⟩ : A) ∈ (N ⊓ A).subgroupOf A := mem_subgroupOf.2 ⟨ha, haA⟩
      rw [h1, mem_bot] at this
      exact congrArg Subtype.val this
    have hN1 : ∀ a ∈ N, a = 1 := by
      intro a ha
      refine perm_five_central a fun g hg => ?_
      have hx1 : a * (g * a⁻¹ * g⁻¹) ∈ N := mul_mem ha (hNconj a⁻¹ (inv_mem ha) g hg)
      have hx2 : a * (g * a⁻¹ * g⁻¹) ∈ A := by
        have := mul_mem (hnormA g hg a⁻¹⁻¹) (inv_mem hg)
        simpa [mul_assoc] using this
      have hx := hNA _ hx1 hx2
      have : a * g = g * a := by
        calc a * g = (a * (g * a⁻¹ * g⁻¹)) * (g * a) := by group
          _ = g * a := by rw [hx, one_mul]
      exact this
    intro a b
    constructor
    · intro hab
      have hbA : ∀ g ∈ A, b * g * b⁻¹ = a * g * a⁻¹ := by
        intro g hg
        have h2 := H.mul_mem (H.mul_mem hab (hdg g hg)) (H.inv_mem hab)
        have h3 := hdg _ (hnormA g hg a)
        have h4 := H.mul_mem h2 (H.inv_mem h3)
        have h5 := hsw _ _ h4
        have h6 : b * g * b⁻¹ * (a * g * a⁻¹)⁻¹ = 1 :=
          hN1 _ ((hN _).2 (by simpa [Prod.mk_mul_mk, Prod.inv_mk] using h5))
        exact mul_inv_eq_one.1 h6
      have hba : b = a := by
        have : a⁻¹ * b = 1 := by
          refine perm_five_central _ fun g hg => ?_
          have := hbA g hg
          calc a⁻¹ * b * g = a⁻¹ * (b * g * b⁻¹) * b := by group
            _ = a⁻¹ * (a * g * a⁻¹) * b := by rw [this]
            _ = g * (a⁻¹ * b) := by group
        calc b = a * (a⁻¹ * b) := by group
          _ = a := by rw [this, mul_one]
      subst hba
      exact ⟨hodd _ hab, rfl⟩
    · rintro ⟨ha, rfl⟩
      exact hdg _ ha
  ·
    right
    have hAN : ∀ a ∈ A, (a, 1) ∈ H := by
      intro a ha
      have : (⟨a, ha⟩ : A) ∈ (N ⊓ A).subgroupOf A := by rw [h1]; exact mem_top _
      exact ((mem_subgroupOf.1 this).1 : a ∈ N)
    have hAN' : ∀ a ∈ A, (1, a) ∈ H := fun a ha => hsw _ _ (hAN a ha)
    have hodd2 : ∀ u v, (u, v) ∈ H → u ∈ A := by
      intro u v huv
      by_contra hu
      have hu' : Perm.sign u = -1 := by
        rcases Int.units_eq_one_or (Perm.sign u) with h | h
        · exact absurd (Perm.mem_alternatingGroup.2 h) hu
        · exact h
      by_cases hv : v ∈ A
      · have h1 : (u, 1) ∈ H := by
          have := H.mul_mem huv (H.inv_mem (hAN' v hv))
          simpa using this
        have h2 : (u, u) ∈ H := by
          have := H.mul_mem h1 (hsw _ _ h1)
          simpa using this
        exact hu (hodd _ h2)
      · have hv' : Perm.sign v = -1 := by
          rcases Int.units_eq_one_or (Perm.sign v) with h | h
          · exact absurd (Perm.mem_alternatingGroup.2 h) hv
          · exact h
        have hw : v⁻¹ * u ∈ A := by
          rw [Perm.mem_alternatingGroup, map_mul, map_inv, hu', hv']
          decide
        have h2 : (u, u) ∈ H := by
          have := H.mul_mem huv (hAN' _ hw)
          simpa using this
        exact hu (hodd _ h2)
    intro a b
    constructor
    · intro hab
      exact ⟨hodd2 a b hab, hodd2 b a (hsw _ _ hab)⟩
    · rintro ⟨ha, hb⟩
      have := H.mul_mem (hAN a ha) (hAN' b hb)
      simpa using this

theorem dichotomy {Γ : Type*} [Group Γ] (π : Γ →* Perm (Fin 5)) (H : Subgroup (Γ × Γ))
    (hK : ∀ a b : Γ, π a = 1 → π b = 1 → (a, b) ∈ H)
    (hsw : ∀ a b : Γ, (a, b) ∈ H → (b, a) ∈ H)
    (hdg : ∀ s ∈ alternatingGroup (Fin 5), ∃ b : Γ, π b = s ∧ (b, b) ∈ H)
    (hodd : ∀ a b : Γ, (a, b) ∈ H → π a = π b → π a ∈ alternatingGroup (Fin 5)) :
    (∀ a b : Γ, (a, b) ∈ H ↔ π a ∈ alternatingGroup (Fin 5) ∧ π b = π a) ∨
    (∀ a b : Γ, (a, b) ∈ H ↔ π a ∈ alternatingGroup (Fin 5) ∧ π b ∈ alternatingGroup (Fin 5)) := by
  let H' : Subgroup (Perm (Fin 5) × Perm (Fin 5)) := H.map (π.prodMap π)
  have hH' : ∀ a b : Γ, (π a, π b) ∈ H' ↔ (a, b) ∈ H := by
    intro a b
    constructor
    · rintro ⟨⟨a', b'⟩, hab', he⟩
      have h1 : π a' = π a := congrArg Prod.fst he
      have h2 : π b' = π b := congrArg Prod.snd he
      have hk := hK (a'⁻¹ * a) (b'⁻¹ * b) (by rw [map_mul, map_inv, h1]; group)
        (by rw [map_mul, map_inv, h2]; group)
      have := H.mul_mem hab' hk
      simpa [Prod.mk_mul_mk] using this
    · intro h
      exact ⟨(a, b), h, rfl⟩
  have hsurj : ∀ s t : Perm (Fin 5), (s, t) ∈ H' → ∃ a b : Γ, π a = s ∧ π b = t ∧ (a, b) ∈ H := by
    rintro s t ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, congrArg Prod.fst he, congrArg Prod.snd he, hab⟩
  have key := dichotomy_S5 H'
    (fun a b hab => by
      obtain ⟨a', b', rfl, rfl, h⟩ := hsurj a b hab
      exact (hH' b' a').2 (hsw _ _ h))
    (fun s hs => by
      obtain ⟨b, rfl, hb⟩ := hdg s hs
      exact (hH' b b).2 hb)
    (fun s hs => by
      obtain ⟨a, b, rfl, hb, h⟩ := hsurj s s hs
      exact hb ▸ hodd a b h hb.symm)
  rcases key with h | h
  · left
    intro a b
    rw [← hH']
    exact h (π a) (π b)
  · right
    intro a b
    rw [← hH']
    exact h (π a) (π b)

end CFSG.EvenSporadicStandard.Fin76b
