module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Dich

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Subgroup

theorem trichotomy_S5 (H : Subgroup (Perm (Fin 5) × Perm (Fin 5)))
    (hΔ : ∀ s : Perm (Fin 5), (s, s) ∈ H) :
    (∀ a b, (a, b) ∈ H ↔ a = b) ∨
    (∀ a b, (a, b) ∈ H ↔ Perm.sign a = Perm.sign b) ∨
    (∀ a b, (a, b) ∈ H) := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  set A := alternatingGroup (Fin 5) with hA
  have hAmem : ∀ x : Perm (Fin 5), x ∈ A ↔ Perm.sign x = 1 := fun x => Perm.mem_alternatingGroup
  have hneg : ∀ u v : ℤˣ, u ≠ 1 → v ≠ 1 → u * v⁻¹ = 1 := by
    intro u v hu hv
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
    · exact absurd rfl hu
    · exact absurd rfl hu
    · exact absurd rfl hv
    · decide
  have hcomm : ∀ u v : ℤˣ, u * (v * u⁻¹ * v⁻¹) = 1 := by
    intro u v
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      decide
  let N : Subgroup (Perm (Fin 5)) := H.comap (MonoidHom.inl (Perm (Fin 5)) (Perm (Fin 5)))
  have hN : ∀ a, a ∈ N ↔ (a, 1) ∈ H := fun a => Iff.rfl
  have hchar : ∀ a b : Perm (Fin 5), (a, b) ∈ H ↔ a * b⁻¹ ∈ N := by
    intro a b
    rw [hN]
    constructor
    · intro hab
      have := H.mul_mem hab (H.inv_mem (hΔ b))
      simpa [Prod.mk_mul_mk, Prod.inv_mk] using this
    · intro hab
      have := H.mul_mem hab (hΔ b)
      simpa [Prod.mk_mul_mk] using this
  have hNconj : ∀ a ∈ N, ∀ g : Perm (Fin 5), g * a * g⁻¹ ∈ N := by
    intro a ha g
    rw [hN] at ha ⊢
    have := H.mul_mem (H.mul_mem (hΔ g) ha) (H.inv_mem (hΔ g))
    simpa [Prod.mk_mul_mk, Prod.inv_mk] using this
  have hnormal : ((N ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    exact ⟨hNconj k hk.1 g, (g * ⟨k, hk.2⟩ * g⁻¹).2⟩
  have hNA : (∀ x ∈ N, x ∈ A → x = 1) ∨ (∀ g ∈ A, g ∈ N) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ A).subgroupOf A) with h1 | h1
    · left
      intro x hx hxA
      have : (⟨x, hxA⟩ : A) ∈ (N ⊓ A).subgroupOf A := mem_subgroupOf.2 ⟨hx, hxA⟩
      rw [h1, mem_bot] at this
      exact congrArg Subtype.val this
    · right
      intro g hg
      have : (⟨g, hg⟩ : A) ∈ (N ⊓ A).subgroupOf A := by rw [h1]; exact mem_top _
      exact ((mem_subgroupOf.1 this).1 : g ∈ N)
  rcases hNA with hNA | hAN
  ·
    left
    have hN1 : ∀ a ∈ N, a = 1 := by
      intro a ha
      refine perm_five_central a fun g _ => ?_
      have hx1 : a * (g * a⁻¹ * g⁻¹) ∈ N := mul_mem ha (hNconj a⁻¹ (inv_mem ha) g)
      have hx2 : a * (g * a⁻¹ * g⁻¹) ∈ A := by
        rw [hAmem]
        simp only [map_mul, map_inv]
        exact hcomm _ _
      have hx := hNA _ hx1 hx2
      calc a * g = (a * (g * a⁻¹ * g⁻¹)) * (g * a) := by group
        _ = g * a := by rw [hx, one_mul]
    intro a b
    rw [hchar]
    constructor
    · intro hab
      exact mul_inv_eq_one.1 (hN1 _ hab)
    · intro hab
      rw [hab, mul_inv_cancel]
      exact N.one_mem
  · by_cases hodd : ∃ s ∈ N, s ∉ A
    ·
      right
      right
      obtain ⟨s, hsN, hsA⟩ := hodd
      have hall : ∀ g : Perm (Fin 5), g ∈ N := by
        intro g
        by_cases hgA : g ∈ A
        · exact hAN g hgA
        · have hgs : g * s⁻¹ ∈ A := by
            rw [hAmem] at hgA hsA ⊢
            rw [map_mul, map_inv]
            exact hneg _ _ hgA hsA
          have := mul_mem (hAN _ hgs) hsN
          simpa using this
      intro a b
      rw [hchar]
      exact hall _
    ·
      right
      left
      push_neg at hodd
      have hNiff : ∀ g : Perm (Fin 5), g ∈ N ↔ g ∈ A := fun g => ⟨hodd g, hAN g⟩
      intro a b
      rw [hchar, hNiff, hAmem, map_mul, map_inv, mul_inv_eq_one]

theorem trichotomy {Γ : Type*} [Group Γ] (π : Γ →* Perm (Fin 5)) (H : Subgroup (Γ × Γ))
    (hK : ∀ a b : Γ, π a = 1 → π b = 1 → (a, b) ∈ H)
    (hdg : ∀ s : Perm (Fin 5), ∃ b : Γ, π b = s ∧ (b, b) ∈ H) :
    (∀ a b : Γ, (a, b) ∈ H ↔ π a = π b) ∨
    (∀ a b : Γ, (a, b) ∈ H ↔ Perm.sign (π a) = Perm.sign (π b)) ∨
    (∀ a b : Γ, (a, b) ∈ H) := by
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
  have hΔ : ∀ s : Perm (Fin 5), (s, s) ∈ H' := fun s => by
    obtain ⟨b, rfl, hb⟩ := hdg s
    exact (hH' b b).2 hb
  rcases trichotomy_S5 H' hΔ with h | h | h
  · left
    intro a b
    rw [← hH']
    exact h (π a) (π b)
  · right
    left
    intro a b
    rw [← hH']
    exact h (π a) (π b)
  · right
    right
    intro a b
    rw [← hH']
    exact h (π a) (π b)

end CFSG.EvenSporadicStandard.Fin76b
