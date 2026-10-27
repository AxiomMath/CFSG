module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L4

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Comm

variable {S : Type} [Group S]

@[expose] def commHom (K : Subgroup S) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (g : S)
    (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K) : K →* K :=
  MonoidHom.mk' (fun y : K => ⟨g * (y : S) * g⁻¹ * (y : S)⁻¹,
      K.mul_mem (hKg _ y.2) (K.inv_mem y.2)⟩) (by
    intro y₁ y₂
    apply Subtype.ext
    have hc : (y₁ : S)⁻¹ * (g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹) =
        (g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹) * (y₁ : S)⁻¹ :=
      hKab _ (K.inv_mem y₁.2) _ (K.mul_mem (hKg _ y₂.2) (K.inv_mem y₂.2))
    have e1 : g * ((y₁ * y₂ : K) : S) * g⁻¹ * ((y₁ * y₂ : K) : S)⁻¹ =
        (g * (y₁ : S) * g⁻¹) * ((g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹) * (y₁ : S)⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    show g * ((y₁ * y₂ : K) : S) * g⁻¹ * ((y₁ * y₂ : K) : S)⁻¹ =
      (g * (y₁ : S) * g⁻¹ * (y₁ : S)⁻¹) * (g * (y₂ : S) * g⁻¹ * (y₂ : S)⁻¹)
    rw [e1, ← hc]
    group)

@[expose] def commSub (K : Subgroup S) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (g : S)
    (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K) : Subgroup S :=
  (commHom K hKab g hKg).range.map K.subtype

theorem mem_commSub (K : Subgroup S) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (g : S)
    (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K) (x : S) :
    x ∈ commSub K hKab g hKg ↔ ∃ y ∈ K, x = g * y * g⁻¹ * y⁻¹ := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩

theorem commSub_le (K : Subgroup S) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (g : S)
    (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K) : commSub K hKab g hKg ≤ K := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_commSub K hKab g hKg x).mp hx
  exact K.mul_mem (hKg _ hy) (K.inv_mem hy)

theorem card_eq_fix_mul_comm [Finite S] (K : Subgroup S)
    (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (g : S) (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K) :
    Nat.card K = Nat.card (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) *
      Nat.card (commSub K hKab g hKg) := by
  have h := card_eq_ker_mul_range (commHom K hKab g hKg)
  have h1 : Nat.card (commHom K hKab g hKg).ker =
      Nat.card (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) := by
    have hmap : (commHom K hKab g hKg).ker.map K.subtype =
        (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        have h1 : g * (y : S) * g⁻¹ * (y : S)⁻¹ = 1 := congrArg Subtype.val hy
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc (y : S) * g = (g * (y : S) * g⁻¹ * (y : S)⁻¹)⁻¹ * (g * (y : S)) := by group
          _ = g * (y : S) := by rw [h1]; group
      · rintro ⟨hxK, hxc⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        have h2 : x * g = g * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
        apply Subtype.ext
        show g * x * g⁻¹ * x⁻¹ = 1
        rw [← h2]
        group
    rw [← hmap, Subgroup.card_map_of_injective K.subtype_injective]
  have h2 : Nat.card (commSub K hKab g hKg) = Nat.card (commHom K hKab g hKg).range := by
    unfold commSub
    exact Subgroup.card_map_of_injective K.subtype_injective
  rw [h2, ← h1]
  exact h

theorem commSub_le_fix (K : Subgroup S) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hexp : ∀ x ∈ K, x * x = 1) (g : S) (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K)
    (hg2 : ∀ y ∈ K, g * g * y = y * (g * g)) :
    commSub K hKab g hKg ≤ K ⊓ Subgroup.centralizer ({g} : Set S) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_commSub K hKab g hKg x).mp hx
  refine ⟨K.mul_mem (hKg _ hy) (K.inv_mem hy), ?_⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have hu : g * y⁻¹ * g⁻¹ ∈ K := hKg _ (K.inv_mem hy)
  have hyu : (y * (g * y⁻¹ * g⁻¹)) * (y * (g * y⁻¹ * g⁻¹)) = 1 :=
    hexp _ (K.mul_mem hy hu)
  have hgy : g * g * y * g⁻¹ * g⁻¹ = y := by
    rw [hg2 y hy]
    group
  have key : g * (g * y * g⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ = 1 := by
    have e : g * (g * y * g⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ =
        (g * g * y * g⁻¹ * g⁻¹) * (g * y⁻¹ * g⁻¹) *
          (y * (g * y⁻¹ * g⁻¹)) := by group
    rw [e, hgy]
    exact hyu
  calc (g * y * g⁻¹ * y⁻¹) * g
      = (g * (g * y * g⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹)⁻¹ *
          (g * (g * y * g⁻¹ * y⁻¹)) := by group
    _ = g * (g * y * g⁻¹ * y⁻¹) := by rw [key]; group

theorem card_le_card_fix_sq [Finite S] (K : Subgroup S)
    (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hexp : ∀ x ∈ K, x * x = 1) (g : S)
    (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K) (hg2 : ∀ y ∈ K, g * g * y = y * (g * g)) :
    Nat.card K ≤ Nat.card (K ⊓ Subgroup.centralizer ({g} : Set S) : Subgroup S) ^ 2 := by
  have h := card_eq_fix_mul_comm K hKab g hKg
  have hle := Subgroup.card_le_of_le (commSub_le_fix K hKab hexp g hKg hg2)
  rw [h, pow_two]
  exact Nat.mul_le_mul_left _ hle

end Comm

end CFSG.EvenSporadicStandard.Fin76b
