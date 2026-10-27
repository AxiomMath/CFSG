module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Base

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup

variable {G : Type} [Group G]

private theorem comm_mul_left_eq {v₁ v₂ u : G} (h : Commute v₁ (v₂ * u * v₂⁻¹ * u⁻¹)) :
    v₁ * v₂ * u * (v₁ * v₂)⁻¹ * u⁻¹ = v₂ * u * v₂⁻¹ * u⁻¹ * (v₁ * u * v₁⁻¹ * u⁻¹) := by
  calc v₁ * v₂ * u * (v₁ * v₂)⁻¹ * u⁻¹
      = v₁ * (v₂ * u * v₂⁻¹ * u⁻¹) * u * v₁⁻¹ * u⁻¹ := by group
    _ = v₂ * u * v₂⁻¹ * u⁻¹ * v₁ * u * v₁⁻¹ * u⁻¹ := by rw [h.eq]
    _ = v₂ * u * v₂⁻¹ * u⁻¹ * (v₁ * u * v₁⁻¹ * u⁻¹) := by group

private theorem comm_mul_right_eq {v u₁ u₂ : G} (h : Commute u₁ (v * u₂ * v⁻¹ * u₂⁻¹)) :
    v * (u₁ * u₂) * v⁻¹ * (u₁ * u₂)⁻¹ = v * u₁ * v⁻¹ * u₁⁻¹ * (v * u₂ * v⁻¹ * u₂⁻¹) := by
  calc v * (u₁ * u₂) * v⁻¹ * (u₁ * u₂)⁻¹
      = v * u₁ * v⁻¹ * (v * u₂ * v⁻¹ * u₂⁻¹ * u₁⁻¹) := by group
    _ = v * u₁ * v⁻¹ * (u₁⁻¹ * (v * u₂ * v⁻¹ * u₂⁻¹)) := by rw [← h.inv_left.eq]
    _ = v * u₁ * v⁻¹ * u₁⁻¹ * (v * u₂ * v⁻¹ * u₂⁻¹) := by group

namespace Sec4Base

variable {L T U₁ : Subgroup G} {x : G}

theorem swapComm_mul (hE : Sec4Base L T U₁) (hxx : x * x = 1)
    (hxT : ∀ t ∈ T ⊓ centralizer (L : Set G), x * t * x⁻¹ ∈ U₁)
    (hxA : ∀ a ∈ gmsA L T, x * a = a * x) {t₁ t₂ : G}
    (h₁ : t₁ ∈ T ⊓ centralizer (L : Set G)) (h₂ : t₂ ∈ T ⊓ centralizer (L : Set G)) :
    t₁ * t₂ * (x * (t₁ * t₂) * x⁻¹) * (t₁ * t₂)⁻¹ * (x * (t₁ * t₂) * x⁻¹)⁻¹ =
      t₁ * (x * t₁ * x⁻¹) * t₁⁻¹ * (x * t₁ * x⁻¹)⁻¹ *
        (t₂ * (x * t₂ * x⁻¹) * t₂⁻¹ * (x * t₂ * x⁻¹)⁻¹) := by
  have hA : ∀ {t u : G}, t ∈ T ⊓ centralizer (L : Set G) → u ∈ U₁ →
      t * u * t⁻¹ * u⁻¹ ∈ gmsA L T := fun ht hu => hE.comm_mem _ ht _ hu
  have hTA : ∀ {t a : G}, t ∈ T ⊓ centralizer (L : Set G) → a ∈ gmsA L T → Commute t a :=
    fun ht ha => (mem_centralizer_iff.mp (mem_inf.mp ht).2 _ (mem_inf.mp (mem_inf.mp ha).1).2).symm
  have hUA : ∀ {u a : G}, u ∈ U₁ → a ∈ gmsA L T → Commute u a :=
    fun hu ha => hE.comm hu (hE.A_le ha)
  have hu : x * (t₁ * t₂) * x⁻¹ = x * t₁ * x⁻¹ * (x * t₂ * x⁻¹) := by group
  set u₁ := x * t₁ * x⁻¹ with hu₁def
  set u₂ := x * t₂ * x⁻¹ with hu₂def
  have hu₁ : u₁ ∈ U₁ := hxT t₁ h₁
  have hu₂ : u₂ ∈ U₁ := hxT t₂ h₂
  rw [hu, comm_mul_left_eq (hTA h₁ (hA h₂ (mul_mem hu₁ hu₂))),
    comm_mul_right_eq (hUA hu₁ (hA h₂ hu₂)), comm_mul_right_eq (hUA hu₁ (hA h₁ hu₂))]
  have hx : x * u₂ * x⁻¹ = t₂ := by
    calc x * u₂ * x⁻¹ = x * x * t₂ * (x * x)⁻¹ := by rw [hu₂def]; group
      _ = t₂ := by rw [hxx]; group
  have hcross : t₁ * u₂ * t₁⁻¹ * u₂⁻¹ = (t₂ * u₁ * t₂⁻¹ * u₁⁻¹)⁻¹ := by
    calc t₁ * u₂ * t₁⁻¹ * u₂⁻¹ = x * (t₁ * u₂ * t₁⁻¹ * u₂⁻¹) * x⁻¹ := by
          rw [hxA _ (hA h₁ hu₂)]; group
      _ = x * t₁ * x⁻¹ * (x * u₂ * x⁻¹) * (x * t₁ * x⁻¹)⁻¹ * (x * u₂ * x⁻¹)⁻¹ := by group
      _ = u₁ * t₂ * u₁⁻¹ * t₂⁻¹ := by rw [← hu₁def, hx]
      _ = (t₂ * u₁ * t₂⁻¹ * u₁⁻¹)⁻¹ := by group
  have hp := hA h₂ hu₁
  have hq := hA h₂ hu₂
  have hr := hA h₁ hu₁
  rw [hcross]
  set p := t₂ * u₁ * t₂⁻¹ * u₁⁻¹
  set q := t₂ * u₂ * t₂⁻¹ * u₂⁻¹
  set r := t₁ * u₁ * t₁⁻¹ * u₁⁻¹
  have hqr : Commute q r := hUA (hE.A_le hq) hr
  calc p * q * (r * p⁻¹) = p * (q * r) * p⁻¹ := by group
    _ = q * r * p * p⁻¹ := by
        rw [((hUA (hE.A_le hp) hq).mul_right (hUA (hE.A_le hp) hr)).eq]
    _ = r * q := by rw [mul_inv_cancel_right, hqr.eq]

theorem swapComm_eq_one (hE : Sec4Base L T U₁)
    (hxT : ∀ t ∈ T ⊓ centralizer (L : Set G), x * t * x⁻¹ ∈ U₁)
    (hxA : ∀ a ∈ gmsA L T, x * a = a * x) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G))
    (h1 : t * (x * t * x⁻¹) * t⁻¹ * (x * t * x⁻¹)⁻¹ = 1) : t = 1 := by
  by_contra hne
  have h2 : t * (x * t * x⁻¹) * t⁻¹ = x * t * x⁻¹ := mul_inv_eq_one.mp h1
  have hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹) := by
    calc x * t * x⁻¹ * t = t * (x * t * x⁻¹) * t⁻¹ * t := by rw [h2]
      _ = t * (x * t * x⁻¹) := by group
  have huA : x * t * x⁻¹ ∈ gmsA L T := by
    rw [← hE.centralizer_eq t ht hne]
    exact mem_inf.mpr ⟨hxT t ht, mem_centralizer_singleton_iff.mpr hcomm⟩
  have htu : t = x * t * x⁻¹ := by
    calc t = x⁻¹ * (x * t * x⁻¹ * x) := by group
      _ = x⁻¹ * (x * (x * t * x⁻¹)) := by rw [← hxA _ huA]
      _ = x * t * x⁻¹ := by group
  have hmem : t ∈ (T ⊓ centralizer (L : Set G)) ⊓ U₁ :=
    mem_inf.mpr ⟨ht, hE.A_le (htu ▸ huA)⟩
  rw [hE.inf_eq_bot, mem_bot] at hmem
  exact hne hmem

theorem exists_swapComm_eq [Finite G] (hE : Sec4Base L T U₁)
    (hcard : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = Nat.card (gmsA L T))
    (hxx : x * x = 1) (hxT : ∀ t ∈ T ⊓ centralizer (L : Set G), x * t * x⁻¹ ∈ U₁)
    (hxA : ∀ a ∈ gmsA L T, x * a = a * x) {b : G} (hb : b ∈ gmsA L T) :
    ∃ t ∈ T ⊓ centralizer (L : Set G), t * (x * t * x⁻¹) * t⁻¹ * (x * t * x⁻¹)⁻¹ = b := by
  let φ : (T ⊓ centralizer (L : Set G) : Subgroup G) → gmsA L T := fun t =>
    ⟨t * (x * t * x⁻¹) * (t : G)⁻¹ * (x * t * x⁻¹)⁻¹, hE.comm_mem t t.2 _ (hxT t t.2)⟩
  have hinj : Function.Injective φ := by
    intro t₁ t₂ h12
    have h : (t₁ : G) * (x * t₁ * x⁻¹) * (t₁ : G)⁻¹ * (x * t₁ * x⁻¹)⁻¹ =
        t₂ * (x * t₂ * x⁻¹) * (t₂ : G)⁻¹ * (x * t₂ * x⁻¹)⁻¹ := congrArg Subtype.val h12
    have hs : (t₂ : G)⁻¹ * t₁ ∈ T ⊓ centralizer (L : Set G) := mul_mem (inv_mem t₂.2) t₁.2
    have hmul := hE.swapComm_mul hxx hxT hxA t₂.2 hs
    rw [show (t₂ : G) * ((t₂ : G)⁻¹ * t₁) = t₁ by group, h] at hmul
    have h1 := hE.swapComm_eq_one hxT hxA hs (mul_eq_left.mp hmul.symm)
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  obtain ⟨t, ht⟩ := ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).2 ⟨b, hb⟩
  exact ⟨t, t.2, congrArg Subtype.val ht⟩

theorem exists_conj_eq_mul_of_swap [Finite G] (hE : Sec4Base L T U₁)
    (hcard : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = Nat.card (gmsA L T))
    (hxx : x * x = 1) (hxT : ∀ t ∈ T ⊓ centralizer (L : Set G), x * t * x⁻¹ ∈ U₁)
    (hxA : ∀ a ∈ gmsA L T, x * a = a * x) {b : G} (hb : b ∈ gmsA L T) :
    ∃ w ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)), w * x * w⁻¹ = x * b := by
  obtain ⟨t, ht, rfl⟩ := hE.exists_swapComm_eq hcard hxx hxT hxA hb
  refine ⟨t * (x * t * x⁻¹), mul_mem (mem_sup_right ht) (mem_sup_left (hxT t ht)), ?_⟩
  rw [hxA _ hb, inv_eq_of_mul_eq_one_right hxx]
  group

end Sec4Base

end CFSG.ComponentClassification.GMS78
