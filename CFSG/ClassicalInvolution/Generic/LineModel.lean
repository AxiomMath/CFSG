module

public import CFSG.ClassicalInvolution.Generic.Weyl
public import CFSG.ClassicalInvolution.Generic.FrameTorus

public section

namespace CFSG.ClassicalInvolution.Generic

section Transport

variable {H G : Type*} [Group H] [Group G]

theorem conjSub_map (θ : H →* G) (x : H) (B : Subgroup H) :
    conjSub (θ x) (B.map θ) = (conjSub x B).map θ := by
  ext y
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨x * b * x⁻¹, conj_mem_conjSub hb, by simp⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨θ b, ⟨b, hb, rfl⟩, by simp⟩

theorem conjSub_eq_self_of_forall {x : H} {B : Subgroup H} (hx : ∀ m ∈ B, x * m * x⁻¹ ∈ B)
    (hx' : ∀ m ∈ B, x⁻¹ * m * x ∈ B) : conjSub x B = B := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := hx _ h
    simpa [mul_assoc] using this
  · intro h
    exact hx' y h

theorem mem_normalizer_map {θ : H →* G} {D : Subgroup H} {ω : H}
    (hω : ∀ d ∈ D, ω * d * ω⁻¹ ∈ D) (hω' : ∀ d ∈ D, ω⁻¹ * d * ω ∈ D) :
    θ ω ∈ Subgroup.normalizer ((D.map θ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨ω * d * ω⁻¹, hω d hd, by simp⟩
  · rintro ⟨d', hd', hy⟩
    refine ⟨ω⁻¹ * d' * ω, hω' d' hd', ?_⟩
    rw [map_mul, map_mul, map_inv, hy]
    group

end Transport

section Model

variable {F : Type*} [Field F] {H G : Type*} [Group H] [Group G]

theorem isLine_of_model [Finite F] {E K L : Subgroup G} (hK : InSigma F E K)
    (hL : InSigma F E L) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) {θ : H →* G}
    {B₁ B₂ D₁ D₂ : Subgroup H} {w₁ w₂ : H} (hker : θ.ker ≤ Subgroup.center H)
    (hB₁ : ∀ b ∈ B₁, b ∈ Subgroup.center H → b = 1)
    (hB₂ : ∀ b ∈ B₂, b ∈ Subgroup.center H → b = 1) (hD₁ : D₁ ≤ B₁) (hD₂ : D₂ ≤ B₂)
    (hKB : B₁.map θ = K) (hLB : B₂.map θ = L) (hHK : centPart K E = D₁.map θ)
    (hHL : centPart L E = D₂.map θ) (tor₁ : ∀ d ∈ D₁, ∀ m ∈ B₂, d * m * d⁻¹ ∈ B₂)
    (tor₂ : ∀ d ∈ D₂, ∀ m ∈ B₁, d * m * d⁻¹ ∈ B₁) (hw₁ : w₁ ∈ B₁) (hw₂ : w₂ ∈ B₂)
    (nw₁ : ∀ d ∈ D₁, w₁ * d * w₁⁻¹ ∈ D₁) (nw₁' : ∀ d ∈ D₁, w₁⁻¹ * d * w₁ ∈ D₁)
    (nw₂ : ∀ d ∈ D₂, w₂ * d * w₂⁻¹ ∈ D₂) (nw₂' : ∀ d ∈ D₂, w₂⁻¹ * d * w₂ ∈ D₂)
    (ndw₁ : w₁ ∉ D₁) (ndw₂ : w₂ ∉ D₂) (swap : conjSub w₁ B₂ = conjSub w₂ B₁)
    (cube : (w₁ * w₂) ^ 3 = 1) : IsLine E K L ∧ IsLine E L K := by
  subst hKB hLB
  have tL : ∀ c ∈ centPart (B₁.map θ) E, conjSub c (B₂.map θ) = B₂.map θ := by
    intro c hc
    rw [hHK] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    rw [conjSub_map, conjSub_eq_self_of_forall (fun m hm => tor₁ d hd m hm)
      (fun m hm => by simpa using tor₁ d⁻¹ (D₁.inv_mem hd) m hm)]
  have tR : ∀ c ∈ centPart (B₂.map θ) E, conjSub c (B₁.map θ) = B₁.map θ := by
    intro c hc
    rw [hHL] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    rw [conjSub_map, conjSub_eq_self_of_forall (fun m hm => tor₂ d hd m hm)
      (fun m hm => by simpa using tor₂ d⁻¹ (D₂.inv_mem hd) m hm)]
  have hwK_mem : θ w₁ ∈ normPart (B₁.map θ) E := by
    rw [hK.normPart_eq hodd h5, Subgroup.mem_inf, hHK]
    exact ⟨⟨w₁, hw₁, rfl⟩, mem_normalizer_map nw₁ nw₁'⟩
  have hwL_mem : θ w₂ ∈ normPart (B₂.map θ) E := by
    rw [hL.normPart_eq hodd h5, Subgroup.mem_inf, hHL]
    exact ⟨⟨w₂, hw₂, rfl⟩, mem_normalizer_map nw₂ nw₂'⟩
  have hwK_nc : θ w₁ ∉ centPart (B₁.map θ) E := by
    rw [hHK]
    rintro ⟨d, hd, hdθ⟩
    have hz : w₁ * d⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdθ, mul_inv_cancel]
    have h1 : w₁ * d⁻¹ = 1 := hB₁ _ (B₁.mul_mem hw₁ (B₁.inv_mem (hD₁ hd))) (hker hz)
    exact ndw₁ (mul_inv_eq_one.mp h1 ▸ hd)
  have hwL_nc : θ w₂ ∉ centPart (B₂.map θ) E := by
    rw [hHL]
    rintro ⟨d, hd, hdθ⟩
    have hz : w₂ * d⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdθ, mul_inv_cancel]
    have h1 : w₂ * d⁻¹ = 1 := hB₂ _ (B₂.mul_mem hw₂ (B₂.inv_mem (hD₂ hd))) (hker hz)
    exact ndw₂ (mul_inv_eq_one.mp h1 ▸ hd)
  have hswap : conjSub (θ w₁) (B₂.map θ) = conjSub (θ w₂) (B₁.map θ) := by
    rw [conjSub_map, conjSub_map, swap]
  have hcube : (θ w₁ * θ w₂) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, cube, map_one]
  have hcube' : (θ w₂ * θ w₁) ^ 3 = 1 := by
    have h1 : (θ w₂ * θ w₁) ^ 3 = (θ w₁)⁻¹ * (θ w₁ * θ w₂) ^ 3 * θ w₁ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [h1, hcube]
    group
  refine ⟨⟨tL, tR, θ w₁, hwK_mem, hwK_nc, θ w₂, hwL_mem, hwL_nc, hswap, ?_⟩,
    ⟨tR, tL, θ w₂, hwL_mem, hwL_nc, θ w₁, hwK_mem, hwK_nc, hswap.symm, ?_⟩⟩
  · rw [hcube]
    exact one_mem _
  · rw [hcube']
    exact one_mem _

end Model

end CFSG.ClassicalInvolution.Generic
