module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4AutB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open Subgroup

variable {G : Type} [Group G]

theorem five_le_card [Finite G] {K : Subgroup G} {x₁ x₂ x₃ x₄ x₅ : G} (h₁ : x₁ ∈ K)
    (h₂ : x₂ ∈ K) (h₃ : x₃ ∈ K) (h₄ : x₄ ∈ K) (h₅ : x₅ ∈ K) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h14 : x₁ ≠ x₄) (h15 : x₁ ≠ x₅) (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h25 : x₂ ≠ x₅)
    (h34 : x₃ ≠ x₄) (h35 : x₃ ≠ x₅) (h45 : x₄ ≠ x₅) : 5 ≤ Nat.card K := by
  have hsub : ({x₁, x₂, x₃, x₄, x₅} : Set G) ⊆ K := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({x₁, x₂, x₃, x₄, x₅} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13, h14, h15]),
      Set.ncard_insert_of_notMem (by simp [h23, h24, h25]),
      Set.ncard_insert_of_notMem (by simp [h34, h35]), Set.ncard_pair h45]
  calc 5 = ({x₁, x₂, x₃, x₄, x₅} : Set G).ncard := hcard.symm
    _ ≤ (K : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card K := (Nat.card_coe_set_eq _).symm

theorem eq_of_mem_three [Finite G] {B F : Subgroup G} (hB8 : Nat.card B = 8) (hFB : F ≤ B)
    {a b₂ b₃ : G} (haF : a ∈ F) (hb₂F : b₂ ∈ F) (hb₃F : b₃ ∈ F) (haa : a * a = 1)
    (ha1 : a ≠ 1) (hb₂1 : b₂ ≠ 1) (hb₂a : b₂ ≠ a) (hb₃1 : b₃ ≠ 1) (hb₃a : b₃ ≠ a)
    (hb₃b : b₃ ≠ b₂) (hb₃ab : b₃ ≠ a * b₂) : F = B := by
  have hab1 : (1 : G) ≠ a * b₂ := by
    intro h
    apply hb₂a
    calc b₂ = a * (a * b₂) := by rw [← mul_assoc, haa, one_mul]
      _ = a := by rw [← h, mul_one]
  have haab : a ≠ a * b₂ := fun h => hb₂1 (by
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm)
  have hbab : b₂ ≠ a * b₂ := fun h => ha1 (by
    have := congrArg (· * b₂⁻¹) h
    simpa using this.symm)
  have h5 := five_le_card (one_mem F) haF hb₂F (mul_mem haF hb₂F) hb₃F (Ne.symm ha1)
    (Ne.symm hb₂1) hab1 (Ne.symm hb₃1) (Ne.symm hb₂a) haab (Ne.symm hb₃a) hbab (Ne.symm hb₃b)
    (Ne.symm hb₃ab)
  have hdvd : Nat.card F ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 from rfl, ← hB8]
    exact card_dvd_of_le hFB
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk3 : k = 3 := by
    interval_cases k <;> simp_all
  exact eq_of_le_of_card_ge hFB (by rw [hB8, hk', hk3]; norm_num)

section Cycle

variable {E : Type} [Group E]

theorem exists_mulAut_cycle (hE : ∀ x y : E, x * y = y * x) (h2 : ∀ x : E, x * x = 1)
    {a b₂ b₃ : E} (hb₂1 : b₂ ≠ 1) (hb₂a : b₂ ≠ a) (hb₃1 : b₃ ≠ 1) (hb₃a : b₃ ≠ a)
    (hb₃b : b₃ ≠ b₂) (hb₃ab : b₃ ≠ a * b₂) :
    ∃ σ : MulAut E, σ a = a ∧ σ b₂ = b₃ ∧ σ b₃ = b₃ * b₂ := by
  have hfix : ∀ (τ : MulAut E) (u : E), u ≠ 1 → (∀ x : E, x⁻¹ * τ x ∈ zpowers u) → τ u = u := by
    intro τ u hu1 hτ
    rcases GrS4.eq_one_or_eq_of_mem_zpowers (h2 u) (hτ u) with h | h
    · calc τ u = u * (u⁻¹ * τ u) := by group
        _ = u := by rw [h, mul_one]
    · exfalso
      apply hu1
      refine τ.injective ?_
      calc τ u = u * (u⁻¹ * τ u) := by group
        _ = τ 1 := by rw [h, h2, map_one]
  obtain ⟨τ₂, hτ₂, hτ₂u, hτ₂v⟩ := GrS4.exists_mulAut_transvection hE h2 (a := b₂) (u := b₃)
    (v := a) hb₃1 hb₃b hb₃a (by rwa [hE b₂ a])
  obtain ⟨τ₃, hτ₃, hτ₃u, hτ₃v⟩ := GrS4.exists_mulAut_transvection hE h2 (a := b₃) (u := b₂)
    (v := a) hb₂1 (Ne.symm hb₃b) hb₂a (by
      intro h
      apply hb₃ab
      rw [h, hE b₃ a, ← mul_assoc, h2, one_mul])
  have hτ₂b : τ₂ b₂ = b₂ := hfix τ₂ b₂ hb₂1 hτ₂
  have hτ₃b : τ₃ b₃ = b₃ := hfix τ₃ b₃ hb₃1 hτ₃
  refine ⟨τ₂ * τ₃, ?_, ?_, ?_⟩
  · rw [MulAut.mul_apply, hτ₃v, hτ₂v]
  · rw [MulAut.mul_apply, hτ₃u, map_mul, hτ₂b, hτ₂u, hE b₃ b₂, ← mul_assoc, h2, one_mul]
  · rw [MulAut.mul_apply, hτ₃b, hτ₂u]

end Cycle

theorem mem_centralizer_of_cycle [Finite G] {B : Subgroup G} (hB : IsEightGroup B)
    {a b₂ b₃ r m : G} (haB : a ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B) (ha1 : a ≠ 1)
    (hb₂1 : b₂ ≠ 1) (hb₂a : b₂ ≠ a) (hb₃1 : b₃ ≠ 1) (hb₃a : b₃ ≠ a) (hb₃b : b₃ ≠ b₂)
    (hb₃ab : b₃ ≠ a * b₂) (hra : a * r = r * a)
    (hr : ∀ b ∈ B, r⁻¹ * b * r = b ∨ r⁻¹ * b * r = b * a)
    (hm₂ : m⁻¹ * b₂ * m = b₃ ∨ m⁻¹ * b₂ * m = b₃ * a)
    (hm₃ : m⁻¹ * b₃ * m = b₃ * b₂ ∨ m⁻¹ * b₃ * m = b₃ * b₂ * a)
    (hinv : ∀ b ∈ B, b ∈ centralizer ({r} : Set G) → m⁻¹ * b * m ∈ centralizer ({r} : Set G)) :
    r ∈ centralizer (B : Set G) := by
  set C := centralizer ({r} : Set G) with hC
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hra
  have haa : a * a = 1 := hB.1.2 a haB
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := hB.1.1
  have hfixC : ∀ {b : G}, r⁻¹ * b * r = b → b ∈ C := by
    intro b hb
    rw [hC, mem_centralizer_singleton_iff]
    calc b * r = r * (r⁻¹ * b * r) := by group
      _ = r * b := by rw [hb]
  have hdropa : ∀ {x : G}, x * a ∈ C → x ∈ C := by
    intro x hx
    have := mul_mem hx haC
    rwa [mul_assoc, haa, mul_one] at this
  have h23 : b₂ ∈ C → b₃ ∈ C := by
    intro h
    have h1 := hinv b₂ hb₂B h
    rcases hm₂ with e | e <;> rw [e] at h1
    · exact h1
    · exact hdropa h1
  have h32 : b₃ ∈ C → b₂ ∈ C := by
    intro h
    have h1 := hinv b₃ hb₃B h
    have h2 : b₃ * b₂ ∈ C := by
      rcases hm₃ with e | e <;> rw [e] at h1
      · exact h1
      · exact hdropa h1
    have := mul_mem (inv_mem h) h2
    rwa [inv_mul_cancel_left] at this
  have hb₂C : b₂ ∈ C := by
    rcases hr b₂ hb₂B with e₂ | e₂
    · exact hfixC e₂
    rcases hr b₃ hb₃B with e₃ | e₃
    · exact h32 (hfixC e₃)
    have hbbC : b₂ * b₃ ∈ C := by
      apply hfixC
      have e : r⁻¹ * (b₂ * b₃) * r = (r⁻¹ * b₂ * r) * (r⁻¹ * b₃ * r) := by group
      rw [e, e₂, e₃, show b₂ * a * (b₃ * a) = b₂ * (a * b₃) * a by group, hBc a haB b₃ hb₃B,
        show b₂ * (b₃ * a) * a = b₂ * b₃ * (a * a) by group, haa, mul_one]
    have h1 := hinv _ (mul_mem hb₂B hb₃B) hbbC
    have hsq : b₃ * (b₃ * b₂) = b₂ := by rw [← mul_assoc, hB.1.2 b₃ hb₃B, one_mul]
    rw [show m⁻¹ * (b₂ * b₃) * m = (m⁻¹ * b₂ * m) * (m⁻¹ * b₃ * m) by group] at h1
    rcases hm₂ with e | e <;> rcases hm₃ with f | f <;> rw [e, f] at h1
    · rwa [hsq] at h1
    · rw [show b₃ * (b₃ * b₂ * a) = b₃ * (b₃ * b₂) * a by group, hsq] at h1
      exact hdropa h1
    · rw [show b₃ * a * (b₃ * b₂) = b₃ * (a * b₃) * b₂ by group, hBc a haB b₃ hb₃B,
        show b₃ * (b₃ * a) * b₂ = b₃ * b₃ * (a * b₂) by group, hB.1.2 b₃ hb₃B, one_mul,
        hBc a haB b₂ hb₂B] at h1
      exact hdropa h1
    · rw [show b₃ * a * (b₃ * b₂ * a) = b₃ * (a * b₃) * b₂ * a by group, hBc a haB b₃ hb₃B,
        show b₃ * (b₃ * a) * b₂ * a = b₃ * b₃ * (a * b₂) * a by group, hB.1.2 b₃ hb₃B, one_mul,
        hBc a haB b₂ hb₂B, mul_assoc, haa, mul_one] at h1
      exact h1
  have hF := eq_of_mem_three hB.2 (inf_le_left : B ⊓ C ≤ B) (mem_inf.mpr ⟨haB, haC⟩)
    (mem_inf.mpr ⟨hb₂B, hb₂C⟩) (mem_inf.mpr ⟨hb₃B, h23 hb₂C⟩) haa ha1 hb₂1 hb₂a hb₃1 hb₃a hb₃b
    hb₃ab
  rw [mem_centralizer_iff]
  intro b hb
  rw [← hF] at hb
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp hb).2

@[expose] def lineKernel (X B : Subgroup G) (a : G) (hXa : X ≤ centralizer ({a} : Set G))
    (hXB : X ≤ normalizer (B : Set G)) : Subgroup G where
  carrier := {y | y ∈ X ∧ ∀ b ∈ B, b⁻¹ * (y⁻¹ * b * y) ∈ zpowers a}
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
    refine ⟨mul_mem hy₁ hy₂, fun b hb => ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (h₁ b hb)
    have hya : y₂⁻¹ * a * y₂ = a := by
      have := mem_centralizer_singleton_iff.mp (hXa hy₂)
      rw [mul_assoc, ← this, inv_mul_cancel_left]
    have h3 : y₂⁻¹ * (b⁻¹ * (y₁⁻¹ * b * y₁)) * y₂ ∈ zpowers a := by
      rw [← hk, show y₂⁻¹ * a ^ k * y₂ = y₂⁻¹ * a ^ k * y₂⁻¹⁻¹ by rw [inv_inv], ← conj_zpow,
        inv_inv, hya]
      exact zpow_mem (mem_zpowers a) k
    have := mul_mem (h₂ b hb) h3
    rwa [show b⁻¹ * (y₂⁻¹ * b * y₂) * (y₂⁻¹ * (b⁻¹ * (y₁⁻¹ * b * y₁)) * y₂) =
      b⁻¹ * ((y₁ * y₂)⁻¹ * b * (y₁ * y₂)) by group] at this
  one_mem' := ⟨one_mem X, fun b _ => by simp⟩
  inv_mem' := by
    rintro y ⟨hy, h⟩
    refine ⟨inv_mem hy, fun b hb => ?_⟩
    have hb' : y * b * y⁻¹ ∈ B := (mem_normalizer_iff.mp (hXB hy) b).mp hb
    have := inv_mem (h _ hb')
    rwa [show ((y * b * y⁻¹)⁻¹ * (y⁻¹ * (y * b * y⁻¹) * y))⁻¹ = b⁻¹ * (y⁻¹⁻¹ * b * y⁻¹) by
      group] at this

end CFSG.ComponentClassification.GrSLit.FinalG
