module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GoldConj

public section

namespace CFSG.EvenSporadicStandard.M24Std.Gold

open Subgroup

variable {G : Type*} [Group G]

@[expose] def WClosed (T A : Subgroup G) : Prop := ∀ g : G, cj g A ≤ T → cj g A = A

theorem comm_cj {g : G} {A : Subgroup G} (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ a ∈ cj g A, ∀ b ∈ cj g A, a * b = b * a := by
  intro a ha b hb
  rw [mem_cj] at ha hb
  have h2 : g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ =
      g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [hab _ ha _ hb]
  simpa [mul_assoc] using h2

theorem WClosed.conj_mem {T : Sylow 2 G} {A : Subgroup G} (hw : WClosed T A) (hAT : A ≤ T)
    {x : G} (hx : x ∈ (T : Subgroup G)) {a : G} (ha : a ∈ A) : x * a * x⁻¹ ∈ A := by
  have h1 : cj x A ≤ T := by
    rintro _ ⟨a', ha', rfl⟩
    exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hx (hAT ha'))
      ((T : Subgroup G).inv_mem hx)
  have h2 := hw x h1
  have h3 : x * a * x⁻¹ ∈ cj x A := conj_mem_cj ha
  rwa [h2] at h3

theorem WClosed.cj_eq [Finite G] {T : Sylow 2 G} {A : Subgroup G} (hw : WClosed T A)
    {S : Subgroup G} (hS : IsPGroup 2 S) {g₁ g₂ : G} (h₁ : cj g₁ A ≤ S) (h₂ : cj g₂ A ≤ S) :
    cj g₁ A = cj g₂ A := by
  obtain ⟨x, hx⟩ := exists_le_cj_sylow T hS
  have key : ∀ g, cj g A ≤ S → cj g A = cj x A := by
    intro g hg
    have h1 : cj (x⁻¹ * g) A ≤ T := by
      rw [cj_mul, cj_le_iff, inv_inv]
      exact hg.trans hx
    have h2 := hw _ h1
    rw [cj_mul] at h2
    calc cj g A = cj x (cj x⁻¹ (cj g A)) := (cj_cj_inv x _).symm
      _ = cj x A := by rw [h2]
  rw [key g₁ h₁, key g₂ h₂]

theorem WClosed.le_of_centralizes [Finite G] {T : Sylow 2 G} {A : Subgroup G} (hw : WClosed T A)
    (hAT : A ≤ T) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {B : Subgroup G}
    (hBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) {y : G} (hy : cj y B ≤ A) : B ≤ A := by
  have hBA' : B ≤ cj y⁻¹ A := cj_le_iff.1 hy
  have hab' := comm_cj (g := y⁻¹) hab
  have hA2 : IsPGroup 2 A := T.isPGroup'.to_le hAT
  have hA'2 : IsPGroup 2 (cj y⁻¹ A) := isPGroup_cj hA2 _
  have hAK : A ≤ centralizer (B : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => hBA b hb a ha
  have hA'K : cj y⁻¹ A ≤ centralizer (B : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => hab' b (hBA' hb) a ha
  obtain ⟨k, hk, hS⟩ := exists_isPGroup_sup_cj hA2 hA'2 hAK hA'K
  have h1 : cj 1 A ≤ A ⊔ cj k (cj y⁻¹ A) := by
    rw [cj_one]
    exact le_sup_left
  have h2 : cj (k * y⁻¹) A ≤ A ⊔ cj k (cj y⁻¹ A) := by
    rw [cj_mul]
    exact le_sup_right
  have h3 := hw.cj_eq hS h1 h2
  rw [cj_one, cj_mul] at h3
  intro b hb
  rw [h3]
  have hkb : k * b * k⁻¹ = b := by
    have := mem_centralizer_iff.1 hk b hb
    rw [← this]
    group
  have h4 : k * b * k⁻¹ ∈ cj k (cj y⁻¹ A) := conj_mem_cj (hBA' hb)
  rwa [hkb] at h4

theorem WClosed.exists_cj_le [Finite G] {T : Sylow 2 G} {A : Subgroup G} (hw : WClosed T A)
    (hAT : A ≤ T) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {B : Subgroup G} {y : G}
    (hy : cj y B ≤ A) :
    ∃ g : G, cj g B ≤ A ∧ cj g ((T : Subgroup G) ⊓ normalizer (B : Set G)) ≤ T := by
  have hBA₁ : B ≤ cj y⁻¹ A := cj_le_iff.1 hy
  have hab₁ := comm_cj (g := y⁻¹) hab
  have hA2 : IsPGroup 2 A := T.isPGroup'.to_le hAT
  have hA₁2 : IsPGroup 2 (cj y⁻¹ A) := isPGroup_cj hA2 _
  have hA₁N : cj y⁻¹ A ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer (B : Set G)
      (mem_centralizer_iff.2 fun b hb => hab₁ b (hBA₁ hb) a ha)
  have hP2 : IsPGroup 2 ↥((T : Subgroup G) ⊓ normalizer (B : Set G)) :=
    T.isPGroup'.to_le inf_le_left
  obtain ⟨n, hn, hS⟩ := exists_isPGroup_sup_cj hP2 hA₁2 inf_le_right hA₁N
  obtain ⟨x, hx⟩ := exists_le_cj_sylow T hS
  refine ⟨x⁻¹, ?_, ?_⟩
  · have hBW : B ≤ cj n (cj y⁻¹ A) := by
      intro b hb
      rw [mem_cj]
      apply hBA₁
      have := (mem_normalizer_iff.1 hn (n⁻¹ * b * n)).2 (by simpa [mul_assoc] using hb)
      exact this
    have h1 : cj (x⁻¹ * (n * y⁻¹)) A ≤ T := by
      rw [cj_mul, cj_mul, cj_le_iff, inv_inv]
      exact le_sup_right.trans hx
    have h2 := hw _ h1
    calc cj x⁻¹ B ≤ cj x⁻¹ (cj n (cj y⁻¹ A)) := cj_le_cj.2 hBW
      _ = A := by rw [← cj_mul n y⁻¹ A, ← cj_mul x⁻¹ (n * y⁻¹) A, h2]
  · rw [cj_le_iff, inv_inv]
    exact le_sup_left.trans hx

end CFSG.EvenSporadicStandard.M24Std.Gold
