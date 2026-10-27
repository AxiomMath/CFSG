module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrIso

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open scoped commutatorElement

variable {Y : Type*} [Group Y]

theorem aut_mem_normalizer {S : Subgroup Y} (φ : MulAut Y) (hS : ∀ w, w ∈ S ↔ φ w ∈ S) {b : Y}
    (hb : b ∈ Subgroup.normalizer (S : Set Y)) : φ b ∈ Subgroup.normalizer (S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hb ⊢
  intro h
  obtain ⟨h', rfl⟩ : ∃ h', φ h' = h := ⟨φ.symm h, by simp⟩
  have e : φ b * φ h' * (φ b)⁻¹ = φ (b * h' * b⁻¹) := by simp
  rw [e]
  exact (hS h').symm.trans ((hb h').trans (hS _))

theorem mem_normalizer_of_conj_mul {S : Subgroup Y} {x : Y} {φ α : MulAut Y}
    (hα : α = MulAut.conj x * φ) (hαS : ∀ w, w ∈ S ↔ α w ∈ S) (hφ : ∀ w, w ∈ S ↔ φ w ∈ S) :
    x ∈ Subgroup.normalizer (S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have e : x * w * x⁻¹ = α (φ.symm w) := by
    rw [hα]
    simp [MulAut.conj_apply]
  have h1 : φ.symm w ∈ S ↔ w ∈ S := by
    have := hφ (φ.symm w)
    simpa using this
  rw [e, ← hαS, h1]

theorem conj_mul_power_map {S : Subgroup Y}
    (hab : ∀ b ∈ Subgroup.normalizer (S : Set Y), ∀ c ∈ Subgroup.normalizer (S : Set Y),
      ⁅b, c⁆ ∈ S)
    {x : Y} (hx : x ∈ Subgroup.normalizer (S : Set Y)) {φ : MulAut Y}
    (hφ : ∀ w, w ∈ S ↔ φ w ∈ S) {k : ℕ}
    (hk : ∀ b ∈ Subgroup.normalizer (S : Set Y), φ b * (b ^ k)⁻¹ ∈ S) :
    ∀ b ∈ Subgroup.normalizer (S : Set Y), (MulAut.conj x * φ) b * (b ^ k)⁻¹ ∈ S := by
  intro b hb
  have h1 : ⁅x, φ b⁆ ∈ S := hab x hx _ (aut_mem_normalizer φ hφ hb)
  have h2 : (MulAut.conj x * φ) b * (b ^ k)⁻¹ = ⁅x, φ b⁆ * (φ b * (b ^ k)⁻¹) := by
    simp [commutatorElement_def, MulAut.conj_apply, mul_assoc]
  rw [h2]
  exact S.mul_mem h1 (hk b hb)

theorem AutScalarTorus.of_decomp [Finite Y] (S₁ : Sylow 2 Y)
    (hab : ∀ b ∈ Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y),
      ∀ c ∈ Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y), ⁅b, c⁆ ∈ (S₁ : Subgroup Y))
    (hdec : ∀ α : MulAut Y, (∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧ α ^ e ∈ inn Y) →
      ∃ (x : Y) (φ : MulAut Y) (k : ℕ), α = MulAut.conj x * φ ∧
        (∀ w, w ∈ (S₁ : Subgroup Y) ↔ φ w ∈ (S₁ : Subgroup Y)) ∧
          ∀ b ∈ Subgroup.normalizer ((S₁ : Subgroup Y) : Set Y),
            φ b * (b ^ k)⁻¹ ∈ (S₁ : Subgroup Y)) :
    AutScalarTorus Y := by
  refine AutScalarTorus.of_sylow S₁ fun α hα hinn => ?_
  obtain ⟨x, φ, k, hαφ, hφ, hk⟩ := hdec α hinn
  have hαS := forall_iff_of_map_eq hα
  refine ⟨k, ?_⟩
  rw [hαφ]
  exact conj_mul_power_map hab (mem_normalizer_of_conj_mul hαφ hαS hφ) hφ hk

end CFSG.AGLEmbedding.ParabAutIrr
