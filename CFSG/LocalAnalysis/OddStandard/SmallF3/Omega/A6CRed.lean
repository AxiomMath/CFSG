module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CImage
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CPair

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem a6c_red {X R Γ : Type} [Group X] [Group R] [Group Γ] [Finite X] [Finite Γ]
    {P : Γ → Prop} {kc bound : ℕ} (hP : ∀ a δ : Γ, P a → P (δ * a * δ⁻¹))
    (hΓ : ¬ 25 ∣ Nat.card Γ) (hkc : kc ∣ 40) (F : A6CPairFacts Γ P kc bound)
    (φ : X →* Γ) (ψ : R →* Γ) (e : X ⧸ center X ≃* alternatingGroup (Fin 6))
    (hodd : Odd (Nat.card (center X))) (hker : ∀ x : X, φ x = 1 → x ∈ center X)
    (hA : ∀ a ∈ φ.range, a * a = 1 → a ≠ 1 → P a)
    (hcomm : ∀ (x : X) (r : R), φ x * ψ r = ψ r * φ x) :
    Nat.card ψ.range ≤ bound ∧ ∀ c ∈ ψ.range, c * c = 1 := by
  obtain ⟨e'⟩ := a6c_range_equiv_A6 φ e hodd hker hΓ
    (fun ξ hξ => (a6c_card_centralizer_of_orderOf hΓ F hξ) ▸ hkc)
  obtain ⟨hcard, hexp⟩ := a6c_centralizer_A6 hP hΓ F φ.range e' hA
  have hle : ψ.range ≤ centralizer (φ.range : Set Γ) := by
    rintro _ ⟨r, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact hcomm x r
  exact ⟨(Subgroup.card_le_of_le hle).trans hcard, fun c hc => hexp c (hle hc)⟩

end CFSG.OddStandard.SmallF3.Omega
