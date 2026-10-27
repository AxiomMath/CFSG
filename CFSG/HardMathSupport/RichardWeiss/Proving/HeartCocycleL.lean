module

public import CFSG.HardMathSupport.RichardWeiss.Proving.HeartCohomology

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

variable {n : ℕ} {Λ : Type*} [Group Λ]

theorem cocycle_heart_decomp_of_hom (hn : 6 ≤ n) (hev : Even n) (a : Fin n)
    (θ : Λ →* Perm (Fin n)) (hAlt : ∀ l, θ l ∈ alternatingGroup (Fin n))
    (hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ l, θ l = σ)
    (F : Λ → altHeart n)
    (hF : ∀ l₁ l₂, F (l₁ * l₂) = F l₁ + altAct (θ l₁) (F l₂))
    (hker : ∀ r, θ r = 1 → F r = 0) :
    ∃ (w : altHeart n) (β : Bool), ∀ l : Λ,
      F l = (if β then (pairEW ((θ l) a) a : altHeart n) else 0) + (altAct (θ l) w - w) := by
  classical
  choose lift hlift using hsurj
  let f : alternatingGroup (Fin n) → altHeart n := fun σ => F (lift σ.1 σ.2)
  have hF1 : ∀ l₁ l₂, ∀ r, θ r = 1 → F (l₁ * l₂ * r) = F (l₁ * l₂) := by
    intro l₁ l₂ r hr
    rw [hF, hker r hr, map_zero, add_zero]
  have hf : ∀ σ τ, f (σ * τ) = f σ + altAct (σ : Perm (Fin n)) (f τ) := by
    intro σ τ
    let l₁ := lift σ.1 σ.2
    let l₂ := lift τ.1 τ.2
    let l₃ := lift (σ * τ).1 (σ * τ).2
    have hθ1 : θ l₁ = σ := hlift σ.1 σ.2
    have hθ2 : θ l₂ = τ := hlift τ.1 τ.2
    have hθ3 : θ l₃ = σ * τ := hlift (σ * τ).1 (σ * τ).2
    let r := (l₁ * l₂)⁻¹ * l₃
    have hr : θ r = 1 := by
      simp only [r, map_mul, map_inv, hθ1, hθ2, hθ3]; group
    have hl3 : l₃ = l₁ * l₂ * r := by simp only [r]; group
    show F l₃ = F l₁ + altAct (σ : Perm (Fin n)) (F l₂)
    rw [hl3, hF1 l₁ l₂ r hr, hF, hθ1]
  obtain ⟨w, β, hwβ⟩ := cocycle_heart_decomp hn hev a f hf
  refine ⟨w, β, fun l => ?_⟩
  let σ : alternatingGroup (Fin n) := ⟨θ l, hAlt l⟩
  let l₁ := lift σ.1 σ.2
  have hθ1 : θ l₁ = θ l := hlift σ.1 σ.2
  let r := l₁⁻¹ * l
  have hr : θ r = 1 := by simp only [r, map_mul, map_inv, hθ1]; group
  have hl : l = l₁ * r := by simp only [r]; group
  have e1 : F l = f σ := by
    rw [hl, hF, hker r hr, map_zero, add_zero]
  rw [e1, hwβ σ]

end CFSG.HardMathSupport.RichardWeiss.Proving
