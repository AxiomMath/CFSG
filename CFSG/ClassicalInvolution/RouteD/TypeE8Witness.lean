module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Model

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Adjoint (iform)

variable (p f : ℕ) [Fact p.Prime]

theorem mem_roots_D7_iff (v : Fin 7 → ℤ) : v ∈ (D7 p f).roots ↔ v ∈ rootFinset .E7 :=
  (CFSG.LieType.Steinberg.Minuscule.e7Data_valid.mem_minDatum_roots
    CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7 (GaloisField p f)).trans
    mem_rootFinset.symm

private abbrev V7 : Type := Fin (Tag.rank .E7) → ℤ

private def vec (l : List ℤ) : V7 := fun i => l.getD i 0

private def R1W (p₀ : Fin 7) (γ c l₁ l₂ l₃ : V7) : Prop :=
  (γ ∈ rootFinset .E7 ∧ c ∈ rootFinset .E7 ∧ l₁ ∈ rootFinset .E7 ∧ l₂ ∈ rootFinset .E7 ∧
    l₃ ∈ rootFinset .E7) ∧
  (((γ p₀ : ℤ) : ZMod 2) = 0 ∧ ((c p₀ : ℤ) : ZMod 2) = 0 ∧ ((l₁ p₀ : ℤ) : ZMod 2) = 0 ∧
    ((l₂ p₀ : ℤ) : ZMod 2) = 0 ∧ ((l₃ p₀ : ℤ) : ZMod 2) = 0) ∧
  (iform γ c = 0 ∧ iform γ l₁ = 0 ∧ iform γ l₂ = 0 ∧ iform γ l₃ = 0 ∧ iform c l₁ = -1 ∧
    iform c l₂ = -1 ∧ iform c l₃ = -1 ∧ iform l₁ l₂ = 0 ∧ iform l₁ l₃ = 0 ∧ iform l₂ l₃ = 0)

private theorem r1w_0 : R1W 0 (vec [-2,-2,-3,-4,-3,-2,-1]) (vec [0,-1,-1,-2,-2,-2,-1])
    (vec [0,0,0,0,0,1,0]) (vec [0,0,0,0,1,1,1])
    (vec [0,1,1,2,1,1,1]) := by
  unfold R1W; decide +kernel

private theorem r1w_2 : R1W 2 (vec [-1,-2,-2,-4,-3,-2,-1]) (vec [-1,-1,-2,-2,-2,-2,-1])
    (vec [0,0,0,0,0,1,0]) (vec [0,0,0,0,1,1,1])
    (vec [1,1,2,2,1,1,1]) := by
  unfold R1W; decide +kernel

private theorem r1w_3 : R1W 3 (vec [-2,-2,-3,-4,-3,-2,-1]) (vec [0,-1,-1,-2,-2,-2,-1])
    (vec [0,0,0,0,0,1,0]) (vec [0,0,0,0,1,1,1])
    (vec [0,1,1,2,1,1,1]) := by
  unfold R1W; decide +kernel

private theorem r1w_5 : R1W 5 (vec [-2,-2,-3,-4,-3,-2,-1]) (vec [0,-1,-1,-2,-1,0,0])
    (vec [0,0,0,1,0,0,0]) (vec [0,0,1,1,1,0,0])
    (vec [0,1,0,1,1,0,0]) := by
  unfold R1W; decide +kernel

private def R2W (p₀ : Fin 7) (γ₁ γ₂ dx da db ρ δm δn : V7) : Prop :=
  (γ₁ ∈ rootFinset .E7 ∧ γ₂ ∈ rootFinset .E7 ∧ dx ∈ rootFinset .E7 ∧ da ∈ rootFinset .E7 ∧
    db ∈ rootFinset .E7 ∧ ρ ∈ rootFinset .E7 ∧ δm ∈ rootFinset .E7 ∧ δn ∈ rootFinset .E7) ∧
  (((γ₁ p₀ : ℤ) : ZMod 2) = 0 ∧ ((γ₂ p₀ : ℤ) : ZMod 2) = 0 ∧ ((dx p₀ : ℤ) : ZMod 2) = 0 ∧
    ((da p₀ : ℤ) : ZMod 2) = 0 ∧ ((db p₀ : ℤ) : ZMod 2) = 0 ∧ ((ρ p₀ : ℤ) : ZMod 2) ≠ 0 ∧
    ((δm p₀ : ℤ) : ZMod 2) ≠ 0) ∧
  (iform γ₁ γ₂ = 0 ∧ iform dx γ₁ = -1 ∧ (iform dx γ₁ + iform dx γ₂) % 2 = 0 ∧
    iform da db = -1 ∧ iform da γ₁ = 0 ∧ iform da γ₂ = 0 ∧ iform db γ₁ = 0 ∧ iform db γ₂ = 0 ∧
    iform da dx = 0 ∧ iform db dx = 0) ∧
  (∀ i : Fin (Tag.rank .E7), iform ρ (Pi.single i 1) % 2 =
    (iform γ₁ (Pi.single i 1) + iform γ₂ (Pi.single i 1)) % 2) ∧
  (iform ρ δm = 0 ∧ iform ρ δn = 0 ∧ iform δm δn = -1 ∧
    (iform δm γ₁ + iform δm γ₂) % 2 = 0 ∧ (iform δn γ₁ + iform δn γ₂) % 2 = 0)

private theorem r2w_1 : R2W 1 (vec [-2,-2,-3,-4,-3,-2,-1]) (vec [0,0,-1,-1,-1,-1,-1])
    (vec [1,0,0,0,0,0,0]) (vec [0,0,0,-1,-1,-1,0])
    (vec [0,0,0,0,0,1,0]) (vec [0,1,0,1,1,1,1])
    (vec [-1,-1,-2,-3,-3,-2,-1]) (vec [-1,-1,-1,-1,0,0,0]) := by
  unfold R2W; decide +kernel

private theorem r2w_4 : R2W 4 (vec [-1,-2,-2,-3,-2,-2,-1]) (vec [-1,-1,-2,-3,-2,-1,-1])
    (vec [0,0,0,0,0,1,0]) (vec [-1,-1,-2,-2,-2,-1,0])
    (vec [0,0,1,0,0,0,0]) (vec [0,0,0,0,1,1,1])
    (vec [-2,-2,-3,-4,-3,-2,-1]) (vec [1,0,0,0,0,0,0]) := by
  unfold R2W; decide +kernel

theorem exists_r1_roots (p₀ : Fin 7) (h : p₀ = 0 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 5) :
    ∃ γ c l₁ l₂ l₃ : Fin 7 → ℤ,
      γ ∈ (D7 p f).roots ∧ c ∈ (D7 p f).roots ∧ l₁ ∈ (D7 p f).roots ∧ l₂ ∈ (D7 p f).roots ∧
      l₃ ∈ (D7 p f).roots ∧
      ((γ p₀ : ℤ) : ZMod 2) = 0 ∧ ((c p₀ : ℤ) : ZMod 2) = 0 ∧ ((l₁ p₀ : ℤ) : ZMod 2) = 0 ∧
      ((l₂ p₀ : ℤ) : ZMod 2) = 0 ∧ ((l₃ p₀ : ℤ) : ZMod 2) = 0 ∧
      iform (τ := .E7) γ c = 0 ∧ iform (τ := .E7) γ l₁ = 0 ∧ iform (τ := .E7) γ l₂ = 0 ∧
      iform (τ := .E7) γ l₃ = 0 ∧ iform (τ := .E7) c l₁ = -1 ∧ iform (τ := .E7) c l₂ = -1 ∧
      iform (τ := .E7) c l₃ = -1 ∧ iform (τ := .E7) l₁ l₂ = 0 ∧ iform (τ := .E7) l₁ l₃ = 0 ∧
      iform (τ := .E7) l₂ l₃ = 0 := by
  have key : ∃ γ c l₁ l₂ l₃ : V7, R1W p₀ γ c l₁ l₂ l₃ := by
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨_, _, _, _, _, r1w_0⟩
    · exact ⟨_, _, _, _, _, r1w_2⟩
    · exact ⟨_, _, _, _, _, r1w_3⟩
    · exact ⟨_, _, _, _, _, r1w_5⟩
  obtain ⟨γ, c, l₁, l₂, l₃, ⟨m₁, m₂, m₃, m₄, m₅⟩, ⟨f₁, f₂, f₃, f₄, f₅⟩,
    ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉, r₁₀⟩⟩ := key
  exact ⟨γ, c, l₁, l₂, l₃, (mem_roots_D7_iff p f _).2 m₁, (mem_roots_D7_iff p f _).2 m₂,
    (mem_roots_D7_iff p f _).2 m₃, (mem_roots_D7_iff p f _).2 m₄, (mem_roots_D7_iff p f _).2 m₅,
    f₁, f₂, f₃, f₄, f₅, r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉, r₁₀⟩

theorem exists_r2_roots (p₀ : Fin 7) (h : p₀ = 1 ∨ p₀ = 4) :
    ∃ γ₁ γ₂ dx da db ρ δm δn : Fin 7 → ℤ,
      γ₁ ∈ (D7 p f).roots ∧ γ₂ ∈ (D7 p f).roots ∧ dx ∈ (D7 p f).roots ∧ da ∈ (D7 p f).roots ∧
      db ∈ (D7 p f).roots ∧ ρ ∈ (D7 p f).roots ∧ δm ∈ (D7 p f).roots ∧ δn ∈ (D7 p f).roots ∧
      ((γ₁ p₀ : ℤ) : ZMod 2) = 0 ∧ ((γ₂ p₀ : ℤ) : ZMod 2) = 0 ∧ ((dx p₀ : ℤ) : ZMod 2) = 0 ∧
      ((da p₀ : ℤ) : ZMod 2) = 0 ∧ ((db p₀ : ℤ) : ZMod 2) = 0 ∧ ((ρ p₀ : ℤ) : ZMod 2) ≠ 0 ∧
      ((δm p₀ : ℤ) : ZMod 2) ≠ 0 ∧
      iform (τ := .E7) γ₁ γ₂ = 0 ∧ iform (τ := .E7) dx γ₁ = -1 ∧
      (iform (τ := .E7) dx γ₁ + iform (τ := .E7) dx γ₂) % 2 = 0 ∧
      iform (τ := .E7) da db = -1 ∧ iform (τ := .E7) da γ₁ = 0 ∧ iform (τ := .E7) da γ₂ = 0 ∧
      iform (τ := .E7) db γ₁ = 0 ∧ iform (τ := .E7) db γ₂ = 0 ∧ iform (τ := .E7) da dx = 0 ∧
      iform (τ := .E7) db dx = 0 ∧
      (∀ i : Fin 7, iform (τ := .E7) ρ (Pi.single i 1) % 2 =
        (iform (τ := .E7) γ₁ (Pi.single i 1) + iform (τ := .E7) γ₂ (Pi.single i 1)) % 2) ∧
      iform (τ := .E7) ρ δm = 0 ∧ iform (τ := .E7) ρ δn = 0 ∧ iform (τ := .E7) δm δn = -1 ∧
      (iform (τ := .E7) δm γ₁ + iform (τ := .E7) δm γ₂) % 2 = 0 ∧
      (iform (τ := .E7) δn γ₁ + iform (τ := .E7) δn γ₂) % 2 = 0 := by
  have key : ∃ γ₁ γ₂ dx da db ρ δm δn : V7, R2W p₀ γ₁ γ₂ dx da db ρ δm δn := by
    rcases h with rfl | rfl
    · exact ⟨_, _, _, _, _, _, _, _, r2w_1⟩
    · exact ⟨_, _, _, _, _, _, _, _, r2w_4⟩
  obtain ⟨γ₁, γ₂, dx, da, db, ρ, δm, δn, ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈⟩,
    ⟨f₁, f₂, f₃, f₄, f₅, g₁, g₂⟩, ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉, r₁₀⟩, hρ,
    ⟨s₁, s₂, s₃, s₄, s₅⟩⟩ := key
  exact ⟨γ₁, γ₂, dx, da, db, ρ, δm, δn, (mem_roots_D7_iff p f _).2 m₁,
    (mem_roots_D7_iff p f _).2 m₂, (mem_roots_D7_iff p f _).2 m₃, (mem_roots_D7_iff p f _).2 m₄,
    (mem_roots_D7_iff p f _).2 m₅, (mem_roots_D7_iff p f _).2 m₆, (mem_roots_D7_iff p f _).2 m₇,
    (mem_roots_D7_iff p f _).2 m₈, f₁, f₂, f₃, f₄, f₅, g₁, g₂, r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈,
    r₉, r₁₀, hρ, s₁, s₂, s₃, s₄, s₅⟩

end CFSG.ClassicalInvolution.RouteD.TypeE8
