module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81U

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

structure Stage7 (d : Data H₁) (v : H) : Prop where
  facts : d.Facts
  isV : d.IsV v
  not_b_bz : ∀ c : H, c⁻¹ * d.b * c ≠ d.b * d.z
  conj_asigma : ∃ c : H, c⁻¹ * (h.a * d.sigma) * c = d.z * d.sigma
  card_P : Nat.card h.P = Nat.card h.D
  P_le_F : h.P ≤ h.F32
  dihedral : d.b * d.p * d.b⁻¹ = d.p⁻¹
  fusion : ∀ π ∈ h.P, π * π = 1 → π ≠ 1 → π ≠ h.a → ∃ c : H, c⁻¹ * d.b * c = π
  y : ∃ y ∈ h.S, y⁻¹ * h.a * y = h.a ∧ y⁻¹ * d.z * y = d.z ∧
    y⁻¹ * d.sigma * y = h.a * d.z * d.sigma ∧
    (∃ e ∈ h.D, y * e * y⁻¹ * e⁻¹ ∉ ⁅h.D, h.D⁆) ∧
    ∃ π ∈ h.P, y * π * y⁻¹ * π⁻¹ ∉ zpowers (d.p ^ 2)

end Data

end L81Hyp

end Hyp59

@[expose] def GS81Step3Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data), d.Facts →
    (∀ c : H, c⁻¹ * h.a * c ≠ d.b) → (∃ c : H, c⁻¹ * d.b * c = d.b * d.z) →
    HasNormalPComplement 2 ↥(centralizer ({h.a} : Set H) ⊓ centralizer ({d.b * d.z} : Set H))

@[expose] def GS81Step8Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8)) →
      ∃ A : Subgroup H, A ≤ h.U81 v ⊓ centralizer ({h.a * d.sigma} : Set H) ∧
        (∀ e ∈ A, e * e = 1) ∧ Nat.card A = 32 ∧
        ∀ t ∈ A ⊓ coreActionKernel h.J, t ∉ zpowers (h.a * d.sigma) →
          (∃ c : H, c⁻¹ * h.a * c = t) ∨ (∃ c : H, c⁻¹ * d.sigma * c = t)

@[expose] def GS81Step9Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f →
      layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ ∧
        (p ^ f = 3 →
          centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) =
            (oddCoreIn (centralizer ({h.a} : Set H)) ⊓ centralizer ({h.a * d.z} : Set H)) ⊔
              h.S)

end CFSG.ComponentClassification.GSThmB
