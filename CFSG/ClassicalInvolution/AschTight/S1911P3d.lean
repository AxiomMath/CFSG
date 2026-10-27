module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.AschTight.S1911FusF
public import CFSG.ClassicalInvolution.AschTight.S1911SecA

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

@[expose] def IsT6Tag (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k : ℕ) : Prop :=
  (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨ (t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)

@[expose] def FactM0 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ), IsT6Tag t k →
        Nonempty (Ih8Model p e Ω t k e') →
        ∀ φ : MulAut E, φ * φ = 1 → (∀ L ∈ Ω, L.map φ.toMonoidHom ∈ Ω) →
          ∃ L ∈ Ω, L.map φ.toMonoidHom = L

@[expose] def FactM1 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
        ((t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) → Nonempty (Ih8Model p e Ω t k e') →
        ∀ φ : MulAut E, φ * φ = 1 → (∀ L ∈ Ω, L.map φ.toMonoidHom ∈ Ω) →
          ∀ L ∈ Ω, L.map φ.toMonoidHom = L →
            (∀ P : Subgroup E, IsPGroup 2 P → P ≤ L → (∀ x ∈ P, φ x = x) →
              ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
            ∃ x : E, φ = MulAut.conj x

@[expose] def FactM2 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ), IsT6Tag t k →
        Nonempty (Ih8Model p e Ω t k e') → Ω.Nonempty →
        ∀ x : E, x * x = 1 → x ≠ 1 → ∃ L ∈ Ω, IsUniqueInvolution L x

@[expose] def FactM3 : Prop :=
  ∀ (p e : ℕ) (hp : p.Prime), p ≠ 2 → ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k : ℕ),
    IsT6Tag t k → CFSG.Assembly.LowTwoRank.StatedLieAdmissible t k p e →
      Odd (Nat.card (Subgroup.center (Generic.modelUniv t k p e hp).K))

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_16FusL3GraphTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W → p ^ f ≠ 9 →
      ∀ a ∈ (S : Subgroup G), a * a = 1 → a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K →
        ∀ e₀ : ℕ, (SectionLieType p e₀ (conjFamily (perfectCoreIn K a))
            (conjGen (perfectCoreIn K a)) .PSL 3 ∨ SectionLieType p e₀
              (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .PSU 3) →
          ∀ s : ↥(Subgroup.centralizer ({a} : Set G)), (∃ g : G, (s : G) = g * z * g⁻¹) →
            (s : G) * z = z * (s : G) →
            ∃ y ∈ conjGen (perfectCoreIn K a), ∀ x ∈ conjGen (perfectCoreIn K a),
              (s * y⁻¹) * x * (s * y⁻¹)⁻¹ * x⁻¹ ∈ oddCoreOf (conjGen (perfectCoreIn K a))

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
