module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeNF
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2D4Leaf

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Generic

variable {Y : Type} [Group Y]

@[expose] def D4Out (φ : MulAut Y) : Prop := D4NoAbel φ ∧ D4PtKer φ

theorem D4Out.conj {φ : MulAut Y} (h : D4Out φ) (β : MulAut Y) : D4Out (β * φ * β⁻¹) :=
  ⟨h.1.conj β, h.2.conj β⟩

theorem D4Out.inv {φ : MulAut Y} (h : D4Out φ) : D4Out φ⁻¹ := ⟨h.1.inv, h.2.inv⟩

theorem D4Out.of_conj_eq {φ ψ : MulAut Y} (h : D4Out ψ) (β : MulAut Y)
    (hφ : β * φ * β⁻¹ = ψ) : D4Out φ := by
  have h1 := h.conj β⁻¹
  have h2 : β⁻¹ * ψ * β⁻¹⁻¹ = φ := by
    rw [← hφ]
    group
  rwa [h2] at h1

end Generic

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def D4OuterThreeG2 : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
      D4Out (fieldActor (t := TwistTag.D4) σ σ)

@[expose] def D4OuterThreeRest : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), orderOf φ = 3 →
      φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      (¬ ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹) →
      D4Out φ

theorem d4OuterThree_of_G2_rest (hG2 : D4OuterThreeG2) (hR : D4OuterThreeRest) :
    D4OuterThree := by
  intro p f hp hp2 hp3 hf K _ _ hK σ hσ φ hφord hφout
  by_cases hconj : ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj y * φ * (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
      MulAut.conj y * φ * (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹
  · obtain ⟨y, hy | hy⟩ := hconj
    · exact (hG2 p f hp hp2 hp3 hf K hK σ hσ).of_conj_eq _ hy
    · exact ((hG2 p f hp hp2 hp3 hf K hK σ hσ).inv).of_conj_eq _ hy
  · exact hR p f hp hp2 hp3 hf K hK σ hσ φ hφord hφout hconj

@[expose] def D4CocycleNF : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1 →
      ∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧
        MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ

end CFSG.GH74.GLS.Stage2.Bender.Thm1
