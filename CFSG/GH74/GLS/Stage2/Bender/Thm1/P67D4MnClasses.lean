module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnNF

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4Minus_outer_three_nf {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφord : orderOf φ = 3)
    (hφout : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    (∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj y * φ * (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
      MulAut.conj y * φ * (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹) ∨
    (∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, D4MinusToral p f hp K σ s ∧
      (MulAut.conj y * φ * (MulAut.conj y)⁻¹ =
          MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∨
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ =
          (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)⁻¹)) ∨
    (∃ y n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, D4MinusElliptic p f hp K σ n ∧
      (MulAut.conj y * φ * (MulAut.conj y)⁻¹ =
          MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ ∨
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ =
          (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ)⁻¹)) := by
  obtain ⟨g, hg, hφ | hφ⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ φ hφord hφout
  · rcases d4MinusNF p f hp hp2 hp3 hf hq K hK σ hσ g hg with ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ |
        ⟨y, n, hn, hyn⟩
    · exact Or.inl ⟨y, Or.inl (by rw [hφ]; exact hy)⟩
    · exact Or.inr (Or.inl ⟨y, s, hs, Or.inl (by rw [hφ]; exact hys)⟩)
    · exact Or.inr (Or.inr ⟨y, n, hn, Or.inl (by rw [hφ]; exact hyn)⟩)
  · have hinv : ∀ (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = (MulAut.conj y * φ⁻¹ * (MulAut.conj y)⁻¹)⁻¹ :=
      fun y => by group
    rcases d4MinusNF p f hp hp2 hp3 hf hq K hK σ hσ g hg with ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ |
        ⟨y, n, hn, hyn⟩
    · exact Or.inl ⟨y, Or.inr (by rw [hinv, hφ, hy])⟩
    · exact Or.inr (Or.inl ⟨y, s, hs, Or.inr (by rw [hinv, hφ, hys])⟩)
    · exact Or.inr (Or.inr ⟨y, n, hn, Or.inr (by rw [hinv, hφ, hyn])⟩)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
