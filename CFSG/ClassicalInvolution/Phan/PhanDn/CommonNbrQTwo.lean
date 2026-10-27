module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipEmb
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoDensity

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem FlipEmb.exists_isFlipflopPt_orth_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (φ : FlipEmb σ 3 n)
    (y : Fin n ⊕ Fin n → K) :
    ∃ p, IsFlipflopPt σ p ∧ p ≤ LinearMap.range φ.toLinearMap ∧
      ∀ v ∈ p, polar (quadPlus n K) v y = 0 ∧ flipHerm σ v y = 0 := by
  obtain ⟨f, hf⟩ := φ.exists_adjoint hσ.invol y
  obtain ⟨p₀, hp₀, horth⟩ := exists_flipflopPt_orth_of_card_eq_four hσ hK f
  refine ⟨p₀.map φ.toLinearMap, φ.isFlipflopPt_map hp₀, LinearMap.map_le_range, ?_⟩
  intro v hv
  obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
  exact ⟨(hf v₀).1.trans (horth v₀ hv₀).1, (hf v₀).2.trans (horth v₀ hv₀).2⟩

theorem exists_isFlipflopPt_orth_orth_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) {X : Submodule K (Fin n ⊕ Fin n → K)}
    (hX : IsFlipflopSub σ X) (hd : Module.finrank K X + 3 ≤ n) (y : Fin n ⊕ Fin n → K) :
    ∃ p, IsFlipflopPt σ p ∧ p ≤ qPerp n K X ∧ p ≤ flipOrth σ X ∧
      ∀ v ∈ p, polar (quadPlus n K) v y = 0 ∧ flipHerm σ v y = 0 := by
  obtain ⟨φ, hφ⟩ := exists_flipEmb_orth hσ hX hd
  obtain ⟨p, hp, hprange, hporth⟩ :=
    FlipEmb.exists_isFlipflopPt_orth_of_card_eq_four hσ hK φ y
  refine ⟨p, hp, ?_, ?_, hporth⟩
  · intro v hv
    rw [mem_qPerp]
    intro w hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp (hprange hv)
    exact (hφ x w hw).1
  · intro v hv
    rw [mem_flipOrth]
    intro w hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp (hprange hv)
    exact (hφ x w hw).2

end CFSG.ClassicalInvolution.PhanDn
