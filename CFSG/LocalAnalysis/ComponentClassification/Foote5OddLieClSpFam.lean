module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpDisp

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem conj_injective_of_center_eq_bot {T : Type*} [Group T] (h : center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← h, mem_center_iff]
  intro g
  have hg : x * g * x⁻¹ = g := by
    have := congrArg (fun φ : MulAut T => φ g) (MonoidHom.mem_ker.1 hx)
    simpa [MulAut.conj_apply] using this
  calc g * x = x * g * x⁻¹ * x := by rw [hg]
    _ = x * g := by group

theorem ClSp.commute_psp {r : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hKc : Nat.card K = p ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    (h4 : ClSp.SpFourThreeSkewInput) (i : MulAut (StatedProj (StatedSp r K)))
    (hi : orderOf i = 2) {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * i = i * y)
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨A, σ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr i
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hi hRi hRc
    exact ClSp.commute_inner hp hp2 hf hKc hr hinj h4 hi hRodd hRi hRc
  · exact ClSp.commute_field hp hp2 hf hKc hr hinj hσ hi hRodd hRi hRc

theorem oddLieCoreFamilyInput_psp_of (h4 : ClSp.SpFourThreeSkewInput) :
    OddLieCoreFamilyInput .PSp := by
  intro S _ _ _ hna n p f hp hp2 hadm hm hL2 i hi R hRodd hRi hRc
  obtain ⟨-, hf, hn, -⟩ := hadm
  have hcl : StatedClassicalModel S .PSp n p f := by
    rcases hm with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  obtain ⟨-, K, _, _, hKc, ⟨θ⟩⟩ := hcl
  have hZ := center_eq_bot_of_mulEquiv θ (center_eq_bot_of_simple hna)
  refine commute_of_congr θ (fun R' hR'odd hR'i hR'c =>
    ClSp.commute_psp hp hp2 hf hKc hn (conj_injective_of_center_eq_bot hZ) h4 _ ?_ hR'odd hR'i
      hR'c) hRodd hRi hRc
  rw [MulEquiv.orderOf_eq]
  exact hi

end CFSG.ComponentClassification.Foote5.OddLieCore
