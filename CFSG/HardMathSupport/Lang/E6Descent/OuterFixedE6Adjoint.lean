module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Fixed

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Generic

variable {G : Type*} [Group G]

theorem fixedSubgroup_le_pow (α : MulAut G) (n : ℕ) : fixedSubgroup α ≤ fixedSubgroup (α ^ n) := by
  intro x hx
  have hfix : α x = x := hx
  show (α ^ n) x = x
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, hfix]
    exact ih

theorem card_fixedSubgroup_conj (ψ β : MulAut G) :
    Nat.card (fixedSubgroup (ψ * β * ψ⁻¹)) = Nat.card (fixedSubgroup β) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv ψ.toEquiv ?_)).symm
  intro x
  show β x = x ↔ (ψ * β * ψ⁻¹) (ψ x) = ψ x
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, ψ.symm_apply_apply]
  exact ⟨fun h => by rw [h], fun h => ψ.injective h⟩

theorem fixedSubgroup_pow_eq {α : MulAut G} {r j : ℕ} (hαr : (α ^ r) ^ j = α) :
    fixedSubgroup α = fixedSubgroup (α ^ r) :=
  le_antisymm (fixedSubgroup_le_pow α r) (by
    have := fixedSubgroup_le_pow (α ^ r) j
    rwa [hαr] at this)

end Generic


section Main

theorem outerFixedOrder_adjointE6
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd 3 (ℓ ^ f - 1))
    (α : MulAut (adjointGroup Tag.E6 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.E6 K)) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .E6 0 (ℓ ^ f₀) := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  obtain ⟨d, T, r, j, ψ, hd, -, hcard, -, -, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_not_innerDiag .E6 (Or.inl rfl) hf K hK hp hp2 α hαp fun g a h => by
      obtain ⟨h3, hq⟩ := prime_dvd_of_diag_noninner .E6 (Or.inl rfl) K hp g a α h hαp hα
      have h3' : p ∣ 3 := by rw [det_cartan_E6] at h3; exact h3
      exact hdiv (Nat.dvd_gcd h3' (by rwa [hK] at hq))
  refine ⟨d, hd, ?_⟩
  rw [fixedSubgroup_pow_eq hαβ, ← card_fixedSubgroup_conj ψ (α ^ r), hψ,
    card_fixedSubgroup_entrywiseAdjointAut]
  exact card_entrywiseFixedGroup_E6_dvd T hcard

end Main

end CFSG.HardMathSupport.Lang.E6Descent
