module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Transport
public import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GorensteinWalter (PSL2)
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut)
open CFSG.RankThree.PartOne.FOC
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)


theorem psl_two_field_case {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (ζ : MulAut (projectiveSL 2 K)) (hζ3 : ζ ^ 3 = 1)
    (hζinn : ζ ∉ innerAut (projectiveSL 2 K)) :
    (∃ D : Subgroup (projectiveSL 2 K), (∀ x ∈ D, ζ x = x) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D) ∨
      Nat.card (fixSub ζ) ∣ 24 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ζ = 3 :=
    orderOf_eq_prime hζ3 fun h1 => hζinn (h1 ▸ (innerAut (projectiveSL 2 K)).one_mem)
  let ψ : projectiveSL 2 K ≃* coordinateG K :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm.trans (pslEquivCoordinateG K)
  obtain ⟨-, k, hkcard, ⟨eX⟩⟩ :=
    psl_two_fixSub_equiv_gen hℓ Nat.prime_three (by norm_num) hf hK ψ hord hζinn
  by_cases h4 : 4 ≤ Nat.card k
  · left
    have : Fintype ↥k := Fintype.ofFinite ↥k
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset ↥k)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    have hperf : Group.IsPerfect (PSL2 ↥k) :=
      CFSG.LinearGroups.linear_projective_perfect (n := 2) le_rfl (Or.inr ⟨t, ht⟩)
    let e : ↥(fixSub ζ) ≃* PSL2 ↥k := eX.trans (pslEquivCoordinateG ↥k).symm
    refine ⟨fixSub ζ, fun x hx => hx, commutator_eq_self_of_equiv_perfect _ e, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_congr
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 ↥k).toEquiv,
      Nat.card_congr (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 2 ↥k).toEquiv]
    exact CFSG.Quasithin.three_dvd_card_psl (K := ↥k) le_rfl
  · right
    have h1 : Nat.card (fixSub ζ) ∣ Nat.card (Equiv.Perm (Omega ↥k)) := by
      rw [Nat.card_congr eX.toEquiv]
      exact Subgroup.card_subgroup_dvd_card (coordinateG ↥k)
    have h5 : Nat.card (Omega ↥k) = Nat.card ↥k + 1 := by simp [Omega]
    have hk : Nat.card ↥k ≤ 3 := by omega
    have h6 : Nat.card (Equiv.Perm (Omega ↥k)) ∣ 24 := by
      rw [Nat.card_perm, h5]
      interval_cases Nat.card ↥k <;> decide
    exact h1.trans h6

end CFSG.HardMathSupport.Malle.E27Lie
