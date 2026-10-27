module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddDict
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Fischer CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec11
  CFSG.RankThree.PartTwo.Sec19

section Statements


@[expose] def TriOddIsClassY {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (x : C0 σ) : Prop :=
  ∃ h : C0 σ, h * x * h⁻¹ ∈ Bsub σ

@[expose] def TriOddIsClassX {X : Type} [Field X] [Finite X] (σ : X ≃+* X) (x : C0 σ) : Prop :=
  ∃ h : C0 σ, h * x * h⁻¹ ∈ Asub σ

@[expose] def TriOddYGLine : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (E : Subgroup (MulAut (C0 σ))) (x : C0 σ), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (C0 σ) → x ^ 3 = 1 → x ≠ 1 → MulAut.conj x ∈ E →
      TriOddIsClassY σ x → TriOddHasGLine σ E

@[expose] def TriOddXNoG : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (E : Subgroup (MulAut (C0 σ))) (x : C0 σ), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (C0 σ) → ¬ TriOddHasGLine σ E → x ^ 3 = 1 →
      x ≠ 1 → MulAut.conj x ∈ E → TriOddIsClassX σ x →
      Subgroup.closure (fixUnion E) = ⊤

end Statements

section Glue


theorem triOddNoGLine_of_YX (hY : TriOddYGLine) (hX : TriOddXNoG) : TriOddNoGLine := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ E hE hc hout hng
  obtain ⟨x, hx3, hx1, g, e, -, -, -, hEeq⟩ :=
    triOdd_plane_shape σ hℓ hℓ2 hf hK hσ E hE hc hout
  have hcx : MulAut.conj x ∈ E := by
    rw [hEeq]; exact Subgroup.subset_closure (by simp)
  have h3q : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)).symm)
  obtain ⟨h, hh⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds K (ℓ ^ f) σ hK hσ
    h3q x hx3 hx1
  rcases hh with hA | hB
  · exact hX ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ E x hE hc hout hng hx3 hx1 hcx ⟨h, hA⟩
  · exact absurd (hY ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ E x hE hc hout hx3 hx1 hcx ⟨h, hB⟩) hng

end Glue

section Final


theorem trialityThreePlanesOdd_of_open (hY : TriOddYGLine) (hX : TriOddXNoG) :
    TrialityThreePlanesOdd :=
  triOdd_trialityThreePlanesOdd_of_two triOddJPlanes (triOddNoGLine_of_YX hY hX)

end Final

end CFSG.LieType.SeitzGeneration.ExcWideThree
