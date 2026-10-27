module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKG
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndInputs

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank

@[expose] def EndKnownGroupsInputOn (C : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → C X →
    ∀ (z t : X) (K P D : Subgroup X), IsTwoComponentAt z K →
      (∀ K₂ : Subgroup X, IsTwoComponentAt z K₂ → K₂ = K) →
      IsSimpleGroup (K ⧸ pPrimeCore 2 K) → FooteFamilyType K →
      IsEmpty (X ≃* K ⧸ pPrimeCore 2 K) → IsSylowOf 2 P K → t ∈ P → orderOf t = 2 →
      z * t = t * z → z ∈ D → D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K →
      P ≤ centralizer (D : Set X) → AschbacherTheorem3.IsDihedralTwoGroup D → 8 ≤ Nat.card D →
      Group.IsSolvable ↥(centralizer ({z} : Set X) ⊓ centralizer (K : Set X)) →
      (∀ b ∈ D, orderOf b = 2 → ∃ Y : Subgroup X, IsTwoComponentAt b Y ∧ P ≤ Y ∧
        Nonempty (Y ⧸ pPrimeCore 2 Y ≃* K ⧸ pPrimeCore 2 K)) →
      ¬ Group.IsSolvable ↥(centralizer ({z * t} : Set X))

theorem endKnownGroupsInputOn_oddLieType (h : Sol78.F514.EndOddLieInput) :
    EndKnownGroupsInputOn fun X _ => Blueprint.OddLieType X :=
  h

theorem endKnownGroupsInputOn_cyclic : EndKnownGroupsInputOn fun X _ =>
    ∃ q : ℕ, q.Prime ∧ Nonempty (X ≃* Multiplicative (ZMod q)) := by
  intro X _ _ _ hX z t K P D hK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exfalso
  obtain ⟨q, -, ⟨e⟩⟩ := hX
  have hcomm : ∀ x y : X, x * y = y * x := fun x y => e.injective (by
    rw [map_mul, map_mul, mul_comm])
  obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_quotient_of_isPComponent hK.2.1 hK.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 2
  exact Subtype.ext (hcomm a b)

theorem endKnownGroupsInput_of_families (hodd : Sol78.F514.EndOddLieInput)
    (heven : EndKnownGroupsInputOn fun X _ => ∃ (τ : StatedLieTag) (n f : ℕ),
      StatedLieAdmissible τ n 2 f ∧ Blueprint.LieModel X τ n 2 f)
    (halt : EndKnownGroupsInputOn fun X _ =>
      ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n)))
    (hspor : EndKnownGroupsInputOn fun X _ => Blueprint.NativeSporadic.SporadicRep X) :
    EndKnownGroupsInput := by
  intro X _ _ hX hcat
  rcases RankThree.PartOne.PlaneCases.catalog_cases hcat with hab | hA | ⟨τ, n, ℓ, f, hadm, hmod⟩ |
    hsp
  · exact endKnownGroupsInputOn_cyclic X hX hab
  · exact halt X hX hA
  · by_cases hℓ : ℓ = 2
    · subst hℓ
      exact heven X hX ⟨τ, n, f, hadm, hmod⟩
    · exact hodd X hX ⟨τ, n, ℓ, f, hadm.1, hℓ, hadm, hmod⟩
  · exact hspor X hX hsp

end CFSG.ComponentClassification.Foote5
