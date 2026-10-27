module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitary
public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryGWStep

public section

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField CFSG.Semidihedral.UnitaryDValue

@[expose] def DValueCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (D : DValueData G), D.CharacterExtend →
    D.CharacterTrivial → D.PrincipalPair → D.GWStep →
    D.m * Nat.card D.A * Nat.gcd (D.q + 1) 3 = D.q + 1

@[expose] def WreathedCharacterTrivialStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SmallerWreathedRecognition G →
    ∀ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)),
      ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 ≤ p ^ f → p ^ f % 4 = 3 →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f →
      OriginalAllPrimeStationarity n S e → OriginalAllPrimeCoverage n S e →
    ∀ θ : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) →* ℂˣ,
      (∀ c : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G),
        (c : G) ∈ (S : Subgroup G) → θ c = 1) →
      (∀ g ∈ Subgroup.normalizer ((Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
          wreathModelHom S e (Original.x2 (2 ^ n))} : Subgroup G) : Set G),
        ∀ c c' : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G),
          (c : G) ∈ Subgroup.centralizer ((Subgroup.closure
            {wreathModelHom S e (Original.x (2 ^ n)), wreathModelHom S e (Original.x2 (2 ^ n))} :
              Subgroup G) : Set G) →
          (c' : G) = g * c * g⁻¹ → θ c' = θ c) →
      ∀ c : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G), θ c = 1

theorem dValue_of_core
    (hcore : DValueCoreStatement) (htriv : WreathedCharacterTrivialStatement) :
    DValueStatement := by
  intro G _ _ _ hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨D, hDp, hDf, hDm, hDx, hDz, hDS, hDA, hext, hpair, hgw⟩ :=
    exists_dValueData_gwStep hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  have htriv' : D.CharacterTrivial := by
    unfold DValueData.CharacterTrivial
    rw [hDx, hDz, hDS]
    exact htriv G hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  have h := hcore G D hext htriv' hpair hgw
  have hq : D.q = p ^ f := by
    show D.p ^ D.f = p ^ f
    rw [hDp, hDf]
  rw [hDm, hDA, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hq] at h
  rw [Nat.mul_comm (Nat.card (centralizerOddCore n S e)) (2 ^ n)]
  exact h

theorem unitaryBranch_of_core
    (hcore : DValueCoreStatement)
    (htriv : WreathedCharacterTrivialStatement) :
    CFSG.Wreathed.RecognitionFromGaps.UnitaryBranchStatement :=
  unitaryBranch_of_dValue (dValue_of_core hcore htriv)

end CFSG.Wreathed.SameFieldUnitary
