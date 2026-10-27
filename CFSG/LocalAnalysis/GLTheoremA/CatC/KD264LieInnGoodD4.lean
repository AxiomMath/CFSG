module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedD4

public section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal.Spin CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.D4Three
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


@[expose] def D4GraphPerfect : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 3 → Nat.card F ≠ 2 →
    ∀ (g : adjointGroup Tag.D4 F) (a : Fin Tag.D4.rank → Fˣ) (ε : ℕ), (ε = 1 ∨ ε = 2) →
      (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε)) ^ 3 = 1 →
      ∃ P : Subgroup (adjointGroup Tag.D4 F),
        P ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε)) ∧
        ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P

theorem innGoodAt_D4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpc : p ≠ (TauCeti.LieTypeIndex.D 4 q).characteristic) (h32 : ¬ (p = 3 ∧ q.card = 2))
    (hgr : p = 3 → D4GraphPerfect) :
    InnGoodAt p (.D 4 q) (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group := by
  classical
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hFcard : Nat.card F = q.p ^ q.exponent := by
    change Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) =
      q.p ^ q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_D, TauCeti.LieTypeIndex.fieldExponent_D]
  have hcharD : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p :=
    TauCeti.LieTypeIndex.characteristic_D 4 q
  have hcharF : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hFcard
  have hpℓ : p ≠ q.p := fun h => hpc (by rw [hcharD, h])
  have hpl : p ≠ ringChar F := by rw [hcharF]; exact hpℓ
  have h3 : p = 3 → 4 ≤ Nat.card F := fun hp3 =>
    four_le_card_of_ringChar_ne_three (fun h => hpl (hp3.trans h.symm))
      (fun h2 => h32 ⟨hp3, by rw [TauCeti.PrimePower.card_def, ← hFcard]; exact h2⟩)
  obtain ⟨hreg, hregT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := 4) (by omega)
  have hplanes : PerfectCentralizerPlanes p (ProjOrthDerived (quadPlus 4 F)) :=
    perfectCentralizerPlanes_projOrthDerived hreg hregT hp hp2 hpl h3
  obtain ⟨eP⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadPlus 4 F)
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  have hplanesC : PerfectCentralizerPlanes p (adjointGroup Tag.D4 F) :=
    PerfectCentralizerPlanes.of_mulEquiv (eP.symm.trans eC) hplanes
  have hcoord : InnGoodAt p (.D 4 q) (adjointGroup Tag.D4 F) := by
    intro D hD hcard hDle
    by_cases hDi : D ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup Tag.D4 F)
    · exact Or.inl (exists_good_of_le_inner center_adjointGroup_eq_bot hplanesC hD hcard hDi)
    · obtain ⟨β, hβD, hβni⟩ := SetLike.not_le_iff_exists.mp hDi
      have hβp : β ^ p = 1 := hD.2 β hβD
      have hp3 : p = 3 := by
        by_contra hp3
        obtain ⟨h, hh⟩ := exists_conj_eq_of_mem_innAutDerived_D4 hp hp2 hp3 (hDle hβD) hβp
        exact hβni ⟨h, hh.symm⟩
      subst hp3
      have hβ3 : β ^ 3 = 1 := by simpa using hβp
      rcases innAutDerived_D4_three_cases (hDle hβD) hβ3 with ⟨h, hh⟩ | ⟨g, a, ε, hε, hβeq⟩
      · exact absurd ⟨h, hh.symm⟩ hβni
      · have hq3 : q.p ≠ 3 := by
          intro hq
          exact hpc (by rw [hcharD]; exact hq.symm)
        have hF3 : ringChar F ≠ 3 := by
          rw [hcharF]
          exact hq3
        have hF2 : Nat.card F ≠ 2 := by
          intro h2
          exact h32 ⟨rfl, by rw [TauCeti.PrimePower.card_def, ← hFcard]; exact h2⟩
        have hα : (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε)) ^ 3 = 1 := by
          rw [← hβeq]
          exact hβ3
        obtain ⟨P, hPfix, hPperf, hPdvd⟩ :=
          hgr rfl F hF3 hF2 g a ε hε hα
        refine Or.inl ⟨β, hβD, ?_, P, ?_, hPperf, hPdvd⟩
        · intro h1
          exact hβni (h1 ▸ one_mem _)
        · rw [hβeq]
          exact hPfix
  have e₁ := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid
    4 q hv
  have e₂ := (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
    F).some
  exact innGoodAt_of_mulEquiv (e₁.trans e₂).symm hcoord

theorem lieInnGood_D4_of_graph (hgr : D4GraphPerfect) :
    LieInnGood fun d => ∃ q, d = .D 4 q := by
  intro d p hp hp2 hpc h3 h5 hd
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, hq⟩ := hd
  change idx = .D 4 q at hq
  subst hq
  have h32 : ¬ (p = 3 ∧ q.card = 2) := by
    rintro ⟨hp3, h2⟩
    exact h3 ⟨hp3, by
      show fieldSize (.D 4 q) = 2
      rw [show fieldSize (.D 4 q) = q.card by simp [fieldSize]]
      exact h2⟩
  exact innGoodAt_D4 q hv hp hp2 hpc h32 (fun _ => hgr)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
