module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCyc
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
public import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
public import CFSG.RankThree.PartOne.MB3.OddOutExceptional
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.NormalForm
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.TriD4
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterD4Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart

theorem outPNice_statedClassicalModel_PSp {p n r m : ℕ} {X : Type} [Group X]
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (h : StatedClassicalModel X .PSp n r m) : OutPNice p X := by
  by_cases hr : r = 2
  · subst hr
    by_cases hn2 : n = 2
    · subst hn2
      exact outPNice_PSp_two hp h
    · exact outPNice_PSp_ge_three hp (by omega) h
  · by_cases hn2 : n = 2
    · subst hn2
      exact CFSG.RankThree.PartOne.AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hr h
    · exact outPNice_PSp_ge_three_odd hp hp2 (by omega) h

theorem outCycAt_adjointD4_three {K : Type} [Field K] [Finite K] :
    OutCycAt 3 (adjointGroup Tag.D4 K) := by
  haveI : IsCyclic (RingAut K) := CFSG.LieType.Chevalley.ringAut_isCyclic
  haveI : Finite (adjointGroup Tag.D4 K) := by
    have : Finite (ModGL Tag.D4 K) := finite_modGL
    exact Subtype.finite
  refine outCycAt_of_cyclic (p := 3) Nat.prime_three
    (E := ⊤) (fun α _ => Subgroup.mem_top α) (C := RingAut K) ?_ ?_
  · exact (fieldPart (K := K)).comp (⊤ : Subgroup (MulAut (adjointGroup Tag.D4 K))).subtype
  · intro x hφ hx
    obtain ⟨g, a, σ, ε, hε, -, hxeq⟩ :=
      exists_cube_normal_form_sigma (K := K) (x : MulAut (adjointGroup Tag.D4 K)) hx
    have hφ' : fieldPart (x : MulAut (adjointGroup Tag.D4 K)) = 1 := hφ
    have hσ1 : σ = 1 := by
      have h1 : fieldPart (x : MulAut (adjointGroup Tag.D4 K)) = σ := by
        rw [hxeq, map_mul, fieldPart_conj, fieldPart_normalForm, one_mul]
      rw [← h1]
      exact hφ'
    rw [hσ1] at hxeq
    interval_cases ε
    · rw [d4Graph_zero, mul_one] at hxeq
      obtain ⟨h, hh⟩ := exists_inner_sq_conj_mul_exactNormalAut_one g a
      have hsq : (x : MulAut (adjointGroup Tag.D4 K)) ^ 2 ∈
          innAutDerived (adjointGroup Tag.D4 K) := by
        rw [hxeq, hh]
        exact inner_le_innAutDerived _ ⟨h, rfl⟩
      have hy : (x : MulAut (adjointGroup Tag.D4 K)) =
          ((x : MulAut (adjointGroup Tag.D4 K)) ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
      rw [hy]
      exact (innAutDerived (adjointGroup Tag.D4 K)).pow_mem hsq 2
    · rw [hxeq]
      exact mem_innAutDerived_of_graphType g a (Or.inl rfl) (by rw [← hxeq]; exact hx)
    · rw [hxeq]
      exact mem_innAutDerived_of_graphType g a (Or.inr rfl) (by rw [← hxeq]; exact hx)

theorem outCycAt_pomegaPlus_four_three {ℓ f : ℕ} {G : Type} [Group G]
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) : OutCycAt 3 G := by
  obtain ⟨-, K, hfield, hfinite, -, ⟨eG⟩⟩ := h
  letI := hfield
  letI := hfinite
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
      (F := K)
  exact outCycAt_of_mulEquiv (eG.trans eC).symm (outCycAt_adjointD4_three (K := K))

theorem outCycAt_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutCycAt p (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩).Group := by
  obtain ⟨K, hfield, hfinite, σ, hK, hσ, -, ⟨eB⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  letI := hfield
  letI := hfinite
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hCE : ChevalleyExceptionalModel ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      .trialityD4 q.p q.exponent :=
    CFSG.HardMathSupport.Dickson.Sec6.chevalleyExceptionalModel_trialityD4_of_equiv
      q.prime_p q.exponent_pos hK σ hσ (MulEquiv.refl _)
  have hPN : OutPNice p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    by_cases h2 : q.p = 2
    · rw [h2] at hCE
      exact outPNice_trialityD4 hp hCE
    · exact outPNice_trialityD4_odd hp h2 hCE
  exact outCycAt_of_mulEquiv eB.symm (outCycAt_of_outPChain hp hPN.toChain)

theorem lieOutCyc_classicalBCD :
    LieOutCyc isClassicalBCDIdx := by
  rintro ⟨d, hd⟩ p hp hp2 _ hP
  cases d with
  | B n q =>
    have hm := CFSG.Models.lieModel_B n q hd (MulEquiv.refl _)
    rcases hm with hm | hm
    · obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
      · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B n q, hd⟩).Group :=
          CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
        exact outCycAt_of_outPChain hp
          ((outPNice_statedClassicalModel_PSp hp hp2 hadm.2.2.1 hSC).toChain)
      · have h2n : 2 ≤ n := hadm.2.2.1
        omega
    · obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
      · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B n q, hd⟩).Group :=
          CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
        exact outCycAt_of_outPChain hp
          ((CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaOdd_all hp hp2 hSC).toChain)
      · have h3n : 3 ≤ n := hadm.2.2.1
        omega
  | C n q =>
    have hm := CFSG.Models.lieModel_C n q hd (MulEquiv.refl _)
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.C n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact outCycAt_of_outPChain hp
        ((outPNice_statedClassicalModel_PSp hp hp2 hadm.2.2.1 hSC).toChain)
    · have h2n : 2 ≤ n := hadm.2.2.1
      omega
  | D n q =>
    have hm := CFSG.Models.lieModel_D n q hd (MulEquiv.refl _)
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.D n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      by_cases hn : n = 4
      · obtain rfl : n = 4 := hn
        by_cases hp3 : p = 3
        · subst hp3
          exact outCycAt_pomegaPlus_four_three hSC
        · have hp5 : 5 ≤ p := by
            have h2 := hp.two_le
            have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
            omega
          exact outCycAt_of_outPChain hp (outPChain_POmegaPlus_four_gen hp hp5 hSC)
      · have hn4 : 4 ≤ n := hSC.1.2.2
        have hn5 : 5 ≤ n := by omega
        exact outCycAt_of_outPChain hp
          ((CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaPlus_all_ge_five
            hp hp2 hn5 hSC).toChain)
    · have h4n : 4 ≤ n := hadm.2.2
      omega
  | twistedD n q =>
    have hm := CFSG.Models.lieModel_twistedD n q hd (MulEquiv.refl _)
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hd⟩).Group :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact outCycAt_of_outPChain hp
        ((CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaMinus_all hp hp2 hSC).toChain)
    · have h4n : 4 ≤ n := hadm.2.2
      omega
  | A n q => exact absurd hP (by simp [isClassicalBCDIdx])
  | twistedA n q => exact absurd hP (by simp [isClassicalBCDIdx])
  | E6 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | E7 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | E8 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | F4 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | G2 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | twistedE6 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | trialityD4 q => exact absurd hP (by simp [isClassicalBCDIdx])
  | suzuki k => exact absurd hP (by simp [isClassicalBCDIdx])
  | reeG2 k => exact absurd hP (by simp [isClassicalBCDIdx])
  | reeF4 k => exact absurd hP (by simp [isClassicalBCDIdx])
  | tits => exact absurd hP (by simp [isClassicalBCDIdx])

theorem lieOutCyc_triality :
    LieOutCyc isTrialityIdx := by
  rintro ⟨d, hd⟩ p hp hp2 _ hP
  cases d with
  | trialityD4 q => exact outCycAt_trialityD4 q hd hp hp2
  | A n q => exact absurd hP (by simp [isTrialityIdx])
  | twistedA n q => exact absurd hP (by simp [isTrialityIdx])
  | B n q => exact absurd hP (by simp [isTrialityIdx])
  | C n q => exact absurd hP (by simp [isTrialityIdx])
  | D n q => exact absurd hP (by simp [isTrialityIdx])
  | twistedD n q => exact absurd hP (by simp [isTrialityIdx])
  | E6 q => exact absurd hP (by simp [isTrialityIdx])
  | E7 q => exact absurd hP (by simp [isTrialityIdx])
  | E8 q => exact absurd hP (by simp [isTrialityIdx])
  | F4 q => exact absurd hP (by simp [isTrialityIdx])
  | G2 q => exact absurd hP (by simp [isTrialityIdx])
  | twistedE6 q => exact absurd hP (by simp [isTrialityIdx])
  | suzuki k => exact absurd hP (by simp [isTrialityIdx])
  | reeG2 k => exact absurd hP (by simp [isTrialityIdx])
  | reeF4 k => exact absurd hP (by simp [isTrialityIdx])
  | tits => exact absurd hP (by simp [isTrialityIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
