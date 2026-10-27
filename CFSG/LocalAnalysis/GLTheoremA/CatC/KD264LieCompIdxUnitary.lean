module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

theorem compIdxAt_primeFormP_unitary {q : TauCeti.PrimePower} {r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData q.p q.exponent K) (hr : 3 ≤ r + 1)
    (hq : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ q.p) :
    CompIdxAt p (.twistedA r q) (primeFormP h (idGram K (r + 1))) := by
  intro β hβmem hβp hβ1 T hT
  classical
  obtain ⟨A, c, -, hA, hβeq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived h isPrimeFormGram_idGram hr hq
      hβmem hβp
  rw [hβeq] at hT
  obtain ⟨dd, hdd, hcase⟩ :=
    exists_field_factor_of_component_primeFormConjHom (h := h) hp hpℓ A hA T hT
  have hTperf : commutator ↥T = ⊤ := hT.2.2.1
  have hpow : (fieldSize (TauCeti.LieTypeIndex.twistedA r q)) ^ dd =
      q.p ^ (q.exponent * dd) := by
    rw [show fieldSize (TauCeti.LieTypeIndex.twistedA r q) = q.card from rfl,
      TauCeti.PrimePower.card_def, pow_mul]
  rcases hcase with
      ⟨F, hF, hFt, hcharF, hcardF, h4, g, hg, hk⟩ |
      ⟨E, hE, hEt, m, hcharE, hcardE, hm, hne, g, hg, hk⟩ |
      ⟨E, hE, hEt, m, hcharE, hcardE, hm2, h4, g, hg, hk⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
      (slFactorFacts_holds F 2 le_rfl (fun _ => h4)).perfect
    obtain ⟨i, ⟨φ⟩, hidx⟩ :=
      (catalogueOver_sl F 2 le_rfl (fun _ => h4)).of_surjective hperf g hg hk
    rw [hcharF, hcardF] at hidx
    exact ⟨i, ⟨φ⟩, compRelC_of_idxOver (d := .twistedA r q) (j := dd) hdd (by
      rwa [TauCeti.LieTypeIndex.characteristic_twistedA, hpow])⟩
  · letI : Field E := hE
    letI : Fintype E := hEt
    have hperf : commutator ↥(StatedSU m (q.p ^ (q.exponent * dd)) E) = ⊤ :=
      (suFactorFacts_holds E m (q.p ^ (q.exponent * dd)) hcardE hm hne).perfect
    obtain ⟨i, ⟨φ⟩, hidx⟩ := (catalogueOver_su E m (q.p ^ (q.exponent * dd)) hcardE hm
      hne).of_surjective hperf g hg hk
    rw [hcharE] at hidx
    exact ⟨i, ⟨φ⟩, compRelC_of_idxOver (d := .twistedA r q) (j := dd) hdd (by
      rwa [TauCeti.LieTypeIndex.characteristic_twistedA, hpow])⟩
  · letI : Field E := hE
    letI : Fintype E := hEt
    have hpow2 : (fieldSize (TauCeti.LieTypeIndex.twistedA r q)) ^ (2 * dd) =
        q.p ^ (2 * (q.exponent * dd)) := by
      rw [show fieldSize (TauCeti.LieTypeIndex.twistedA r q) = q.card from rfl,
        TauCeti.PrimePower.card_def, ← pow_mul]
      congr 1
      ring
    have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ :=
      (slFactorFacts_holds E m hm2 (fun _ => h4)).perfect
    obtain ⟨i, ⟨φ⟩, hidx⟩ :=
      (catalogueOver_sl E m hm2 (fun _ => h4)).of_surjective hperf g hg hk
    rw [hcharE, hcardE] at hidx
    exact ⟨i, ⟨φ⟩, compRelC_of_idxOver (d := .twistedA r q) (j := 2 * dd)
      (by omega) (by rwa [TauCeti.LieTypeIndex.characteristic_twistedA, hpow2])⟩

theorem exists_primeFormP_mulEquiv_of_isUnitaryIdx {d : TauCeti.ValidLieTypeIndex}
    (hd : isUnitaryIdx d.1) :
    ∃ (r : ℕ) (q : TauCeti.PrimePower) (K : Type) (_ : Field K)
      (h : UnitaryFieldData q.p q.exponent K),
      2 ≤ r ∧ d.1 = .twistedA r q ∧ ¬ (r + 1 = 3 ∧ q.card = 2) ∧
        Nonempty (primeFormP h (idGram K (r + 1)) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨idx, hv⟩ := d
  simp only [isUnitaryIdx] at hd
  cases idx with
  | twistedA r q =>
      have hmodel : StatedClassicalModel
          (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group .PSU (r + 1) q.p q.exponent :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
      obtain ⟨K, _, hU, -, ⟨eP⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel hmodel
      have hne : ¬ (r + 1 = 3 ∧ q.card = 2) := by
        rintro ⟨h1, h2⟩
        exact hmodel.1.2.2.2 (by rw [h1, ← TauCeti.PrimePower.card_def, h2])
      refine ⟨r, q, K, inferInstance, hU, ?_, ?_, hne, ?_⟩
      · have h3 := hmodel.1.2.2.1
        omega
      · rfl
      · exact ⟨eP.symm⟩
  | A n q => exact absurd hd (by simp [isUnitaryIdx])
  | B n q => exact absurd hd (by simp [isUnitaryIdx])
  | C n q => exact absurd hd (by simp [isUnitaryIdx])
  | D n q => exact absurd hd (by simp [isUnitaryIdx])
  | twistedD n q => exact absurd hd (by simp [isUnitaryIdx])
  | E6 q => exact absurd hd (by simp [isUnitaryIdx])
  | E7 q => exact absurd hd (by simp [isUnitaryIdx])
  | E8 q => exact absurd hd (by simp [isUnitaryIdx])
  | F4 q => exact absurd hd (by simp [isUnitaryIdx])
  | G2 q => exact absurd hd (by simp [isUnitaryIdx])
  | twistedE6 q => exact absurd hd (by simp [isUnitaryIdx])
  | trialityD4 q => exact absurd hd (by simp [isUnitaryIdx])
  | suzuki k => exact absurd hd (by simp [isUnitaryIdx])
  | reeG2 k => exact absurd hd (by simp [isUnitaryIdx])
  | reeF4 k => exact absurd hd (by simp [isUnitaryIdx])
  | tits => exact absurd hd (by simp [isUnitaryIdx])

theorem lieCompIdx_unitary : LieCompIdx isUnitaryIdx := by
  intro d p hp hp2 hpc hP
  obtain ⟨r, q, K, _, hU, hr, hdA, hne, ⟨eP⟩⟩ :=
    exists_primeFormP_mulEquiv_of_isUnitaryIdx hP
  have hpℓ : p ≠ q.p := by
    rw [hdA, TauCeti.LieTypeIndex.characteristic_twistedA] at hpc
    exact hpc
  have hn : 3 ≤ r + 1 := by omega
  have hne' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨h1, by rw [TauCeti.PrimePower.card_def]; exact h2⟩
  have h := compIdxAt_of_mulEquiv eP (compIdxAt_primeFormP_unitary hU hn hne' hp hpℓ)
  simpa [← hdA] using h

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
