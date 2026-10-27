module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCyc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary

public section

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem outCycAt_primeFormP {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutCycAt p (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  classical
  haveI : Finite K := h.finite
  let T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  haveI : Finite T := inferInstance
  haveI : IsCyclic (RingAut K) :=
    (card_ringAut_and_isCyclic h.prime K h.card).2
  let E : Subgroup (MulAut T) := ⊤
  have hE : ∀ α : MulAut T, α ^ p = 1 → α ∈ E := fun _ _ => by simp [E]
  let φ : E →* RingAut K :=
    (primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq).comp E.subtype
  have hker : ∀ x : E, φ x = 1 → (x : MulAut T) ^ p = 1 →
      (x : MulAut T) ∈ innAutDerived T := by
    intro x hx hxp
    have hx' : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq (x : MulAut T) = 1 :=
      hx
    have hxD : (x : MulAut T) ∈ primeFormD h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq]
      exact hx'
    exact mem_innAutDerived_of_mem_primeFormD h hp hp2 hxD hxp
  exact outCycAt_of_cyclic hp E hE φ hker

theorem lieOutCyc_unitary : LieOutCyc isUnitaryIdx := by
  intro d p hp hp2 hpchar hP
  obtain ⟨i, hi⟩ := d
  cases i with
  | twistedA n q =>
    have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hi
      (G := (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hi⟩).Group) (MulEquiv.refl _)
    obtain ⟨K, _, hU, -, ⟨eP⟩⟩ :=
      CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel
        hmodel
    have hN : 3 ≤ n + 1 := hmodel.1.2.2.1
    have hne : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨h1, h2⟩
      exact hmodel.1.2.2.2 (by rw [h1, h2])
    exact outCycAt_of_mulEquiv eP.symm (outCycAt_primeFormP hU hN hne hp hp2)
  | A n q => exact absurd hP (by simp [isUnitaryIdx])
  | B n q => exact absurd hP (by simp [isUnitaryIdx])
  | C n q => exact absurd hP (by simp [isUnitaryIdx])
  | D n q => exact absurd hP (by simp [isUnitaryIdx])
  | twistedD n q => exact absurd hP (by simp [isUnitaryIdx])
  | E6 q => exact absurd hP (by simp [isUnitaryIdx])
  | E7 q => exact absurd hP (by simp [isUnitaryIdx])
  | E8 q => exact absurd hP (by simp [isUnitaryIdx])
  | F4 q => exact absurd hP (by simp [isUnitaryIdx])
  | G2 q => exact absurd hP (by simp [isUnitaryIdx])
  | twistedE6 q => exact absurd hP (by simp [isUnitaryIdx])
  | trialityD4 q => exact absurd hP (by simp [isUnitaryIdx])
  | suzuki k => exact absurd hP (by simp [isUnitaryIdx])
  | reeG2 k => exact absurd hP (by simp [isUnitaryIdx])
  | reeF4 k => exact absurd hP (by simp [isUnitaryIdx])
  | tits => exact absurd hP (by simp [isUnitaryIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
