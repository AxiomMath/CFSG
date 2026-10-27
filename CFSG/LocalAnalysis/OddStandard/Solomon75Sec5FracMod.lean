module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ}

@[expose] noncomputable def AhatModel.transportUp {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n E) :
    AhatModel X n B :=
  ⟨M.K, ((quotOddCore_equiv_of_cover hEB hcov).choose.symm).trans M.e, M.C⟩

theorem AhatModel.transportUp_e_mk {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n E) (a : ↥E) :
    (M.transportUp hEB hcov).e (QuotientGroup.mk (⟨a.1, hEB a.2⟩ : ↥B)) =
      M.e (QuotientGroup.mk a) := by
  have h := (quotOddCore_equiv_of_cover hEB hcov).choose_spec a
  show M.e ((quotOddCore_equiv_of_cover hEB hcov).choose.symm
    (QuotientGroup.mk (⟨a.1, hEB a.2⟩ : ↥B))) = _
  have h2 : (QuotientGroup.mk (⟨a.1, hEB a.2⟩ : ↥B) : ↥B ⧸ pPrimeCore 2 ↥B) =
      (quotOddCore_equiv_of_cover hEB hcov).choose (QuotientGroup.mk a) := by
    rw [h]; rfl
  rw [h2, MulEquiv.symm_apply_apply]

theorem AhatModel.autOf_transportUp {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n E) {c : X}
    (hcE : c ∈ normalizer (E : Set X)) (hcB : c ∈ normalizer (B : Set X)) :
    (M.transportUp hEB hcov).autOf c hcB = M.autOf c hcE := by
  refine MulEquiv.ext fun k => ?_
  obtain ⟨a, rfl⟩ := M.surj_mk k
  have h1 : conjAut hcB (⟨a.1, hEB a.2⟩ : ↥B) = ⟨(conjAut hcE a).1, hEB (conjAut hcE a).2⟩ :=
    Subtype.ext (by simp only [coe_conjAut])
  have e1 : (M.transportUp hEB hcov).autOf c hcB (M.e (QuotientGroup.mk a)) =
      M.e (QuotientGroup.mk (conjAut hcE a)) := by
    have := (M.transportUp hEB hcov).autOf_mk hcB (⟨a.1, hEB a.2⟩ : ↥B)
    rw [M.transportUp_e_mk hEB hcov a, h1, M.transportUp_e_mk hEB hcov (conjAut hcE a)] at this
    exact this
  exact e1.trans (M.autOf_mk hcE a).symm

theorem AhatModel.perm_transportUp (hn : 8 ≤ n) {E B : Subgroup X} (hEB : E ≤ B)
    (hcov : ∀ c ∈ B, ∃ a ∈ E, ∃ o ∈ oddCoreOf B, c = a * o) (M : AhatModel X n E) {c : X}
    (hcE : c ∈ normalizer (E : Set X)) (hcB : c ∈ normalizer (B : Set X)) :
    (M.transportUp hEB hcov).perm c hcB = M.perm c hcE := by
  apply (M.transportUp hEB hcov).perm_eq_of_induces hn hcB
  rw [M.autOf_transportUp hEB hcov hcE hcB]
  exact M.induces_perm hn c hcE

end CFSG.OddStandard.Solomon75
