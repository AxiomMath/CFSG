module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentJ3
public import Certificates.Certificate27824

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native

theorem mulE0_lt : ∀ a < 32, ∀ b < 32, mulE0 a b < 32 := by
  decide +kernel

theorem rho_facts : (∀ k < 32, rhoInvArr[k]! < 32) ∧
    (∀ a < 32, ∀ b < 32, rhoInvArr[a]! = rhoInvArr[b]! → a = b) ∧
    (∀ j < 32, ∃ k < 32, rhoInvArr[k]! = j) ∧ rhoInvArr[0]! = 0 ∧ rhoInvArr[21]! = 21 := by
  decide +kernel

section Cert

theorem rho_mul : ∀ a < 32, ∀ b < 32,
    rhoInvArr[mulE0 a b]! = mulEJ3 rhoInvArr[a]! rhoInvArr[b]! :=
  Certificates.certificate27824

theorem j2_spec : (∀ a < 32, ∀ b < 32, J2.uMulJ2 a b = mulE0 a b) ∧ J2.uIdxJ2 = eT :=
  ⟨fun _ _ _ _ => rfl, rfl⟩

theorem uMulJ2_eq : ∀ a < 32, ∀ b < 32, J2.uMulJ2 a b = mulE0 a b := j2_spec.1

theorem uIdxJ2_eq : J2.uIdxJ2 = eT := j2_spec.2

theorem j3_spec : (∀ a < 32, ∀ b < 32, J3.uMulJ3 a b = mulEJ3 a b) ∧ J3.uIdxJ3 = eT :=
  ⟨fun _ _ _ _ => rfl, rfl⟩

theorem uMulJ3_eq : ∀ a < 32, ∀ b < 32, J3.uMulJ3 a b = mulEJ3 a b := j3_spec.1

theorem uIdxJ3_eq : J3.uIdxJ3 = eT := j3_spec.2

theorem eLab_of_J2 {Γ : Type*} [Group Γ] {E : Subgroup Γ} {t : Γ} {elt : ℕ → Γ}
    (h : ELabelling E t J2.uMulJ2 J2.uIdxJ2 elt) : ELabelling E t mulE0 eT elt where
  mem := h.mem
  surj := h.surj
  inj := h.inj
  lt := mulE0_lt
  mul a ha b hb := by
    rw [← uMulJ2_eq a ha b hb]
    exact h.mul a ha b hb
  one := h.one
  tI_lt := by decide
  at_tI := by
    have h' := h.at_tI
    rwa [uIdxJ2_eq] at h'

theorem eLab_of_J3 {Γ : Type*} [Group Γ] {E : Subgroup Γ} {t : Γ} {elt : ℕ → Γ}
    (h : ELabelling E t J3.uMulJ3 J3.uIdxJ3 elt) :
    ELabelling E t mulE0 eT (fun k => elt rhoInvArr[k]!) where
  mem k hk := h.mem _ (rho_facts.1 k hk)
  surj e he := by
    obtain ⟨j, hj, hje⟩ := h.surj e he
    obtain ⟨k, hk, hkj⟩ := rho_facts.2.2.1 j hj
    exact ⟨k, hk, by show elt rhoInvArr[k]! = e; rw [hkj]; exact hje⟩
  inj a ha b hb hab :=
    rho_facts.2.1 a ha b hb (h.inj _ (rho_facts.1 a ha) _ (rho_facts.1 b hb) hab)
  lt := mulE0_lt
  mul a ha b hb := by
    show elt rhoInvArr[mulE0 a b]! = elt rhoInvArr[a]! * elt rhoInvArr[b]!
    rw [rho_mul a ha b hb, ← uMulJ3_eq _ (rho_facts.1 a ha) _ (rho_facts.1 b hb)]
    exact h.mul _ (rho_facts.1 a ha) _ (rho_facts.1 b hb)
  one := by
    show elt rhoInvArr[0]! = 1
    rw [rho_facts.2.2.2.1]
    exact h.one
  tI_lt := by decide
  at_tI := by
    show elt rhoInvArr[eT]! = t
    rw [show rhoInvArr[eT]! = eT from rho_facts.2.2.2.2, ← uIdxJ3_eq]
    exact h.at_tI

end Cert

end CFSG.EvenSporadicStandard.Fin76b.W16
