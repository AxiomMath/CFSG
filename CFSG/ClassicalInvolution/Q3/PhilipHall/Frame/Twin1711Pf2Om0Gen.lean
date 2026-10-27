module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Om0Fin
public import Certificates.Certificate118003

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Q3.TL4.E4O8

set_option linter.unusedSectionVars false

theorem om0GenFacts_of_cert :
    Om0GenFacts := by
  have h := (Certificates.certificate118003 :
    Om0Check.om0GenCheck () = true)
  simp only [Om0Check.om0GenCheck, Om0Check.om0Comm, Om0Check.om0Prod, Bool.and_eq_true,
    List.all_eq_true] at h
  have hx : Rep 360 (xA 0) (mainPerm 0) := rep_main (by norm_num)
  have hv : Rep 360 (v0A ()) v0 := v0_spec.1
  have hc : ∀ (l : ℕ), l < 8 → ∀ {u : Array ℕ} {w : Equiv.Perm (Fin 360)}, Rep 360 u w →
      Rep 360 (conjArr genArrs[l]! u) (gen l * w * (gen l)⁻¹) := fun l hl u w hu =>
    CFSG.EvenSmallLie.OmegaEight.rep_conjArr (rep_gen (by omega)) (rep_gen_inv (by omega)) hu
  refine ⟨?_, ?_⟩
  · intro l hl hl3
    have hm : l ∈ [0, 1, 2, 4, 5, 6, 7] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    exact (eqA_iff (rep_compA (rep_gen (by omega)) hx) (rep_compA hx (rep_gen (by omega)))).1
      (h.1 l hm)
  · refine (eqA_iff (hc _ (by norm_num) hx) ?_).1 h.2
    exact rep_compA (rep_compA (rep_compA (hc _ (by norm_num) hv) (hc _ (by norm_num) hv))
      (hc _ (by norm_num) hv)) (hc _ (by norm_num) (rep_compA hv hx))

theorem om0_proved :
    NoSandwichAt ModOm0 :=
  om0_of_gen om0GenFacts_of_cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0
