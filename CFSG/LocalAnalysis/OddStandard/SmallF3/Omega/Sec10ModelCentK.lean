module

public import Certificates.Certificate442003
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem centK_check_true :
    Certificates.OmegaCentK.check () = true :=
  Certificates.certificate442003

theorem eq_of_comm_oddL {a : P45}
    (ha : a ∈ QA45.originalSubgroup)
    (h : ∀ x ∈ QP45.originalSubgroup ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45),
      Odd (orderOf x) → a * x = x * a) :
    a = 1 ∨ a = Certificates.P43Twin.tA () := by
  have hs := centK_check_true
  simp only [Certificates.OmegaCentK.check, Certificates.OmegaCentK.centChk] at hs
  have h2 := forall_of_all QA45 QA45_ok hs a ha
  have hO : (Certificates.OmegaCentK.oddL
      (Certificates.OmegaCentK.centL (elemsT QP45) (Certificates.P43Twin.tA ()))).all
      (fun x => decide (a * x = x * a)) = true := by
    rw [List.all_eq_true]
    intro x hx
    simp only [Certificates.OmegaCentK.oddL, Certificates.OmegaCentK.centL, List.mem_filter,
      decide_eq_true_eq] at hx
    obtain ⟨⟨hxL, hxc⟩, hx9⟩ := hx
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat (by decide : Odd 9) (orderOf_dvd_of_pow_eq_one hx9)
    exact decide_eq_true (h x ⟨(mem_elemsT QP45 QP45_ok x).1 hxL,
      Subgroup.mem_centralizer_singleton_iff.2 hxc⟩ hodd)
  rw [hO] at h2
  simpa [Bool.or_eq_true] using h2

end CFSG.OddStandard.SmallF3.Omega
