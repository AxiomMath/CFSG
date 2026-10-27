module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Good
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D
public import Certificates.Certificate55116

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem commute_of_gens {y : Equiv.Perm (Fin 360)} (hu : y * u0 = u0 * y)
    (hv : y * v0 = v0 * y) {c : Equiv.Perm (Fin 360)} (hc : c ∈ K0) : y * c = c * y := by
  have hle : K0 ≤ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 360))) := by
    rw [K0, Subgroup.closure_le]
    rintro z (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact hu.symm
    · exact hv.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm

theorem noGood_model {sc : Equiv.Perm (Fin 360)} (hsc : IsUniqueInvolution K0 sc)
    {x : Equiv.Perm (Fin 360)} (hx : x ∈ omegaT) (k : ℕ) (hx3 : x ^ 3 ^ k = 1)
    (hxK : conjSub x K0 = K0) (hact : ∃ c ∈ K0, x * c ≠ c * x) :
    ∃ y ∈ omegaT, y ^ 3 = 1 ∧ (∀ c ∈ K0, y * c = c * y) ∧ x * y ≠ y * x := by
  have hxx : x * mainPerm 0 = mainPerm 0 * x := by
    have h := hsc.conj_eq hxK
    rw [eq_x0_of_isUniqueInvolution hsc] at h
    calc x * mainPerm 0 = x * mainPerm 0 * x⁻¹ * x := by group
      _ = mainPerm 0 * x := by rw [h]
  have hx1 : x ≠ 1 := by
    rintro rfl
    obtain ⟨c, -, hc⟩ := hact
    exact hc (by rw [one_mul, mul_one])
  obtain ⟨y, hy, hy3, hyu, hyv, hxy⟩ :=
    Certificates.certificate55116 x hx hxx ⟨k, hx3⟩ hx1
  exact ⟨y, hy, hy3, fun c hc => commute_of_gens hyu hyv hc, hxy⟩

theorem e4QuatNoGood_POmegaPlus {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) : E4QuatNoGood M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  exact Vtx.e4QuatNoGood_of_model omegaT K0 (fun K s hd => exists_emb e hd)
    (fun sc hsc x hx k hx3 hxK hact => noGood_model hsc hx k hx3 hxK hact)

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
