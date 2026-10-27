module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Cfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification.AschbacherTightEmbedding

section Coset

variable {T : Type} [Group T]

theorem fixesUnique_of_only_base {M : Subgroup T} {a : T} (haM : a ∈ M)
    (h : ∀ x : T, x⁻¹ * a * x ∈ M → x ∈ M) : ∃! c : T ⧸ M, a • c = c := by
  refine ⟨((1 : T) : T ⧸ M), ?_, ?_⟩
  · show ((a * 1 : T) : T ⧸ M) = ((1 : T) : T ⧸ M)
    rw [QuotientGroup.eq]
    simpa using M.inv_mem haM
  · intro c hc
    revert hc
    refine QuotientGroup.induction_on c fun x => ?_
    intro hc
    have hx : ((a * x : T) : T ⧸ M) = (x : T ⧸ M) := hc
    rw [QuotientGroup.eq] at hx
    have hx' : x⁻¹ * a * x ∈ M := by simpa [mul_assoc] using M.inv_mem hx
    have hxM := h x hx'
    show (x : T ⧸ M) = ((1 : T) : T ⧸ M)
    rw [QuotientGroup.eq]
    simpa using M.inv_mem hxM

end Coset

@[expose] def UniqueCosetZ {T : Type} [Group T] (K : Subgroup T) (z : T) : Prop :=
  ∀ x : T, x⁻¹ * z * x ∈ sigmaNorm K → x ∈ sigmaNorm K

namespace FrameCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {S : Subgroup T}

theorem prod_basic (cfg : FrameCfg K z J zJ S) {h : T} (hne : h⁻¹ * z * h ≠ z)
    (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    z * (h⁻¹ * z * h) ∈ sigmaNorm K ∧ orderOf (z * (h⁻¹ * z * h)) = 2 := by
  set w := h⁻¹ * z * h with hw
  have hz := cfg.datum.unique
  have hwz : z * w = w * z := hc
  have hw2 : w * w = 1 := by
    calc w * w = h⁻¹ * (z * z) * h := by rw [hw]; group
      _ = 1 := by rw [hz.sq]; group
  have ha2 : z * w * (z * w) = 1 := by
    calc z * w * (z * w) = z * (w * z) * w := by group
      _ = z * (z * w) * w := by rw [hwz]
      _ = (z * z) * (w * w) := by group
      _ = 1 := by rw [hz.sq, hw2, one_mul]
  have ha1 : z * w ≠ 1 := by
    intro h1
    apply hne
    have : w = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hz.sq)
  have haC : z * w ∈ Subgroup.centralizer ({z} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * w * z = z * (w * z) := by group
      _ = z * (z * w) := by rw [hwz]
  exact ⟨cfg.cz_le haC, orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1⟩

end FrameCfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
