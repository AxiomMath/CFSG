module

public import CFSG.ClassicalInvolution.Q3.TL3Induct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12

open scoped commutatorElement

namespace Perp23

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem commute_of_alpha {A : Subgroup G} (hα : alphaOf A = ⊥) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {n b : G} (hn : n ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G))) (hb : b ∈ A) :
    n * b = b * n := by
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ ≤ alphaOf A := by
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le a ha (le_iSup (fun _ : a ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) ha1)
  rw [hα, le_bot_iff] at hle
  have hmem : ⁅n, b⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ :=
    Subgroup.commutator_mem_commutator hn hb
  rw [hle, Subgroup.mem_bot, commutatorElement_def] at hmem
  calc n * b = (n * b * n⁻¹ * b⁻¹) * (b * n) := by group
    _ = b * n := by rw [hmem, one_mul]

end OddCore

section Conj

variable {G : Type} [Group G]

@[expose] def centConj (g a : G) :
    ↥(Subgroup.centralizer ({a} : Set G)) ≃* ↥(Subgroup.centralizer ({g * a * g⁻¹} : Set G)) where
  toFun x := ⟨g * (x : G) * g⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    calc g * (x : G) * g⁻¹ * (g * a * g⁻¹) = g * ((x : G) * a) * g⁻¹ := by group
      _ = g * (a * (x : G)) * g⁻¹ := by rw [hx]
      _ = g * a * g⁻¹ * (g * (x : G) * g⁻¹) := by group⟩
  invFun y := ⟨g⁻¹ * (y : G) * g, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    calc g⁻¹ * (y : G) * g * a = g⁻¹ * ((y : G) * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * (y : G)) * g := by rw [hy]
      _ = a * (g⁻¹ * (y : G) * g) := by group⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

end Conj

section Transport

variable {G : Type} [Group G] [Finite G]

theorem tightInO2_conj (g a : G) {x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    (h : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set G)))
      (⟨x, hx⟩ : ↥(Subgroup.centralizer ({a} : Set G))))) :
    TightInO2 (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(Subgroup.centralizer ({g * a * g⁻¹} : Set G)))
      (centConj g a ⟨x, hx⟩)) := by
  obtain ⟨P, hPn, hP2, hxP⟩ := h
  set ψ := centConj g a with hψ
  set ψb := QuotientGroup.congr (classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set G)))
    (classicalInvolutionOddCore ↥(Subgroup.centralizer ({g * a * g⁻¹} : Set G))) ψ
    (CFSG.ComponentClassification.OddCore.equiv_invariant ψ) with hψb
  refine ⟨P.map ψb.toMonoidHom, hPn.map _ ψb.surjective, ?_, ?_⟩
  · exact hP2.of_equiv (P.equivMapOfInjective ψb.toMonoidHom ψb.injective)
  · refine ⟨_, hxP, ?_⟩
    rfl

end Transport

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
