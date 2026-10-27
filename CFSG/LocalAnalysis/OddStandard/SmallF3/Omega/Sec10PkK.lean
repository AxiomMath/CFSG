module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

namespace Pk

theorem gz_comm :
    gz * tA = tA * gz :=
  Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 gz_mem).2

theorem rho_injective :
    Function.Injective (rho : SL23 →* P45) :=
  (injective_iff_map_eq_one _).2 fun A hA => rho_props.2.1 A hA

noncomputable def rhoEquiv :
    SL23 ≃* KA :=
  MonoidHom.ofInjective rho_injective

theorem card_KA :
    Nat.card KA = 24 :=
  (Nat.card_congr rhoEquiv.toEquiv).symm.trans card_sl23

theorem card_KB :
    Nat.card KB = 24 := by
  rw [KB, CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj gz⁻¹).injective]
  exact card_KA

theorem isSL23Mod_KA :
    IsSL23Mod KA :=
  isSL23Mod_of_mulEquiv rhoEquiv isSL23Mod_sl2f3

theorem KA_le : KA ≤ Cs := by
  intro x hx
  obtain ⟨A, rfl⟩ := mem_KA.1 hx
  obtain ⟨-, -, h3, h4, -⟩ := rho_props
  exact Subgroup.mem_inf.2 ⟨h3 A, Subgroup.mem_centralizer_singleton_iff.2 (h4 A)⟩

theorem KB_le : KB ≤ Cs := by
  intro x hx
  obtain ⟨A, rfl⟩ := mem_KB.1 hx
  obtain ⟨-, -, h3, h4, -⟩ := rho_props
  have hg : gz ∈ P0 := (Subgroup.mem_inf.1 gz_mem).1
  have hc : Commute gz tA := gz_comm
  have h5 : Commute (Certificates.OmegaPk.cj gz (rhoF A)) tA :=
    (hc.inv_left.mul_left (h4 A : Commute (rhoF A) tA)).mul_left hc
  exact Subgroup.mem_inf.2 ⟨P0.mul_mem (P0.mul_mem (P0.inv_mem hg) (h3 A)) hg,
    Subgroup.mem_centralizer_singleton_iff.2 h5⟩

theorem tA_mem_KA : tA ∈ KA := by
  obtain ⟨-, -, -, -, A, hA⟩ := facts.rho
  exact mem_KA.2 ⟨A, hA⟩

theorem cent_KA {x : P45}
    (hx : x ∈ P0) (h : ∀ q ∈ Q2l, x * q = q * x) : x ∈ KA := by
  obtain ⟨A, hA⟩ := facts.centA.2 x hx h
  exact mem_KA.2 ⟨A, hA⟩

theorem cent_KB {x : P45}
    (hx : x ∈ P0) (h : ∀ q ∈ Q1l, x * q = q * x) : x ∈ KB := by
  obtain ⟨A, hA⟩ := facts.centB.2 x hx h
  exact mem_KB.2 ⟨A, hA⟩

theorem comm_KAB {a b : P45} (ha : a ∈ KA) (hb : b ∈ KB) :
    a * b = b * a := by
  obtain ⟨A, rfl⟩ := mem_KA.1 ha
  obtain ⟨B, rfl⟩ := mem_KB.1 hb
  exact facts.comm.1 A B

theorem KA_ne_KB : KA ≠ KB := by
  intro h
  obtain ⟨A, hA⟩ := facts.comm.2
  obtain ⟨B, hB⟩ := mem_KB.1 (h ▸ mem_KA.2 ⟨A, rfl⟩ : rhoF A ∈ KB)
  exact hA B hB.symm

theorem mem_sup_KAB {x : P45} :
    x ∈ KA ⊔ KB ↔ ∃ a ∈ KA, ∃ b ∈ KB, a * b = x := by
  have hle : KA ≤ Subgroup.centralizer (KB : Set P45) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (comm_KAB ha hb).symm
  have h := Subgroup.coe_mul_of_left_le_normalizer_right KA KB
    ((Subgroup.centralizer_le_normalizer (KB : Set P45)).trans' hle)
  rw [← SetLike.mem_coe, h, Set.mem_mul]
  simp only [SetLike.mem_coe]

end Pk

end CFSG.OddStandard.SmallF3.Omega
