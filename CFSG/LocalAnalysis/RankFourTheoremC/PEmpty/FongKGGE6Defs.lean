module

public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGGrp
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

set_option linter.unusedSectionVars false


abbrev C6 (F : Type) [Field F] : Type := ↥(adjointGroup Tag.E6 F)

@[expose] def U6 (F : Type) [Field F] : Subgroup (C6 F) :=
  (posUnipotent Tag.E6 F).subgroupOf (adjointGroup Tag.E6 F)

@[expose] def stabU (F : Type) [Field F] : Subgroup (MulAut (C6 F)) where
  carrier := {α | ∀ x : C6 F, α x ∈ U6 F ↔ x ∈ U6 F}
  one_mem' := fun x => Iff.rfl
  mul_mem' := fun {α β} hα hβ x => by
    show α (β x) ∈ U6 F ↔ x ∈ U6 F
    exact (hα (β x)).trans (hβ x)
  inv_mem' := fun {α} hα x => by
    show α⁻¹ x ∈ U6 F ↔ x ∈ U6 F
    have := hα (α⁻¹ x)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

theorem mem_stabU_iff {F : Type} [Field F] {α : MulAut (C6 F)} :
    α ∈ stabU F ↔ ∀ x : C6 F, α x ∈ U6 F ↔ x ∈ U6 F := Iff.rfl

theorem mem_stabU_iff_map {F : Type} [Field F] {α : MulAut (C6 F)} :
    α ∈ stabU F ↔ (U6 F).map α.toMonoidHom = U6 F := by
  constructor
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).mpr hx
    · intro hy
      refine ⟨α⁻¹ y, ?_, by simp⟩
      exact (h (α⁻¹ y)).mp (by simpa using hy)
  · intro h x
    constructor
    · intro hx
      have : α x ∈ (U6 F).map α.toMonoidHom := by rw [h]; exact hx
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := α.injective hyx
      exact this ▸ hy
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩

theorem U6_sylow (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∃ P : Sylow 2 (C6 F), (P : Subgroup (C6 F)) = U6 F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.E6).length
  exact (exceptional_ordinary_Sylow_opposition Tag.E6 F 2 w₀ hw₀).1

theorem exists_conj_stabU (F : Type) [Field F] [Finite F] [CharP F 2] {S : Subgroup (MulAut (C6 F))}
    (hS : IsPGroup 2 ↥S) :
    ∃ h : C6 F, ∀ σ ∈ S, MulAut.conj h⁻¹ * σ * MulAut.conj h ∈ stabU F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_two_fixed hS
  obtain ⟨P₀, hP₀⟩ := U6_sylow F
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (C6 F) P₀ P
  refine ⟨h, fun σ hσ x => ?_⟩
  have hmem : ∀ y : C6 F, y ∈ (P : Subgroup (C6 F)) ↔ h⁻¹ * y * h ∈ U6 F := by
    intro y
    rw [← hh, ← hP₀, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_apply, mul_assoc]
  have e1 : (MulAut.conj h⁻¹ * σ * MulAut.conj h) x = h⁻¹ * σ (h * x * h⁻¹) * h := by
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
  rw [e1]
  have e2 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  have hy := hmem (h * x * h⁻¹)
  rw [e2] at hy
  rw [← hmem (σ (h * x * h⁻¹)), hP σ hσ]
  exact hy

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
