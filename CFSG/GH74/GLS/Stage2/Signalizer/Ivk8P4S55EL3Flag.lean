module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3FlagSp
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3FlagAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

namespace Fl3

variable {F : Type} [Field F]

theorem mem_stabilizer_of_invariant {W : Submodule F (Fin 3 → F)} {g : SL(3, F)}
    (h1 : ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W)
    (h2 : ∀ v ∈ W, ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) :
    g ∈ stabilizer W := by
  rw [mem_stabilizer]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact h1 v hv
  · intro w hw
    refine ⟨((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w, h2 w hw, ?_⟩
    change (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w
    rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul g g⁻¹, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem mem_stabilizer_fix {R : Subgroup SL(3, F)} {g : SL(3, F)}
    (hg : g ∈ normalizer (R : Set SL(3, F))) : g ∈ stabilizer (fix R) :=
  mem_stabilizer_of_invariant (fun _ hv => mulVec_mem_fix hg hv)
    (fun _ hv => mulVec_mem_fix (inv_mem hg) hv)

theorem mem_stabilizer_aug {R : Subgroup SL(3, F)} {g : SL(3, F)}
    (hg : g ∈ normalizer (R : Set SL(3, F))) : g ∈ stabilizer (aug R) :=
  mem_stabilizer_of_invariant (fun _ hv => mulVec_mem_aug hg hv)
    (fun _ hv => mulVec_mem_aug (inv_mem hg) hv)

theorem exists_flag [Finite F] (X Y : Submodule F (Fin 3 → F)) (hXY : X ⊓ Y ≠ ⊥)
    (hX : 1 ≤ finrank F X) (hY : 1 ≤ finrank F Y) (hsum : finrank F X + finrank F Y = 3) :
    ∃ L P : Submodule F (Fin 3 → F), L ≤ P ∧ finrank F L = 1 ∧ finrank F P = 2 ∧
      ((L = X ∧ P = Y) ∨ (L = Y ∧ P = X)) := by
  have hpos : 1 ≤ finrank F ↥(X ⊓ Y) := Submodule.one_le_finrank_iff.mpr hXY
  have hXle : finrank F ↥(X ⊓ Y) ≤ finrank F X := Submodule.finrank_mono inf_le_left
  have hYle : finrank F ↥(X ⊓ Y) ≤ finrank F Y := Submodule.finrank_mono inf_le_right
  rcases (show finrank F X = 1 ∨ finrank F X = 2 by omega) with h | h
  · have hinf : X ⊓ Y = X :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    exact ⟨X, Y, inf_eq_left.mp hinf, h, by omega, Or.inl ⟨rfl, rfl⟩⟩
  · have hinf : X ⊓ Y = Y :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
    exact ⟨Y, X, inf_eq_right.mp hinf, by omega, h, Or.inr ⟨rfl, rfl⟩⟩

end Fl3

theorem false_of_graph_flag {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2)
    (U : Subgroup (projectiveSL 3 F)) (hU1 : U ≠ ⊥) (hUp : IsPGroup p ↥U)
    (T : Subgroup (projectiveSL 3 F)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hTU : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U)
    (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hα : ∀ u ∈ U, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) u ∈ U) : False := by
  obtain ⟨Û, hÛp, hmap, hnorm⟩ := Odd87.exists_lift_isPGroup_proj p U hUp
  have hÛne : Û ≠ ⊥ := by
    intro h
    apply hU1
    rw [← hmap, h, Subgroup.map_bot]
  have hnT : ∀ g : SL(3, F), proj 3 F g ∈ T → g ∈ normalizer (Û : Set SL(3, F)) := by
    intro g hg
    refine hnorm g ?_
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact fun hu => hTU _ hg u hu
    · intro hu
      have := hTU _ (T.inv_mem hg) _ hu
      simpa [mul_assoc] using this
  have hstab : ∀ x ∈ Û, Fl3.gAut A σ x ∈ Û := by
    refine Fl3.gAut_mem hÛp A σ ?_
    intro x hx
    rw [hmap]
    exact hα _ (hmap ▸ Subgroup.mem_map_of_mem _ hx)
  have hcard := Fl3.card_fix_eq A σ Û hstab
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hdim : finrank F (Fl3.fix Û) = finrank F (Fl3.fixT Û) := by
    have h1 : Nat.card ↥(Fl3.fix Û) = Nat.card ↥(Fl3.fixT Û) := hcard
    have e1 := Module.natCard_eq_pow_finrank (K := F) (V := ↥(Fl3.fix Û))
    have e2 := Module.natCard_eq_pow_finrank (K := F) (V := ↥(Fl3.fixT Û))
    rw [e1, e2] at h1
    exact Nat.pow_right_injective hq h1
  have hsum := Fl3.finrank_aug_add_finrank_fixT Û
  have hfix : 1 ≤ finrank F (Fl3.fix Û) := by
    obtain ⟨v, hv0, hv⟩ := Odd87.exists_fixed_vector_sl3 p Û hÛp
    refine Submodule.one_le_finrank_iff.mpr (fun hbot => hv0 ?_)
    have : v ∈ Fl3.fix Û := hv
    rwa [hbot, Submodule.mem_bot] at this
  have haug : 1 ≤ finrank F (Fl3.aug Û) :=
    Submodule.one_le_finrank_iff.mpr (Fl3.aug_ne_bot hÛne)
  obtain ⟨L, P, hLP, hL, hP, hcases⟩ := Fl3.exists_flag (Fl3.fix Û) (Fl3.aug Û)
    (Fl3.fix_inf_aug_ne_bot hÛp hÛne) hfix haug (by omega)
  refine no_sylow_two_in_flag hp2 T hT L P hLP hL hP fun g hg => ?_
  have hgn := hnT g hg
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Fl3.mem_stabilizer_fix hgn, Fl3.mem_stabilizer_aug hgn⟩
  · exact ⟨Fl3.mem_stabilizer_aug hgn, Fl3.mem_stabilizer_fix hgn⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
