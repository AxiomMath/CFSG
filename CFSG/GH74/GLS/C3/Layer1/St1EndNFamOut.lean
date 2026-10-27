module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.St1EndNCfg

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem x_mem_L_of_outer_commutator_cube (h : Lem711Cfg X L K x y)
    (hc : ∀ τ ∈ ⁅(⊤ : Subgroup (Outer ↥L)), (⊤ : Subgroup (Outer ↥L))⁆, τ ^ 3 = 1) : x ∈ L := by
  have := h.normal
  let φ : X →* MulAut ↥L := MulAut.conjNormal
  let π : MulAut ↥L →* Outer ↥L := QuotientGroup.mk' (inner ↥L)
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  have h1 : π (φ x) ∈ ⁅(⊤ : Subgroup (Outer ↥L)), (⊤ : Subgroup (Outer ↥L))⁆ := by
    have hx := h.x_mem_commutator
    have h2 : (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map (π.comp φ) ≤
        ⁅(⊤ : Subgroup (Outer ↥L)), (⊤ : Subgroup (Outer ↥L))⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 ⟨x, hx, rfl⟩
  have h3 : (π (φ x)) ^ 3 = 1 := hc _ h1
  have h4 : (π (φ x)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, pow_two, hxx, map_one, map_one]
  have h5 : π (φ x) = 1 := by
    calc π (φ x) = (π (φ x)) ^ 3 * ((π (φ x)) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h4]; simp
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).1 h5
  have hcomm : ∀ m ∈ L, ((l : X)⁻¹ * x) * m = m * ((l : X)⁻¹ * x) := by
    intro m hm
    have h2 := congrArg (fun a : MulAut ↥L => ((a ⟨m, hm⟩ : ↥L) : X)) hl
    simp only [φ, MulAut.conjNormal_apply] at h2
    change (l : X) * m * (l : X)⁻¹ = x * m * x⁻¹ at h2
    calc ((l : X)⁻¹ * x) * m = (l : X)⁻¹ * (x * m * x⁻¹) * x := by group
      _ = (l : X)⁻¹ * ((l : X) * m * (l : X)⁻¹) * x := by rw [h2]
      _ = m * ((l : X)⁻¹ * x) := by group
  have h6 := h.soc.centralizer_trivial _ (Subgroup.mem_top _) hcomm
  have h7 : x = (l : X) := (inv_mul_eq_one.1 h6).symm
  rw [h7]
  exact l.2

end Lem711Cfg


end CFSG.GH74.GLS
