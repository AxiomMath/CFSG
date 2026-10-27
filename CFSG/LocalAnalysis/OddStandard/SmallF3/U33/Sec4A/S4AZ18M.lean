module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18H

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G]

@[expose] def z18Psi (Y V : Subgroup G) (hN : V ≤ normalizer (Y : Set G)) : ↥V →* MulAut ↥Y :=
  Y.normalizerMonoidHom.comp (Subgroup.inclusion hN)

theorem z18Psi_apply_coe (Y V : Subgroup G) (hN : V ≤ normalizer (Y : Set G)) (g : ↥V)
    (y : ↥Y) : ((z18Psi Y V hN g y : ↥Y) : G) = g * y * g⁻¹ := rfl

theorem z18Psi_eq_one_iff (Y V : Subgroup G) (hN : V ≤ normalizer (Y : Set G)) (g : ↥V) :
    z18Psi Y V hN g = 1 ↔ ∀ y ∈ Y, y * (g : G) = g * y := by
  constructor
  · intro h y hy
    have h1 := congrArg (fun σ : MulAut ↥Y => ((σ ⟨y, hy⟩ : ↥Y) : G)) h
    simp only [z18Psi_apply_coe, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro h
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [z18Psi_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr (h y y.2).symm

theorem z18_psi_pow4 (Y V : Subgroup G) (hN : V ≤ normalizer (Y : Set G)) (hV : IsPGroup 2 V)
    [Finite G] (hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hcard : Nat.card Y = 16) (g : ↥V) : (z18Psi Y V hN g) ^ 4 = 1 := by
  refine z18_exp4_aut (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun y => Subtype.ext (hY2 y y.2)) hcard _ ?_
  obtain ⟨k, hk⟩ := hV g
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem z18_lift_index_two {T : Type} [Group T] {V : Subgroup G} (ψ : ↥V →* T)
    (hψ : Function.Surjective ψ) (MT : Subgroup T) (hMT : MT.index = 2) :
    ∃ M : Subgroup G, M ≤ V ∧ M.relIndex V = 2 ∧ ∀ g : ↥V, (g : G) ∈ M ↔ ψ g ∈ MT := by
  refine ⟨(MT.comap ψ).map V.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact g.2
  · have h1 : ((MT.comap ψ).map V.subtype).subgroupOf V = MT.comap ψ :=
      Subgroup.comap_map_eq_self_of_injective V.subtype_injective _
    rw [Subgroup.relIndex, h1, Subgroup.index_comap_of_surjective _ hψ, hMT]
  · intro g
    constructor
    · rintro ⟨g', hg', hgg⟩
      have : g' = g := Subtype.ext hgg
      subst this
      exact hg'
    · intro hg
      exact ⟨g, hg, rfl⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
