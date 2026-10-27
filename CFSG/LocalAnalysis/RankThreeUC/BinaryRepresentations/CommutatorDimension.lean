module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialHyperplaneVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

namespace CommutatorDimension

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem dimension_formula [Finite G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (X : Subgroup G) (hX : Nat.card X = p)
    (U : Submodule (ZMod 2) V) (hU : ∀ x ∈ X, ∀ u ∈ U, ρ x u ∈ U)
    (hrank : Module.finrank (ZMod 2) U = p * m)
    (hfix : Module.finrank (ZMod 2) ↥(U ⊓ fixedSpace ρ X) = m) :
    Module.finrank (ZMod 2) ↥(commOn ρ X U) = m * (p - 1) := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have hcard : (Fintype.card X : ZMod 2) = 1 := by
    rw [← Nat.card_eq_fintype_card, hX, ZMod.natCast_eq_one_iff_odd]
    exact hp.odd_of_ne_two hp2
  have hmulX : ∀ (y : X) (u : V), ∑ x : X, ρ x (ρ y u) = ∑ x : X, ρ x u := by
    intro y u
    have h1 : ∀ x : X, ρ x (ρ y u) = ρ ((x * y : X) : G) u := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul]
    simp only [h1]
    exact Equiv.sum_comp (Equiv.mulRight y) (fun x : X => ρ x u)
  have hmulX' : ∀ (y : X) (u : V), ρ y (∑ x : X, ρ x u) = ∑ x : X, ρ x u := by
    intro y u
    rw [map_sum]
    have h1 : ∀ x : X, ρ y (ρ x u) = ρ ((y * x : X) : G) u := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul]
    simp only [h1]
    exact Equiv.sum_comp (Equiv.mulLeft y) (fun x : X => ρ x u)
  let f : U →ₗ[ZMod 2] V := (∑ x : X, (ρ x : V →ₗ[ZMod 2] V)).comp U.subtype
  have hf : ∀ u : U, f u = ∑ x : X, ρ x (u : V) := by
    intro u
    simp [f, LinearMap.sum_apply]
  have hker : Submodule.map U.subtype (LinearMap.ker f) = commOn ρ X U := by
    apply le_antisymm
    · rintro w ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hf] at hv
      have key : (v : V) = ∑ x : X, -(ρ x (v : V) - v) := by
        simp [Finset.sum_sub_distrib, hv, Finset.sum_const, Finset.card_univ,
          ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard]
      show (v : V) ∈ commOn ρ X U
      rw [key]
      apply Submodule.sum_mem
      intro x _
      apply Submodule.neg_mem
      apply Submodule.subset_span
      exact ⟨(x : G), x.2, (v : V), v.2, rfl⟩
    · apply Submodule.span_le.mpr
      rintro w ⟨x, hx, u, hu, rfl⟩
      refine ⟨⟨ρ x u - u, sub_mem (hU x hx u hu) hu⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hf]
      simp only [map_sub, Finset.sum_sub_distrib, sub_eq_zero]
      exact hmulX ⟨x, hx⟩ u
  have hrange : LinearMap.range f = U ⊓ BinaryRepresentations.fixedSpace ρ X := by
    apply le_antisymm
    · rintro w ⟨u, rfl⟩
      rw [hf, Submodule.mem_inf]
      refine ⟨Submodule.sum_mem _ (fun x _ => hU x x.2 u u.2), ?_⟩
      rw [BinaryRepresentations.mem_fixedSpace_iff]
      intro y hy
      exact hmulX' ⟨y, hy⟩ _
    · intro w hw
      rw [Submodule.mem_inf] at hw
      obtain ⟨hwU, hwF⟩ := hw
      rw [BinaryRepresentations.mem_fixedSpace_iff] at hwF
      refine ⟨⟨w, hwU⟩, ?_⟩
      rw [hf]
      rw [Finset.sum_congr rfl (fun (x : X) _ => hwF x x.2), Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hfix, hrank] at hrk
  have hk : Module.finrank (ZMod 2) (LinearMap.ker f) =
      Module.finrank (ZMod 2) ↥(commOn ρ X U) := by
    rw [← hker]
    exact (Submodule.finrank_map_subtype_eq U (LinearMap.ker f)).symm
  rw [← hk]
  have hp1 : p - 1 + 1 = p := by have := hp.one_lt; omega
  have h : p * m = m * (p - 1) + m := by
    conv_lhs => rw [← hp1]
    ring
  omega

end CommutatorDimension

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
