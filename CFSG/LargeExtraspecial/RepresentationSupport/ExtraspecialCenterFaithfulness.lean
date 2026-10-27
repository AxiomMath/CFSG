module

public import Mathlib.RepresentationTheory.Invariants
public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter

public section

open Subgroup

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialCenterFaithfulness

theorem injective_of_center_invariants_eq_bot
    {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] [Nontrivial W]
    {p : ℕ} (hp : p.Prime) {E : Type*} [Group E] [Finite E]
    (hE : CFSG.IsExtraspecialPGroup p E)
    (σ : Representation F E W)
    (hinv : Representation.invariants (σ.comp (Subgroup.center E).subtype) = ⊥) :
    Function.Injective σ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpg, -, -, hcard⟩ := hE
  rw [injective_iff_map_eq_one]
  have hK : σ.ker ⊓ Subgroup.center E = ⊥ := by
    by_contra hne
    obtain ⟨⟨z, hz⟩, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
    have hzK : σ (z : E) = 1 := hz.1
    have hzc : (z : E) ∈ Subgroup.center E := hz.2
    set z' : Subgroup.center E := ⟨z, hzc⟩ with hz'
    have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have htop := zpowers_eq_top_of_prime_card hcard hz'1
    have hall : Representation.invariants (σ.comp (Subgroup.center E).subtype) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [Representation.mem_invariants]
      intro c
      have hc : c ∈ zpowers z' := by rw [htop]; trivial
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
      subst hn
      show σ (z ^ n) v = v
      have h1 : σ (z ^ n) = 1 := (σ.ker.zpow_mem hz.1 n)
      rw [h1]
      rfl
    rw [hall] at hinv
    exact (bot_ne_top (α := Submodule F W)) hinv.symm
  have := CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.eq_bot_of_inf_center_eq_bot hpg σ.ker hK
  intro g hg
  have : g ∈ σ.ker := hg
  simp_all
