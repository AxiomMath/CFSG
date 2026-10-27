module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup

variable {G A : Type*} [Group G] [Group A]

@[expose] def fixedRestrict (σ : G →* G) (σ' : A →* A) (Θ : A →* G) (hσ : σ.comp Θ = Θ.comp σ') :
    ↥(MonoidHom.eqLocus σ' (MonoidHom.id A)) →* ↥(MonoidHom.eqLocus σ (MonoidHom.id G)) :=
  (Θ.comp (MonoidHom.eqLocus σ' (MonoidHom.id A)).subtype).codRestrict
    (MonoidHom.eqLocus σ (MonoidHom.id G)) fun g => by
      have h1 := DFunLike.congr_fun hσ (g : A)
      have h2 : σ' (g : A) = (g : A) := g.2
      change σ (Θ (g : A)) = Θ (g : A)
      simpa only [MonoidHom.comp_apply, h2] using h1

theorem coe_fixedRestrict (σ : G →* G) (σ' : A →* A) (Θ : A →* G)
    (hσ : σ.comp Θ = Θ.comp σ') (g : ↥(MonoidHom.eqLocus σ' (MonoidHom.id A))) :
    ((fixedRestrict σ σ' Θ hσ g : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G) = Θ (g : A) :=
  rfl

theorem fixedRestrict_injective (σ : G →* G) (σ' : A →* A) (Θ : A →* G)
    (hσ : σ.comp Θ = Θ.comp σ') (hinj : Function.Injective Θ) :
    Function.Injective (fixedRestrict σ σ' Θ hσ) := fun a b h =>
  Subtype.ext (hinj (congrArg Subtype.val h))

theorem normal_range_fixedRestrict (σ : G →* G) (σ' : A →* A) (Θ : A →* G)
    (hσ : σ.comp Θ = Θ.comp σ') (hinj : Function.Injective Θ) {u : G} (hu : σ u = u)
    (hnorm : (Θ.range.subgroupOf (centralizer ({u} : Set G))).Normal) :
    ((fixedRestrict σ σ' Θ hσ).range.subgroupOf
      (centralizer ({(⟨u, hu⟩ : ↥(MonoidHom.eqLocus σ (MonoidHom.id G)))} :
        Set ↥(MonoidHom.eqLocus σ (MonoidHom.id G))))).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
  have hxa : (((x : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G)) = Θ (a : A) :=
    (congrArg Subtype.val ha).symm
  have hxc : Commute (((x : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G)) u :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2)
  have hgc : Commute (((g : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G)) u :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hxσ : σ (((x : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G)) =
      ((x : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G) := x.1.2
  have hgσ : σ (((g : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G)) =
      ((g : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G) := g.1.2
  have hxC : ((x : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G) ∈ centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxc.eq
  have hgC : ((g : ↥(MonoidHom.eqLocus σ (MonoidHom.id G))) : G) ∈ centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hgc.eq
  have hn : (⟨_, hxC⟩ : ↥(centralizer ({u} : Set G))) ∈
      Θ.range.subgroupOf (centralizer ({u} : Set G)) := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(a : A), hxa.symm⟩
  have hconj := hnorm.conj_mem _ hn ⟨_, hgC⟩
  rw [Subgroup.mem_subgroupOf] at hconj
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hconj
  have hσb : σ' b = b := by
    apply hinj
    have e1 : Θ (σ' b) = σ (Θ b) := (DFunLike.congr_fun hσ b).symm
    rw [e1, hb]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hgσ, hxσ]
  refine MonoidHom.mem_range.2 ⟨⟨b, hσb⟩, Subtype.ext ?_⟩
  rw [coe_fixedRestrict]
  exact hb

end CFSG.OddStandard.HigherRank.F3
