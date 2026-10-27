module

public import CFSG.GH74.GLS.Balance.CompSwap
public import CFSG.GroupTheory.SubnormalJoin

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isComponent_diagonal {x : X} (hx : orderOf x = 2) {K : Subgroup X} (hK : IsComponent K)
    (hKx : x ∉ normalizer (K : Set X)) :
    ∃ J : Subgroup X, J ≤ centralizer ({x} : Set X) ∧
      IsComponent (J.subgroupOf (centralizer ({x} : Set X))) ∧
      ∀ k ∈ K, k * (x * k * x⁻¹) ∈ J := by
  have hx2 : x * x = 1 := by
    have : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    rwa [pow_two] at this
  have hc := Comp.swap_commute hK hKx
  obtain ⟨φ, hφ⟩ := Comp.exists_diagHom hc
  have hker := Comp.diagHom_ker_le_center hc hφ
  have hcen := Comp.diagHom_mem_centralizer hx2 hc hφ
  have hJC : φ.range ≤ centralizer ({x} : Set X) := by
    rintro _ ⟨k, rfl⟩
    exact hcen k
  refine ⟨φ.range, hJC, ⟨?_, ?_⟩, fun k hk => ⟨⟨k, hk⟩, hφ ⟨k, hk⟩⟩⟩
  · have hq : IsQuasisimple φ.range :=
      CFSG.LocalCores.isQuasisimple_of_surjective hK.1 φ.rangeRestrict
        φ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hq
  · have hK' : IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK
    have hD : (K ⊔ K.map (MulAut.conj x).toMonoidHom).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_sup hK.2 hK'.2
    have hK'c : ∀ y ∈ K.map (MulAut.conj x).toMonoidHom, y ∈ centralizer (K : Set X) := by
      rintro _ ⟨b, hb, rfl⟩
      rw [mem_centralizer_iff]
      intro a ha
      exact hc a ha b hb
    have hDn : K ⊔ K.map (MulAut.conj x).toMonoidHom ≤ normalizer (K : Set X) :=
      sup_le Subgroup.le_normalizer fun y hy => Subgroup.centralizer_le_normalizer _ (hK'c y hy)
    have key : ∀ d ∈ K ⊔ K.map (MulAut.conj x).toMonoidHom, d * x = x * d →
        ∀ k₀ : K, d * φ k₀ * d⁻¹ ∈ φ.range := by
      intro d hd hdx k₀
      have hk₁ : d * k₀ * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hDn hd) k₀).mp k₀.2
      refine ⟨⟨d * k₀ * d⁻¹, hk₁⟩, ?_⟩
      have hxd : x * d * x⁻¹ = d := by rw [← hdx]; group
      simp only [hφ]
      calc d * k₀ * d⁻¹ * (x * (d * k₀ * d⁻¹) * x⁻¹)
          = d * k₀ * d⁻¹ * ((x * d * x⁻¹) * (x * k₀ * x⁻¹) * (x * d * x⁻¹)⁻¹) := by group
        _ = d * k₀ * d⁻¹ * (d * (x * k₀ * x⁻¹) * d⁻¹) := by rw [hxd]
        _ = d * ((k₀ : X) * (x * k₀ * x⁻¹)) * d⁻¹ := by group
    have hJD : φ.range ≤ K ⊔ K.map (MulAut.conj x).toMonoidHom := by
      rintro _ ⟨k, rfl⟩
      rw [hφ]
      exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨k, k.2, rfl⟩)
    have hle : φ.range.subgroupOf (centralizer ({x} : Set X)) ≤
        (K ⊔ K.map (MulAut.conj x).toMonoidHom).subgroupOf (centralizer ({x} : Set X)) :=
      fun h hh => hJD hh
    have hnorm : ((φ.range.subgroupOf (centralizer ({x} : Set X))).subgroupOf
        ((K ⊔ K.map (MulAut.conj x).toMonoidHom).subgroupOf (centralizer ({x} : Set X)))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle]
      intro h g hh hg
      obtain ⟨k₀, hk₀⟩ := hh
      have hgx : (g : X) * x = x * (g : X) := Subgroup.mem_centralizer_singleton_iff.mp g.2
      have hk₀' : φ k₀ = (h : X) := hk₀
      rw [Subgroup.mem_subgroupOf]
      change (g : X) * h * (g : X)⁻¹ ∈ φ.range
      rw [← hk₀']
      exact key g hg hgx k₀
    exact Subgroup.IsSubnormal.trans hle hnorm.isSubnormal hD.subgroupOf

end CFSG.GH74.GLS.Balance
