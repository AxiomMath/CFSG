module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem conj_commutes_of_mem_normalizer {R T : Subgroup G} {x g u : G}
    (hTNR : T ≤ normalizer (R : Set G)) (hgR : g ∈ normalizer (R : Set G))
    (huR : u ∈ normalizer (R : Set G)) (hgN : g ∈ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTR : T ⊓ R = ⊥) (hxcT : ∀ t ∈ T, x * t = t * x)
    (huT : ∀ t ∈ T, u * t = t * u) (hux : u * x = x * u)
    (huV : g⁻¹ * u * g ∈ T ⊔ zpowers x) :
    ∀ v ∈ T ⊔ zpowers x, (g⁻¹ * u * g) * v = v * (g⁻¹ * u * g) := by
  have hVnorm : T ⊔ zpowers x ≤ normalizer (T : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have key : x * h * x⁻¹ = h := by
        rw [hxcT h hh, mul_inv_cancel_right]
      rw [key]
      exact hh
    · intro hh
      have key : x * h * x⁻¹ = h := by
        have h2 := hxcT (x * h * x⁻¹) hh
        have h3 : x * h * x⁻¹ * x = x * h := by group
        rw [h3] at h2
        exact mul_left_cancel h2
      rw [key] at hh
      exact hh
  have hwT : ∀ t ∈ T, (g⁻¹ * u * g) * t = t * (g⁻¹ * u * g) := by
    intro t ht
    have hcT : (g⁻¹ * u * g) * t * (g⁻¹ * u * g)⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVnorm huV) t).1 ht) (T.inv_mem ht)
    have hcR : (g⁻¹ * u * g) * t * (g⁻¹ * u * g)⁻¹ * t⁻¹ ∈ R := by
      have htTR : t ∈ T ⊔ R := Subgroup.mem_sup_left ht
      have hs : g * t * g⁻¹ ∈ ((T ⊔ R : Subgroup G) : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hgN t).1 htTR
      rw [Subgroup.coe_mul_of_left_le_normalizer_right T R hTNR] at hs
      obtain ⟨t', ht', r, hr, hprod⟩ := Set.mem_mul.mp hs
      have hX : u * (g * t * g⁻¹) * u⁻¹ * (g * t * g⁻¹)⁻¹ ∈ R := by
        rw [← hprod]
        have e1 : u * (t' * r) * u⁻¹ * (t' * r)⁻¹ = t' * (u * r * u⁻¹ * r⁻¹) * t'⁻¹ := by
          calc u * (t' * r) * u⁻¹ * (t' * r)⁻¹
              = (u * t') * r * u⁻¹ * r⁻¹ * t'⁻¹ := by group
            _ = (t' * u) * r * u⁻¹ * r⁻¹ * t'⁻¹ := by rw [huT t' ht']
            _ = t' * (u * r * u⁻¹ * r⁻¹) * t'⁻¹ := by group
        rw [e1]
        have hq : u * r * u⁻¹ * r⁻¹ ∈ R :=
          R.mul_mem ((Subgroup.mem_normalizer_iff.mp huR r).1 hr) (R.inv_mem hr)
        exact (Subgroup.mem_normalizer_iff.mp (hTNR ht') (u * r * u⁻¹ * r⁻¹)).1 hq
      have hconj : g⁻¹ * (u * (g * t * g⁻¹) * u⁻¹ * (g * t * g⁻¹)⁻¹) * g ∈ R :=
        (Subgroup.mem_normalizer_iff''.mp hgR _).1 hX
      have e2 : (g⁻¹ * u * g) * t * (g⁻¹ * u * g)⁻¹ * t⁻¹
          = g⁻¹ * (u * (g * t * g⁻¹) * u⁻¹ * (g * t * g⁻¹)⁻¹) * g := by group
      rw [e2]
      exact hconj
    have hc1 : (g⁻¹ * u * g) * t * (g⁻¹ * u * g)⁻¹ * t⁻¹ = 1 := by
      have hmem : (g⁻¹ * u * g) * t * (g⁻¹ * u * g)⁻¹ * t⁻¹ ∈ T ⊓ R :=
        Subgroup.mem_inf.mpr ⟨hcT, hcR⟩
      rw [hTR, Subgroup.mem_bot] at hmem
      exact hmem
    have h3 : (g⁻¹ * u * g) * t * (g⁻¹ * u * g)⁻¹ = t := mul_inv_eq_one.mp hc1
    calc (g⁻¹ * u * g) * t
        = (g⁻¹ * u * g) * t * (g⁻¹ * u * g)⁻¹ * (g⁻¹ * u * g) := by group
      _ = t * (g⁻¹ * u * g) := by rw [h3]
  have hVC : T ⊔ zpowers x ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 ?_)
    · intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hxcT t ht
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
  have hwx : x * (g⁻¹ * u * g) = (g⁻¹ * u * g) * x :=
    (Subgroup.mem_centralizer_iff.mp (hVC huV)) x (Set.mem_singleton x)
  have hC : T ⊔ zpowers x ≤ Subgroup.centralizer ({g⁻¹ * u * g} : Set G) := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 ?_)
    · intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hwT t ht
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hwx.symm
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hC hv)) (g⁻¹ * u * g) (Set.mem_singleton _)

theorem conj_commutes_of_hnorm {M R T : Subgroup G} {x : G}
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G))
    (hNn : M ≤ normalizer ((T ⊔ R : Subgroup G) : Set G)) (hTM : T ≤ M)
    (hTR : T ⊓ R = ⊥) (hxM : x ∈ M) (hxcT : ∀ t ∈ T, x * t = t * x)
    {g u : G} (hg : g ∈ M) (hu : u ∈ M) (huT : ∀ t ∈ T, u * t = t * u) (hux : u * x = x * u)
    (huV : g⁻¹ * u * g ∈ T ⊔ zpowers x) :
    ∀ v ∈ T ⊔ zpowers x, (g⁻¹ * u * g) * v = v * (g⁻¹ * u * g) :=
  conj_commutes_of_mem_normalizer (hTM.trans hRn) (hRn hg) (hRn hu) (hNn hg) hTR hxcT huT hux huV

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
