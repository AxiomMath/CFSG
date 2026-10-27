module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BAux

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup Module

theorem two_pow_le_card_conj_of_hyperplane {H W : Type*} [Group H] [Finite H] [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] (E : Subgroup H) (t n : H)
    (hn : n ∈ centralizer ({t} : Set H)) (hnE : ∀ e ∈ E, n * e * n⁻¹ ∈ E)
    (ψ : E → W) (hψ : ∀ e e', ψ (e * e') = ψ e + ψ e') (hsurj : Function.Surjective ψ)
    (T : W →ₗ[ZMod 2] W) (hT : ∀ e : E, ψ ⟨n * e * n⁻¹, hnE e e.2⟩ = T (ψ e))
    (l : W →ₗ[ZMod 2] ZMod 2) (hl : ∀ e : E, l (ψ e) = 0 → (e : H) * t = t * e) {r : ℕ}
    (hr : r ≤ finrank (ZMod 2) (LinearMap.range (T - 1))) :
    2 ^ (r - 1) ≤ Nat.card {y : centralizer ({t} : Set H) //
      IsConj (⟨n, hn⟩ : centralizer ({t} : Set H)) y} := by
  classical
  have hψ1 : ψ 1 = 0 := by
    have h := hψ 1 1
    rw [mul_one] at h
    exact left_eq_add.1 h
  have hψinv : ∀ e : E, ψ e⁻¹ = - ψ e := fun e => by
    have h := hψ e e⁻¹
    rw [mul_inv_cancel, hψ1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have htn : n * t = t * n := mem_centralizer_singleton_iff.1 hn
  let φ : {y : centralizer ({t} : Set H) //
      IsConj (⟨n, hn⟩ : centralizer ({t} : Set H)) y} → W := fun y =>
    if h : ((y : centralizer ({t} : Set H)) : H) * n⁻¹ ∈ E then ψ ⟨_, h⟩ else 0
  refine le_trans (two_pow_le_card_map_ker (T - 1) l hr) ?_
  refine ncard_le_card_of_exists_preimage φ
    (↑(Submodule.map (T - 1) (LinearMap.ker l)) : Set W) ?_
  rintro v ⟨w, hw, rfl⟩
  obtain ⟨e, rfl⟩ := hsurj w
  have he : (e : H) * t = t * e := hl e (LinearMap.mem_ker.1 hw)
  have hte : Commute t (e : H) := he.symm
  have hy : Commute t ((e : H) * n * (e : H)⁻¹) :=
    (hte.mul_right (show Commute t n from htn.symm)).mul_right hte.inv_right
  have heC : (e : H) ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.2 he
  have hyC : (e : H) * n * (e : H)⁻¹ ∈ centralizer ({t} : Set H) :=
    mem_centralizer_singleton_iff.2 hy.eq.symm
  have hconj : IsConj (⟨n, hn⟩ : centralizer ({t} : Set H)) ⟨(e : H) * n * (e : H)⁻¹, hyC⟩ :=
    isConj_iff.2 ⟨⟨e, heC⟩, Subtype.ext rfl⟩
  have hE : (e : H) * n * (e : H)⁻¹ * n⁻¹ ∈ E := by
    have h1 := E.mul_mem e.2 (hnE _ (E.inv_mem e.2))
    have h2 : (e : H) * n * (e : H)⁻¹ * n⁻¹ = (e : H) * (n * (e : H)⁻¹ * n⁻¹) := by group
    rw [h2]
    exact h1
  refine ⟨⟨⟨(e : H) * n * (e : H)⁻¹, hyC⟩, hconj⟩, ?_⟩
  have hφ : φ ⟨⟨(e : H) * n * (e : H)⁻¹, hyC⟩, hconj⟩ =
      ψ ⟨(e : H) * n * (e : H)⁻¹ * n⁻¹, hE⟩ := by simp [φ, hE]
  rw [hφ]
  have hsplit : (⟨(e : H) * n * (e : H)⁻¹ * n⁻¹, hE⟩ : E) =
      e * ⟨n * ((e⁻¹ : E) : H) * n⁻¹, hnE _ (E.inv_mem e.2)⟩ :=
    Subtype.ext (by simp [mul_assoc])
  rw [hsplit, hψ, show (⟨n * ((e⁻¹ : E) : H) * n⁻¹, hnE _ (E.inv_mem e.2)⟩ : E) =
    ⟨n * (e⁻¹ : E) * n⁻¹, hnE (e⁻¹ : E) (e⁻¹ : E).2⟩ from rfl, hT, hψinv, map_neg,
    LinearMap.sub_apply, Module.End.one_apply, ← sub_eq_add_neg, ← neg_sub, ZModModule.neg_eq_self]

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
