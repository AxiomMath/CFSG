module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerExt
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerHyp

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup CFSG.SCATWreath

variable {G : Type*} [Group G]

@[expose] def IsPInvol (K : Subgroup G) (x : G) : Prop :=
  x ∈ K ∧ x ^ 2 = 1 ∧ x ≠ 1 ∧ PInv (K ⊓ centralizer {x})

theorem pinv_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {H : Subgroup X} {H' : Subgroup Y}
    (e : H ≃* H') (h : PInv H) : PInv H' := by
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans h.1, ?_⟩
  rw [← h.2]
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow,
    map_eq_one_iff e e.injective, ne_eq]

def centConj {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) (x : G) :
    (K ⊓ centralizer {x} : Subgroup G) ≃* (K ⊓ centralizer {g * x * g⁻¹} : Subgroup G) where
  toFun k := ⟨g * k * g⁻¹, mem_inf.2 ⟨conj_mem_of_norm hg (mem_inf.1 k.2).1,
    mem_centralizer_singleton_iff.2 (by
      have hk := mem_centralizer_singleton_iff.1 (mem_inf.1 k.2).2
      calc g * k * g⁻¹ * (g * x * g⁻¹) = g * (k * x) * g⁻¹ := by group
        _ = g * (x * k) * g⁻¹ := by rw [hk]
        _ = g * x * g⁻¹ * (g * k * g⁻¹) := by group)⟩⟩
  invFun k := ⟨g⁻¹ * k * g, mem_inf.2 ⟨inv_conj_mem hg (mem_inf.1 k.2).1,
    mem_centralizer_singleton_iff.2 (by
      have hk := mem_centralizer_singleton_iff.1 (mem_inf.1 k.2).2
      calc g⁻¹ * k * g * x = g⁻¹ * (k * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹ * k) * g := by rw [hk]
        _ = x * (g⁻¹ * k * g) := by group)⟩⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [coe_mul]; group)

theorem pinvol_conj {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) {x : G}
    (hx : IsPInvol K x) : IsPInvol K (g * x * g⁻¹) := by
  obtain ⟨hxK, hx2, hx1, hP⟩ := hx
  refine ⟨conj_mem_of_norm hg hxK, ?_, ?_, pinv_of_mulEquiv (centConj hg x) hP⟩
  · rw [conj_pow, hx2]
    group
  · intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

variable {K : Subgroup G} {n : ℕ} {mul : ℕ → ℕ → ℕ} {dec : ℕ → G}

variable {gens : Array ℕ}

end CFSG.OddStandard.AltStdSmall4.Tower
