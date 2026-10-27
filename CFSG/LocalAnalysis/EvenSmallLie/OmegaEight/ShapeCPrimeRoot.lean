module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeAff
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeCheck

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

section Refl


theorem bmulVec_reflRows (ε : Eps) {v x : ℕ} (hv : v < 64) (hx : x < 64) :
    bmulVec 6 6 (reflRows ε v) x = reflB ε v x := by
  have h := (cprimeChecks ε).1
  simp only [reflRowsCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h v hv x hx

theorem mulVec_reflRows (ε : Eps) {v : ℕ} (hv : v < 64) (x : V6) :
    toMat 6 6 (reflRows ε v) *ᵥ x = toVec 6 (reflB ε v (vecBits x)) := by
  conv_lhs => rw [← toVec_vecBits x]
  rw [mulVec_toVec, bmulVec_reflRows ε hv (vecBits_lt x)]

theorem add_refl (ε : Eps) {v : ℕ} (hv : v < 64) (x : V6) :
    x + toMat 6 6 (reflRows ε v) *ᵥ x = 0 ∨ x + toMat 6 6 (reflRows ε v) *ᵥ x = toVec 6 v := by
  have h : x + toMat 6 6 (reflRows ε v) *ᵥ x =
      toVec 6 (if bfB ε (vecBits x) v then v else 0) := by
    have hx : toVec 6 (vecBits x) = x := toVec_vecBits x
    calc x + toMat 6 6 (reflRows ε v) *ᵥ x =
        toVec 6 (vecBits x) + toVec 6 (reflB ε v (vecBits x)) := by
          rw [mulVec_reflRows ε hv, hx]
      _ = toVec 6 (vecBits x ^^^ reflB ε v (vecBits x)) := (toVec_xor _ _).symm
      _ = _ := by rw [reflB, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [h]
  split_ifs
  · exact Or.inr rfl
  · left
    ext i
    simp [toVec]

end Refl

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem tψ_mul_tψ (v w : V6) : t * ψ v * (t * ψ w) = ψ (v + w) := by
  calc t * ψ v * (t * ψ w) = t * (ψ v * t) * ψ w := by group
    _ = t * (t * ψ v) * ψ w := by rw [hS.commute_ψ v]
    _ = (t * t) * (ψ v * ψ w) := by group
    _ = ψ (v + w) := by rw [hS.shape.mul_self, one_mul, hS.rad.ψ_add]

theorem square_root {k : G} (hk : k ∈ Kgrp t Q)
    (hcomm : ∀ v, aff t ψ k (aff t ψ c v) = aff t ψ c (aff t ψ k v)) :
    aff t ψ k 0 = 0 ∨ aff t ψ k 0 = toVec 6 v₀ := by
  set kk : Kgrp t Q := ⟨k, hk⟩
  set cc : Kgrp t Q := ⟨c, hS.c_mem_Kgrp⟩
  have hc : hS.affHom kk * hS.affHom cc = hS.affHom cc * hS.affHom kk :=
    Equiv.ext fun v => hcomm v
  have h1 : hS.affHom (kk * cc * kk⁻¹ * cc⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have he : k * c * k⁻¹ * c⁻¹ ∈ Q ⊔ zpowers t := (hS.affHom_eq_one_iff _).1 h1
  set e := k * c * k⁻¹ * c⁻¹ with he_def
  have hkt : k * t * k⁻¹ = e * (c * e * c⁻¹) * t := by
    have hkc : k * c * k⁻¹ = e * c := by rw [he_def]; group
    calc k * t * k⁻¹ = (k * c * k⁻¹) * (k * c * k⁻¹) := by rw [← hS.shape.sq]; group
      _ = (e * c) * (e * c) := by rw [hkc]
      _ = e * (c * e * c⁻¹) * (c * c) := by group
      _ = e * (c * e * c⁻¹) * t := by rw [hS.shape.sq]
  have hct : c * t * c⁻¹ = t := by rw [hS.shape.c_comm, mul_inv_cancel_right]
  have key : ∃ x, k * t * k⁻¹ = t * ψ (x + toMat 6 6 (reflRows ε v₀) *ᵥ x) := by
    obtain ⟨x, hx | hx⟩ := hS.mem_E_iff.1 he
    · refine ⟨x, ?_⟩
      rw [hkt, hx, hS.data.c_act, ← hS.rad.ψ_add, ← hS.commute_ψ]
    · refine ⟨x, ?_⟩
      have hce : c * e * c⁻¹ = t * ψ (toMat 6 6 (reflRows ε v₀) *ᵥ x) := by
        rw [hx]
        calc c * (t * ψ x) * c⁻¹ = (c * t * c⁻¹) * (c * ψ x * c⁻¹) := by group
          _ = t * ψ (toMat 6 6 (reflRows ε v₀) *ᵥ x) := by rw [hct, hS.data.c_act]
      rw [hkt, hce, hx, hS.tψ_mul_tψ, ← hS.commute_ψ]
  obtain ⟨x, hx⟩ := key
  have h2 : aff t ψ k 0 = x + toMat 6 6 (reflRows ε v₀) *ᵥ x :=
    hS.tψ_injective (by rw [← hS.conj_t_aff hk, hx])
  rw [h2]
  exact add_refl ε hS.data.v₀_lt x

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime
