module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreBasic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RTwin

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
open Equiv Equiv.Perm

section Cover

variable {E : Type*} [Group E] [Finite E] {π : E →* A7} {z : E}

omit [Finite E] in
theorem map_involution_of_sq_eq (h : IsDoubleCoverA7 π z) {k : E} (hk : k * k = z) :
    π k * π k = 1 ∧ π k ≠ 1 := by
  refine ⟨by rw [← map_mul, hk, (h.ker_iff z).mpr (Or.inr rfl)], fun h1 => ?_⟩
  rcases (h.ker_iff k).mp h1 with h2 | h2
  · rw [h2, one_mul] at hk
    exact h.ne_one hk.symm
  · rw [h2, h.sq_eq_one] at hk
    exact h.ne_one hk.symm

theorem exists_inverting_cover (h : IsDoubleCoverA7 π z) {k : E} (hk : k * k = z) :
    ∃ w : E, w * k * w⁻¹ = k * z := by
  obtain ⟨hσ2, hσ1⟩ := map_involution_of_sq_eq h hk
  have hσ2' : ((π k : A7) : Perm (Fin 7)) * (π k : Perm (Fin 7)) = 1 := by
    rw [← Subgroup.coe_mul, hσ2]
    rfl
  have hσ1' : ((π k : A7) : Perm (Fin 7)) ≠ 1 := fun h1 => hσ1 (Subtype.ext h1)
  obtain ⟨a, ha1, ha2⟩ := exists_commuting_conj _ hσ2' hσ1'
  obtain ⟨e, he⟩ := h.surjective a
  set w : E := e⁻¹ * k * e with hw
  have hπw : ((π w : A7) : Perm (Fin 7)) =
      ((a : Perm (Fin 7)))⁻¹ * (π k : Perm (Fin 7)) * (a : Perm (Fin 7)) := by
    rw [hw, map_mul, map_mul, map_inv, he]
    rfl
  have hcomm : π (w * k * w⁻¹ * k⁻¹) = 1 := by
    have h1 : π w * π k = π k * π w := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hπw]
      exact ha2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  rcases (h.ker_iff _).mp hcomm with h1 | h1
  · exfalso
    have hwk : w * k = k * w := by
      calc w * k = (w * k * w⁻¹ * k⁻¹) * k * w := by group
        _ = k * w := by rw [h1]; group
    have hw2 : w * w = z := by
      calc w * w = e⁻¹ * (k * k) * e := by rw [hw]; group
        _ = e⁻¹ * z * e := by rw [hk]
        _ = z := by rw [mul_assoc, ← h.central e]; group
    have hwk2 : (w * k) * (w * k) = 1 := by
      calc (w * k) * (w * k) = w * (k * w) * k := by group
        _ = w * (w * k) * k := by rw [hwk]
        _ = (w * w) * (k * k) := by group
        _ = 1 := by rw [hw2, hk, h.sq_eq_one]
    have hπ : π w = π k := by
      have hσinv : (π k)⁻¹ = π k := inv_eq_of_mul_eq_one_right hσ2
      rcases h.eq_one_or_eq_z_of_sq_eq_one hwk2 with h2 | h2
      · have : w = k⁻¹ := eq_inv_of_mul_eq_one_left h2
        rw [this, map_inv, hσinv]
      · have : w = z * k⁻¹ := by rw [← h2]; group
        rw [this, map_mul, (h.ker_iff z).mpr (Or.inr rfl), one_mul, map_inv, hσinv]
    apply ha1
    rw [← hπw, hπ]
  · refine ⟨w, ?_⟩
    calc w * k * w⁻¹ = (w * k * w⁻¹ * k⁻¹) * k := by group
      _ = z * k := by rw [h1]
      _ = k * z := (h.central k).symm

theorem exists_conj_of_sq_eq_cover (h : IsDoubleCoverA7 π z) {k₁ k₂ : E} (hk₁ : k₁ * k₁ = z)
    (hk₂ : k₂ * k₂ = z) : ∃ e : E, e * k₁ * e⁻¹ = k₂ := by
  obtain ⟨h12, h11⟩ := map_involution_of_sq_eq h hk₁
  obtain ⟨h22, h21⟩ := map_involution_of_sq_eq h hk₂
  obtain ⟨g₁, hg₁⟩ := a7_involution_conj (π k₁) h11 h12
  obtain ⟨g₂, hg₂⟩ := a7_involution_conj (π k₂) h21 h22
  obtain ⟨e₀, he₀⟩ := h.surjective (g₂ * g₁⁻¹)
  have hπ : π (e₀ * k₁ * e₀⁻¹) = π k₂ := by
    rw [map_mul, map_mul, map_inv, he₀, ← hg₁, ← hg₂]
    group
  rcases h.eq_or_eq_mul_z_of_map_eq hπ with h1 | h1
  · exact ⟨e₀, h1⟩
  · obtain ⟨w, hw⟩ := exists_inverting_cover h hk₂
    refine ⟨w * e₀, ?_⟩
    have hzw : z * w⁻¹ = w⁻¹ * z := (h.central w⁻¹).symm
    calc w * e₀ * k₁ * (w * e₀)⁻¹ = w * (e₀ * k₁ * e₀⁻¹) * w⁻¹ := by group
      _ = w * k₂ * (z * w⁻¹) := by rw [h1]; group
      _ = w * k₂ * w⁻¹ * z := by rw [hzw]; group
      _ = k₂ * (z * z) := by rw [hw]; group
      _ = k₂ := by rw [h.sq_eq_one, mul_one]

end Cover

section Member

variable {F : Type} [Group F] [Finite F]

theorem exists_conj_in_member {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {k₁ k₂ : F}
    (hk₁K : k₁ ∈ K) (hk₂K : k₂ ∈ K) (hk₁ : k₁ * k₁ = z) (hk₂ : k₂ * k₂ = z) :
    ∃ g ∈ K, g * k₁ * g⁻¹ = k₂ := by
  obtain ⟨π, z', hcov, hcen⟩ := exists_cover_of_witness hK.witness
  have hz' : (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) = z' :=
    ((hcen _).mp (mk_mem_center hK)).resolve_left (mk_ne_one hK)
  have hsq : ∀ (k : F) (hk : k ∈ K), k * k = z →
      (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : OddQuot K) * QuotientGroup.mk (⟨k, hk⟩ : ↥K) = z' := by
    intro k hk hkk
    rw [← hz', ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkk
  obtain ⟨e, he⟩ := exists_conj_of_sq_eq_cover hcov (hsq k₁ hk₁K hk₁) (hsq k₂ hk₂K hk₂)
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective e
  set x : F := (g₀ : F) * k₁ * (g₀ : F)⁻¹ with hx
  have hxK : x ∈ K := K.mul_mem (K.mul_mem g₀.2 hk₁K) (K.inv_mem g₀.2)
  have hmk : (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : OddQuot K) = QuotientGroup.mk ⟨k₂, hk₂K⟩ := by
    rw [← he, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  rw [QuotientGroup.eq] at hmk
  have hxy : x⁻¹ * k₂ ∈ oddCoreOf K :=
    mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.inv_mem hxK) hk₂K, hmk⟩
  have hxx : x * x = z := by
    calc x * x = (g₀ : F) * (k₁ * k₁) * (g₀ : F)⁻¹ := by rw [hx]; group
      _ = z := by rw [hk₁, hK.mul_comm_of_mem g₀.2]; group
  obtain ⟨h, hh, hhx⟩ := AscFusion.exists_conj_of_odd_coset (oddCoreOf_odd_natCard K)
    (AscFusion.isPGroup_zpowers_of_sq_eq hK.mul_self hxx)
    (AscFusion.isPGroup_zpowers_of_sq_eq hK.mul_self hk₂)
    (AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hxK)) hxy
  have hle : oddCoreOf K ⊔ Subgroup.zpowers x ≤ K :=
    sup_le (oddCoreOf_le_self K) (Subgroup.zpowers_le.mpr hxK)
  refine ⟨h * g₀, K.mul_mem (hle hh) g₀.2, ?_⟩
  calc h * g₀ * k₁ * (h * g₀)⁻¹ = h * x * h⁻¹ := by rw [hx]; group
    _ = k₂ := hhx

end Member

end CFSG.ClassicalInvolution.A7Core
