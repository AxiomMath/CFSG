module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM7

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

variable {F : Type} [Field F]

theorem negOne_mul_longInv_one : negOne F * longInv F 2 1 = longInv F 2 0 := by
  have e : longInv F 2 1 = negOne F * longInv F 2 0 := longInv_rev_eq 0
  rw [e, ← mul_assoc, negOne_mul_self, one_mul]

namespace Frame

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem aut_image_lift [Finite F] (h2 : (2 : F) ≠ 0) (hzA : IsUniqueInvolution A z')
    (β : Y ≃* Y) (hne' : β z' ≠ z') (hcomm : β z' * z' = z' * β z') :
    ∃ j : StatedSp 2 F, fr.ψ j = β z' ∧ j * j = 1 ∧
      j * longInv F 2 0 * j⁻¹ = longInv F 2 1 := by
  obtain ⟨M, σ, hβ⟩ := fr.exists_lift_aut h2 β
  have hψj := hβ (longInv F 2 0)
  rw [← fr.hz] at hψj
  have hj2 : conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) *
      conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) = 1 := by
    rw [← map_mul, ← map_mul, longInv_mul_self, map_one, map_one]
  generalize conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) = j at hψj hj2
  refine ⟨j, hψj.symm, hj2, ?_⟩
  have hz1 : fr.ψ j * z' * (fr.ψ j)⁻¹ = z' := by
    rw [← hψj, hcomm, mul_inv_cancel_right]
  rcases fr.conj_longInv_cases hz1 with hc | hc
  · exfalso
    have hcomm' : j * longInv F 2 0 = longInv F 2 0 * j := by
      calc j * longInv F 2 0 = j * longInv F 2 0 * j⁻¹ * j := by group
        _ = longInv F 2 0 * j := by rw [hc]
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute_longInv h2 0 hcomm'
    rw [complGroup_longInv_two h2] at hb
    have hsq : a * a * (b * b) = 1 * 1 := by
      calc a * a * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [commute_L 0 ha hb]
        _ = a * b * (a * b) := by group
        _ = 1 * 1 := by rw [hj2, mul_one]
    obtain ⟨haa, hbb⟩ := eq_of_mul_eq_L 0 (mul_mem ha ha) (one_mem _) (mul_mem hb hb)
      (one_mem _) hsq
    have hz2 : z' * z' = 1 := hzA.sq
    have hβ1 : β z' ≠ 1 := by
      intro h
      apply hzA.ne_one
      exact β.injective (by rw [h, map_one])
    rcases sq_eq_one_of_mem_L h2 0 ha haa with rfl | rfl <;>
      rcases sq_eq_one_of_mem_L h2 1 hb hbb with rfl | rfl
    · exact hβ1 (by rw [hψj, mul_one, map_one])
    · exact hne' (by rw [hψj, one_mul, fr.ψ_longInv_one])
    · exact hne' (by rw [hψj, mul_one, ← fr.hz])
    · exact hβ1 (by rw [hψj, map_mul, fr.ψ_longInv_one, ← fr.hz, hz2])
  · exact hc

theorem interchange_aux [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) {a₀ b₀ t' : Y}
    (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ A') (ha₀sq : a₀ * a₀ = z') (hb₀sq : b₀ * b₀ = z')
    {j : StatedSp 2 F} (hψj : fr.ψ j = t') (hj2 : j * j = 1)
    (hji' : j * longInv F 2 0 = longInv F 2 1 * j) :
    ∃ x : Y, x * (z' * t') * x⁻¹ = a₀ * b₀ := by
  have hA0 : a₀ ∈ (longRootSp2 F 2 0).map fr.ψ := fr.hA ▸ ha₀
  have hA1 : b₀ ∈ (longRootSp2 F 2 1).map fr.ψ := fr.hA' ▸ hb₀
  obtain ⟨α, hα, rfl⟩ := hA0
  obtain ⟨β', hβ', rfl⟩ := hA1
  have hαsq : α * α = longInv F 2 0 := by
    have h0 : fr.ψ (α * α) = fr.ψ (longInv F 2 0) := by rw [map_mul, ha₀sq]; exact fr.hz
    rcases fr.lift_eq_iff.mp h0 with h | h
    · exact h
    · exfalso
      have e : longInv F 2 0 * negOne F = longInv F 2 1 := by
        rw [← negOne_comm]
        exact (longInv_rev_eq 0).symm
      have hm : longInv F 2 1 ∈ longRootSp2 F 2 0 := by
        rw [← e, ← h]
        exact mul_mem hα hα
      exact longInv_rev_not_mem h2 0 hm
  have hβsq : β' * β' = longInv F 2 1 := by
    have h0 : fr.ψ (β' * β') = fr.ψ (longInv F 2 1) := by
      rw [map_mul, hb₀sq, fr.ψ_longInv_one]
    rcases fr.lift_eq_iff.mp h0 with h | h
    · exact h
    · exfalso
      have e : longInv F 2 1 * negOne F = longInv F 2 0 := by
        rw [← negOne_comm, negOne_mul_longInv_one]
      have hm : longInv F 2 0 ∈ longRootSp2 F 2 1 := by
        rw [← e, ← h]
        exact mul_mem hβ' hβ'
      exact longInv_rev_not_mem h2 1 hm
  have hab : α * β' * (α * β') = negOne F := by
    calc α * β' * (α * β') = α * (β' * α) * β' := by group
      _ = α * (α * β') * β' := by rw [commute_L 0 hα hβ']
      _ = α * α * (β' * β') := by group
      _ = negOne F := by rw [hαsq, hβsq]; rfl
  obtain ⟨g₂, hg₂⟩ := exists_conj_rho_of_mem hodd 0 hα hβ' hab
  have hij : longInv F 2 0 * j * (longInv F 2 0 * j) = negOne F := by
    calc longInv F 2 0 * j * (longInv F 2 0 * j) = longInv F 2 0 * (j * longInv F 2 0) * j := by
          group
      _ = longInv F 2 0 * (longInv F 2 1 * j) * j := by rw [hji']
      _ = longInv F 2 0 * longInv F 2 1 * (j * j) := by group
      _ = negOne F := by rw [hj2, mul_one]; rfl
  obtain ⟨g₁, hg₁⟩ := exists_conj_rho h2 hodd hij
  refine ⟨fr.ψ (g₂⁻¹ * g₁), ?_⟩
  have e : g₂⁻¹ * g₁ * (longInv F 2 0 * j) * (g₂⁻¹ * g₁)⁻¹ = α * β' := by
    calc g₂⁻¹ * g₁ * (longInv F 2 0 * j) * (g₂⁻¹ * g₁)⁻¹ =
        g₂⁻¹ * (g₁ * (longInv F 2 0 * j) * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * (α * β') * g₂⁻¹) * g₂ := by rw [hg₁, hg₂]
      _ = α * β' := by group
  have h := congrArg fr.ψ e
  simp only [map_mul, map_inv] at h ⊢
  rw [← fr.hz, hψj] at h
  exact h

theorem interchange [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    (hzA : IsUniqueInvolution A z') {a₀ b₀ : Y} (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ A')
    (ha₀sq : a₀ * a₀ = z') (hb₀sq : b₀ * b₀ = z') (β : Y ≃* Y) (t' : Y) (ht' : t' = β z')
    (hne' : t' ≠ z') (hcomm : t' * z' = z' * t') :
    (∃ x : Y, x * z' * x⁻¹ = t' ∧ x * t' * x⁻¹ = z') ∧
      ∃ x : Y, x * (z' * t') * x⁻¹ = a₀ * b₀ := by
  subst ht'
  obtain ⟨j, hψj, hj2, hji⟩ := fr.aut_image_lift h2 hzA β hne' hcomm
  have hji' : j * longInv F 2 0 = longInv F 2 1 * j := by
    calc j * longInv F 2 0 = j * longInv F 2 0 * j⁻¹ * j := by group
      _ = longInv F 2 1 * j := by rw [hji]
  have hj1 : j * longInv F 2 1 = longInv F 2 0 * j := by
    have e : longInv F 2 1 = negOne F * longInv F 2 0 := longInv_rev_eq 0
    calc j * longInv F 2 1 = j * negOne F * longInv F 2 0 := by rw [e, mul_assoc]
      _ = negOne F * (j * longInv F 2 0) := by rw [← negOne_comm, mul_assoc]
      _ = negOne F * (longInv F 2 1 * j) := by rw [hji']
      _ = longInv F 2 0 * j := by rw [← mul_assoc, negOne_mul_longInv_one]
  have hc : j * sw F * longInv F 2 0 = longInv F 2 0 * (j * sw F) := by
    calc j * sw F * longInv F 2 0 = j * (sw F * longInv F 2 0) := by group
      _ = j * (longInv F 2 1 * sw F) := by rw [sw_mul_longInv]; rfl
      _ = j * longInv F 2 1 * sw F := by group
      _ = longInv F 2 0 * (j * sw F) := by rw [hj1]; group
  obtain ⟨x, hx, w, hw, hxw⟩ := exists_mul_of_commute_longInv h2 0 hc
  rw [complGroup_longInv_two h2, rev_zero] at hw
  have hjx : j = x * w * sw F := by
    calc j = j * sw F * sw F := by rw [mul_assoc, sw_mul_self, mul_one]
      _ = x * w * sw F := by rw [hxw]
  have hx' : sw F * x * sw F ∈ longRootSp2 F 2 1 := by
    have := Subgroup.mem_map_of_mem (MulAut.conj (sw F)).toMonoidHom hx
    rw [map_sw_L h2 0] at this
    simpa [sw_inv] using this
  have hw' : sw F * w * sw F ∈ longRootSp2 F 2 0 := by
    have := Subgroup.mem_map_of_mem (MulAut.conj (sw F)).toMonoidHom hw
    rw [map_sw_L h2 1] at this
    simpa [sw_inv] using this
  have e1 : j * j = x * w * (sw F * x * sw F) * (sw F * w * sw F) := by
    rw [hjx]
    calc x * w * sw F * (x * w * sw F) = x * w * (sw F * x * (sw F * sw F) * w * sw F) := by
          rw [sw_mul_self]; group
      _ = x * w * (sw F * x * sw F) * (sw F * w * sw F) := by group
  have hprod : x * (sw F * w * sw F) * (w * (sw F * x * sw F)) = 1 * 1 := by
    rw [mul_one, ← hj2, e1]
    calc x * (sw F * w * sw F) * (w * (sw F * x * sw F)) =
        x * ((sw F * w * sw F) * (w * (sw F * x * sw F))) := by group
      _ = x * ((w * (sw F * x * sw F)) * (sw F * w * sw F)) := by
          rw [commute_L 0 hw' (mul_mem hw hx')]
      _ = x * w * (sw F * x * sw F) * (sw F * w * sw F) := by group
  obtain ⟨hxw', -⟩ := eq_of_mul_eq_L 0 (mul_mem hx hw') (one_mem _) (mul_mem hw hx')
    (one_mem _) hprod
  have hw_eq : w = sw F * x⁻¹ * sw F := by
    have h1 : sw F * w * sw F = x⁻¹ := eq_inv_of_mul_eq_one_right hxw'
    calc w = sw F * (sw F * w * sw F) * sw F := by
          rw [← mul_assoc, ← mul_assoc, sw_mul_self, one_mul, mul_assoc, sw_mul_self, mul_one]
      _ = sw F * x⁻¹ * sw F := by rw [h1]
  have hj_eq : j = x * sw F * x⁻¹ := by
    rw [hjx, hw_eq]
    calc x * (sw F * x⁻¹ * sw F) * sw F = x * sw F * x⁻¹ * (sw F * sw F) := by group
      _ = x * sw F * x⁻¹ := by rw [sw_mul_self, mul_one]
  have hxi0 : x⁻¹ * longInv F 2 0 * x = longInv F 2 0 := by
    rw [mul_assoc, longInv_comm_L 0 0 hx, ← mul_assoc, inv_mul_cancel, one_mul]
  have hxi1 : x * longInv F 2 1 * x⁻¹ = longInv F 2 1 := by
    rw [← longInv_comm_L 1 0 hx, mul_inv_cancel_right]
  have hm1 : x * xMat h2 * x⁻¹ * longInv F 2 0 * (x * xMat h2 * x⁻¹)⁻¹ = j := by
    calc x * xMat h2 * x⁻¹ * longInv F 2 0 * (x * xMat h2 * x⁻¹)⁻¹ =
        x * xMat h2 * (x⁻¹ * longInv F 2 0 * x) * (xMat h2)⁻¹ * x⁻¹ := by group
      _ = x * (xMat h2 * longInv F 2 0 * (xMat h2)⁻¹) * x⁻¹ := by rw [hxi0]; group
      _ = j := by rw [xMat_conj_longInv, hj_eq]
  have hm2 : x * xMat h2 * x⁻¹ * j * (x * xMat h2 * x⁻¹)⁻¹ = longInv F 2 1 := by
    rw [hj_eq]
    calc x * xMat h2 * x⁻¹ * (x * sw F * x⁻¹) * (x * xMat h2 * x⁻¹)⁻¹ =
        x * (xMat h2 * sw F * (xMat h2)⁻¹) * x⁻¹ := by group
      _ = longInv F 2 1 := by rw [xMat_conj_sw, hxi1]
  refine ⟨⟨fr.ψ (x * xMat h2 * x⁻¹), ?_, ?_⟩, ?_⟩
  · have h := congrArg fr.ψ hm1
    rw [map_mul, map_mul, map_inv, ← fr.hz, hψj] at h
    exact h
  · have h := congrArg fr.ψ hm2
    rw [map_mul, map_mul, map_inv, hψj, fr.ψ_longInv_one] at h
    exact h
  · exact fr.interchange_aux h2 hodd ha₀ hb₀ ha₀sq hb₀sq hψj hj2 hji'

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
