module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.innerModOdd_conj_swap (hs : Z2SetR r n R S t J u R₀ T₀ P) {b : Y}
    (hbt : b * t * b⁻¹ = u) (x : Y) :
    InnerModOdd (linkLayer R t) x ↔
      InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (b * x * b⁻¹) := by
  rw [innerModOdd_conj_iff x b, hs.conjSub_Λt_swap hbt]

theorem Z2SetR.invOutsideA_of_inner_sq (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hSplit : Z2BigSplit r n) (hr : 4 ≤ r) (hall : NoA1All R t J u) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbA : b ∉ edgeCent (P : Subgroup Y) t u)
    (hin : InnerModOdd (linkLayer R t) (b * b)) : InvOutsideA (P : Subgroup Y) t u := by
  have hbt := hs.swap_of_not_mem hbP hbA
  have hbu := hs.swap_u hbP hbt
  have hbt' : b⁻¹ * t * b⁻¹⁻¹ = u := inv_conj_of_conj hbu
  have hbu' : b⁻¹ * u * b⁻¹⁻¹ = t := inv_conj_of_conj hbt
  have hbb := hs.mul_self_mem_edgeCent hbP
  have hxA : (b * b)⁻¹ ∈ edgeCent (P : Subgroup Y) t u := Subgroup.inv_mem _ hbb
  have hxin : InnerModOdd (linkLayer R t) (b * b)⁻¹ :=
    innerModOdd_inv hin (hs.conjSub_Λt_of_mem hxA)
  obtain ⟨s, hsA, hs1, hs2⟩ := hSplit hr Y R S t J u R₀ T₀ P hs hall _ hxA hxin
  have hcP : b * s ∈ (P : Subgroup Y) := (P : Subgroup Y).mul_mem hbP hsA.1.1
  have hzA : b⁻¹ * s * b⁻¹⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
    hs.conj_mem_edgeCent ((P : Subgroup Y).inv_mem hbP) hsA
  have e : b * s * (b * s) = b * b * (b⁻¹ * s * b⁻¹⁻¹) * s := by group
  refine ⟨b * s, hcP, fun h => hbA ?_, ?_⟩
  · have e' : b = b * s * s⁻¹ := by group
    rw [e']
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hsA)
  refine hs.eq_one_of_actsTriv (hs.mul_self_mem_edgeCent hcP) ?_ ?_
  ·
    rw [e, actsTriv_iff]
    have h1 : ActsLike (linkLayer R t) (b⁻¹ * s * b⁻¹⁻¹) 1 := by
      have h := actsLike_conj (actsTriv_iff.mp hs2) b⁻¹
      rwa [hs.conjSub_Λu_swap hbu', show b⁻¹ * 1 * b⁻¹⁻¹ = 1 by group] at h
    have h2 := actsLike_mul (actsLike_refl _ (b * b)) h1 (by rw [conjSub_one])
      (hs.conjSub_Λt_of_mem hbb)
    have h3 := actsLike_mul h2 hs1 (hs.conjSub_Λt_of_mem hxA)
      (hs.conjSub_Λt_of_mem (Subgroup.mul_mem _ hbb hzA))
    rwa [show b * b * 1 * (b * b)⁻¹ = 1 by group] at h3
  ·
    rw [e, actsTriv_iff]
    have h1 : ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
        (b⁻¹ * s * b⁻¹⁻¹) (b * b)⁻¹ := by
      have h := actsLike_conj hs1 b⁻¹
      rwa [hs.conjSub_Λt_swap hbt', show b⁻¹ * (b * b)⁻¹ * b⁻¹⁻¹ = (b * b)⁻¹ by group] at h
    have h2 := actsLike_mul (actsLike_refl _ (b * b)) h1 (hs.conjSub_Λu_of_mem hxA)
      (hs.conjSub_Λu_of_mem hbb)
    have h3 := actsLike_mul h2 (actsTriv_iff.mp hs2) (by rw [conjSub_one])
      (hs.conjSub_Λu_of_mem (Subgroup.mul_mem _ hbb hzA))
    rwa [show b * b * (b * b)⁻¹ * 1 = 1 by group] at h3

theorem Z2SetR.sq_outer_of_not_invOutsideA (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hSplit : Z2BigSplit r n) (hr : 4 ≤ r) (hall : NoA1All R t J u)
    (hno : ¬ InvOutsideA (P : Subgroup Y) t u) {y : Y} (hyP : y ∈ (P : Subgroup Y))
    (hyA : y ∉ edgeCent (P : Subgroup Y) t u) :
    ¬ InnerModOdd (linkLayer R t) (y * y) ∧
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (y * y) := by
  have hyt := hs.swap_of_not_mem hyP hyA
  have h1 : ¬ InnerModOdd (linkLayer R t) (y * y) := fun h =>
    hno (hs.invOutsideA_of_inner_sq hSplit hr hall hyP hyA h)
  refine ⟨h1, fun h => h1 ?_⟩
  rw [hs.innerModOdd_conj_swap hyt, show y * (y * y) * y⁻¹ = y * y by group]
  exact h

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
