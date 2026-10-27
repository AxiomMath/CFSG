module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

namespace Sec5CDAbs

variable {L B : Subgroup G} {r : G} {i : Fin 6} {fr : NFrame Q (Fin 6) 1}
  {φc : ↥L →* omegaGroup hQ} (h : Sec5CDAbs L B r i fr φc)

include h

theorem exists_twist {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    ∃ g : ↥L, (φc g : OGroup Q) = fr.permOrth σ ∧ (g : G) * r * (g : G)⁻¹ ∈ zpowers r ⊔ B := by
  have hp : fr.permOrth σ ∈ omegaGroup hQ := NFrame.permOrth_mem_omegaGroup hQ fr hσ
  obtain ⟨g₀, hg₀⟩ := h.cover.surjective ⟨fr.permOrth σ, hp⟩
  have hg₀val : (φc g₀ : OGroup Q) = fr.permOrth σ := congrArg Subtype.val hg₀
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right h.r_sq
  have hl'mem : r * (g₀ : G)⁻¹ * r⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp h.r_norm ((g₀ : G)⁻¹)).mp (L.inv_mem g₀.2)
  let l' : ↥L := ⟨r * (g₀ : G)⁻¹ * r⁻¹, hl'mem⟩
  let u₀ : ↥L := g₀ * l'
  have hu₀ : (u₀ : G) = (g₀ : G) * r * (g₀ : G)⁻¹ * r⁻¹ := by
    simp only [u₀, l', Subgroup.coe_mul]
    group
  have hl' : (φc l' : OGroup Q) =
      fr.signChange {i} * (φc g₀⁻¹ : OGroup Q) * (fr.signChange {i})⁻¹ :=
    h.r_act g₀⁻¹ l' (by simp [l'])
  have hti : (fr.signChange {i} : OGroup Q) * fr.signChange {i} = 1 :=
    fr.signChange_mul_self {i}
  have hti_inv : (fr.signChange {i} : OGroup Q)⁻¹ = fr.signChange {i} :=
    inv_eq_of_mul_eq_one_right hti
  have hphi_u₀ : (φc u₀ : OGroup Q) = fr.signChange (symmDiff {σ i} {i}) := by
    calc (φc u₀ : OGroup Q)
        = (φc g₀ : OGroup Q) * (φc l' : OGroup Q) := by
            simp only [u₀, map_mul, Subgroup.coe_mul]
      _ = fr.permOrth σ * (fr.signChange {i} * (φc g₀⁻¹ : OGroup Q) *
            (fr.signChange {i})⁻¹) := by
            rw [hl', hg₀val]
      _ = fr.permOrth σ * fr.signChange {i} * (fr.permOrth σ)⁻¹ * fr.signChange {i} := by
            rw [map_inv, Subgroup.coe_inv, hg₀val, hti_inv]
            group
      _ = fr.signChange {σ i} * fr.signChange {i} := by
            have hconj : fr.permOrth σ * fr.signChange {i} * (fr.permOrth σ)⁻¹ =
                fr.signChange {σ i} := by
              rw [fr.permOrth_mul_signChange σ {i}, mul_assoc, mul_inv_cancel, mul_one]
              congr 1
            rw [hconj]
      _ = fr.signChange (symmDiff {σ i} {i}) := fr.signChange_mul {σ i} {i}
  let J : Finset (Fin 6) := symmDiff {σ i} {i}
  have hJ : Even J.card := by
    change Even (symmDiff {σ i} {i} : Finset (Fin 6)).card
    rw [Finset.even_card_symmDiff_iff, Finset.card_singleton, Finset.card_singleton]
  let b : ↥L := sec5c_liftL L B φc (fr.signChange J)
  have hbB : (b : G) ∈ B := h.liftL_mem (signChange_mem_ffB0 fr hJ)
  have hbmap : (φc b : OGroup Q) = fr.signChange J :=
    h.map_liftL (signChange_mem_ffB0 fr hJ)
  let o : ↥L := b⁻¹ * u₀
  have ho_ker : o ∈ φc.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change (φc o : OGroup Q) = 1
    have hcalc : (φc o : OGroup Q) = (φc b : OGroup Q)⁻¹ * (φc u₀ : OGroup Q) := by
      simp only [o, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcalc, hbmap, hphi_u₀]
    exact inv_mul_cancel _
  have ho_cent : o ∈ Subgroup.center ↥L := h.cover.ker_le_center ho_ker
  have ho_comm (x : ↥L) : o * x = x * o := (Subgroup.mem_center_iff.mp ho_cent x).symm
  have hu₀_bo : u₀ = b * o := by
    simp only [o]
    group
  have hu₀_boG : (u₀ : G) = (b : G) * (o : G) := congrArg Subtype.val hu₀_bo
  have hru₀ : r * (u₀ : G) * r⁻¹ = (u₀ : G)⁻¹ := by
    rw [hu₀, hrinv]
    calc r * ((g₀ : G) * r * (g₀ : G)⁻¹ * r) * r
        = r * (g₀ : G) * r * (g₀ : G)⁻¹ * (r * r) := by group
      _ = r * (g₀ : G) * r * (g₀ : G)⁻¹ := by rw [h.r_sq, mul_one]
      _ = ((g₀ : G) * r * (g₀ : G)⁻¹ * r)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hrinv]
            group
  have hro : r * (o : G) * r⁻¹ = (o : G)⁻¹ := by
    have hbo : Commute (b : G) (o : G) := (congrArg Subtype.val (ho_comm b)).symm
    have hrb : r * (b : G) * r⁻¹ = (b : G) := by
      rw [h.r_comm (b : G) hbB]
      group
    have key : (b : G) * (r * (o : G) * r⁻¹) = (b : G) * (o : G)⁻¹ := by
      have hL : (b : G) * (r * (o : G) * r⁻¹) = r * ((b : G) * (o : G)) * r⁻¹ := by
        calc (b : G) * (r * (o : G) * r⁻¹)
            = (r * (b : G) * r⁻¹) * (r * (o : G) * r⁻¹) := by rw [hrb]
          _ = r * ((b : G) * (o : G)) * r⁻¹ := by group
      rw [hL, ← hu₀_boG, hru₀, hu₀_boG, mul_inv_rev,
        show (b : G)⁻¹ = (b : G) from inv_eq_of_mul_eq_one_right (h.B_sq (b : G) hbB)]
      exact (hbo.inv_right).symm
    exact mul_left_cancel key
  have hoN : o ^ Nat.card φc.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard φc.ker ho_ker)
  obtain ⟨j, hj⟩ := h.cover.odd_card_ker
  have hN1 : 1 ≤ Nat.card φc.ker := by omega
  let o₁ : ↥L := o ^ j
  have ho₁_sq : o₁ ^ 2 = o ^ (Nat.card φc.ker - 1) := by
    show (o ^ j) ^ 2 = o ^ (Nat.card φc.ker - 1)
    rw [← pow_mul]
    congr 1
    omega
  have ho₁_ker : o₁ ∈ φc.ker := φc.ker.pow_mem ho_ker j
  have ho₁_map : φc o₁ = 1 := MonoidHom.mem_ker.mp ho₁_ker
  have ho₁_cent : o₁ ∈ Subgroup.center ↥L := h.cover.ker_le_center ho₁_ker
  have ho₁_comm (x : ↥L) : o₁ * x = x * o₁ := (Subgroup.mem_center_iff.mp ho₁_cent x).symm
  have hro₁G : r * (o₁ : G) * r⁻¹ = (o₁ : G)⁻¹ := by
    show r * ((o ^ j : ↥L) : G) * r⁻¹ = ((o ^ j : ↥L) : G)⁻¹
    rw [Subgroup.coe_pow]
    calc r * (o : G) ^ j * r⁻¹ = (r * (o : G) * r⁻¹) ^ j := (conj_pow).symm
      _ = ((o : G)⁻¹) ^ j := by rw [hro]
      _ = ((o : G) ^ j)⁻¹ := inv_pow (o : G) j
  have ho₁r : (o₁ : G) * r = r * (o₁ : G)⁻¹ := by
    have h1 : (o₁ : G) = r * (o₁ : G)⁻¹ * r := by
      calc (o₁ : G) = r⁻¹ * (r * (o₁ : G) * r⁻¹) * r := by group
        _ = r⁻¹ * (o₁ : G)⁻¹ * r := by rw [hro₁G]
        _ = r * (o₁ : G)⁻¹ * r := by rw [hrinv]
    calc (o₁ : G) * r = (r * (o₁ : G)⁻¹ * r) * r := congrArg (· * r) h1
      _ = r * (o₁ : G)⁻¹ * (r * r) := by group
      _ = r * (o₁ : G)⁻¹ := by rw [h.r_sq, mul_one]
  have hro₁2 : r * (o₁ : G) ^ 2 * r⁻¹ = ((o₁ : G) ^ 2)⁻¹ := by
    rw [← conj_pow, hro₁G, ← inv_pow]
  have hro₁2_inv : r * ((o₁ : G) ^ 2)⁻¹ * r⁻¹ = (o₁ : G) ^ 2 := by
    calc r * ((o₁ : G) ^ 2)⁻¹ * r⁻¹ = (r * (o₁ : G) ^ 2 * r⁻¹)⁻¹ := by group
      _ = (((o₁ : G) ^ 2)⁻¹)⁻¹ := by rw [hro₁2]
      _ = (o₁ : G) ^ 2 := inv_inv _
  have hcen : (o₁ : G) * (g₀ : G) = (g₀ : G) * (o₁ : G) :=
    congrArg Subtype.val (ho₁_comm g₀)
  have hcen_inv : ((o₁ : G) ^ 2)⁻¹ * (g₀ : G)⁻¹ = (g₀ : G)⁻¹ * ((o₁ : G) ^ 2)⁻¹ := by
    have h2 : (o₁ : G) ^ 2 * (g₀ : G) = (g₀ : G) * (o₁ : G) ^ 2 := by
      rw [pow_two]
      calc (o₁ : G) * (o₁ : G) * (g₀ : G)
          = (o₁ : G) * ((o₁ : G) * (g₀ : G)) := by rw [mul_assoc]
        _ = (o₁ : G) * ((g₀ : G) * (o₁ : G)) := by rw [hcen]
        _ = ((o₁ : G) * (g₀ : G)) * (o₁ : G) := by rw [← mul_assoc]
        _ = ((g₀ : G) * (o₁ : G)) * (o₁ : G) := by rw [hcen]
        _ = (g₀ : G) * ((o₁ : G) * (o₁ : G)) := by rw [mul_assoc]
    have h3 := congrArg Inv.inv h2
    rw [mul_inv_rev, mul_inv_rev] at h3
    exact h3.symm
  have hgo : (g₀ : G) * r * (g₀ : G)⁻¹ = (u₀ : G) * r := by
    rw [hu₀]
    group
  have ho₁_sq_comm : o₁ ^ 2 * u₀ = u₀ * o₁ ^ 2 := by
    rw [pow_two]
    calc (o₁ * o₁) * u₀ = o₁ * (o₁ * u₀) := by group
      _ = o₁ * (u₀ * o₁) := by rw [ho₁_comm u₀]
      _ = (o₁ * u₀) * o₁ := by group
      _ = (u₀ * o₁) * o₁ := by rw [ho₁_comm u₀]
      _ = u₀ * (o₁ * o₁) := by group
  have ho₁_sq_u₀ : o₁ ^ 2 * u₀ = b := by
    have h1 : o₁ ^ 2 = o⁻¹ := by
      rw [ho₁_sq]
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hN1]
      exact hoN
    have hcob : Commute o b := ho_comm b
    rw [h1, hu₀_bo]
    calc o⁻¹ * (b * o) = (o⁻¹ * b) * o := by group
      _ = (b * o⁻¹) * o := by rw [hcob.inv_left]
      _ = b := by group
  have hkey : ((g₀ * o₁ : ↥L) : G) * r * (((g₀ * o₁ : ↥L) : G))⁻¹ * r⁻¹ =
      ((o₁ ^ 2 * u₀ : ↥L) : G) := by
    calc ((g₀ * o₁ : ↥L) : G) * r * (((g₀ * o₁ : ↥L) : G))⁻¹ * r⁻¹
        = (g₀ : G) * (o₁ : G) * r * (o₁ : G)⁻¹ * (g₀ : G)⁻¹ * r⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (g₀ : G) * ((o₁ : G) * r) * (o₁ : G)⁻¹ * (g₀ : G)⁻¹ * r⁻¹ := by group
      _ = (g₀ : G) * (r * (o₁ : G)⁻¹) * (o₁ : G)⁻¹ * (g₀ : G)⁻¹ * r⁻¹ := by rw [ho₁r]
      _ = (g₀ : G) * r * ((o₁ : G) ^ 2)⁻¹ * (g₀ : G)⁻¹ * r⁻¹ := by group
      _ = (g₀ : G) * r * (((o₁ : G) ^ 2)⁻¹ * (g₀ : G)⁻¹) * r⁻¹ := by group
      _ = (g₀ : G) * r * ((g₀ : G)⁻¹ * ((o₁ : G) ^ 2)⁻¹) * r⁻¹ := by rw [hcen_inv]
      _ = (g₀ : G) * r * (g₀ : G)⁻¹ * ((o₁ : G) ^ 2)⁻¹ * r⁻¹ := by group
      _ = ((g₀ : G) * r * (g₀ : G)⁻¹) * ((o₁ : G) ^ 2)⁻¹ * r⁻¹ := by group
      _ = (u₀ : G) * r * ((o₁ : G) ^ 2)⁻¹ * r⁻¹ := by rw [hgo]
      _ = (u₀ : G) * (r * ((o₁ : G) ^ 2)⁻¹ * r⁻¹) := by group
      _ = (u₀ : G) * (o₁ : G) ^ 2 := by rw [hro₁2_inv]
      _ = ((o₁ ^ 2 * u₀ : ↥L) : G) := by
            simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using
              (congrArg Subtype.val ho₁_sq_comm).symm
  have hgr : ((g₀ * o₁ : ↥L) : G) * r * (((g₀ * o₁ : ↥L) : G))⁻¹ = (b : G) * r := by
    have hk := hkey
    rw [ho₁_sq_u₀] at hk
    calc ((g₀ * o₁ : ↥L) : G) * r * (((g₀ * o₁ : ↥L) : G))⁻¹
        = (((g₀ * o₁ : ↥L) : G) * r * (((g₀ * o₁ : ↥L) : G))⁻¹ * r⁻¹) * r := by group
      _ = (b : G) * r := by rw [hk]
  refine ⟨g₀ * o₁, ?_, ?_⟩
  · rw [map_mul, ho₁_map, mul_one]
    exact hg₀val
  · rw [hgr]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hbB)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))

end Sec5CDAbs

end CFSG.OddStandard.SmallF3.Omega
