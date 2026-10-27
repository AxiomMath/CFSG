module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCentralProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem commute_conj_of_central {A : Type*} [Group A] {z x c g : A} (hz : z ∈ center A)
    (hzz : z * z = 1) (hg : g * x = x * g) (hc : c * x * c⁻¹ = z * x) :
    (c * g * c⁻¹) * x = x * (c * g * c⁻¹) := by
  have hzc : ∀ a : A, a * z = z * a := fun a => Subgroup.mem_center_iff.mp hz a
  have hcx : c * x = z * x * c := mul_inv_eq_iff_eq_mul.mp hc
  have h1 : c⁻¹ * x = z * x * c⁻¹ := by
    have h2 : x * c⁻¹ = c⁻¹ * z * x := by
      calc x * c⁻¹ = c⁻¹ * (c * x) * c⁻¹ := by group
        _ = c⁻¹ * (z * x * c) * c⁻¹ := by rw [hcx]
        _ = c⁻¹ * z * x := by group
    calc c⁻¹ * x = (z * z) * (c⁻¹ * x) := by rw [hzz, one_mul]
      _ = z * (z * c⁻¹) * x := by group
      _ = z * (c⁻¹ * z) * x := by rw [← hzc c⁻¹]
      _ = z * (c⁻¹ * z * x) := by group
      _ = z * (x * c⁻¹) := by rw [h2]
      _ = z * x * c⁻¹ := by group
  calc (c * g * c⁻¹) * x = c * g * (c⁻¹ * x) := by group
    _ = c * g * (z * x * c⁻¹) := by rw [h1]
    _ = z * (c * (g * x) * c⁻¹) := by
        have : c * g * (z * x * c⁻¹) = c * g * z * x * c⁻¹ := by group
        rw [this, show c * g * z = z * (c * g) from by rw [mul_assoc, hzc g, ← mul_assoc, hzc c,
          mul_assoc]]
        group
    _ = z * (c * (x * g) * c⁻¹) := by rw [hg]
    _ = (z * (c * x)) * g * c⁻¹ := by group
    _ = (z * (z * x * c)) * g * c⁻¹ := by rw [hcx]
    _ = x * (c * g * c⁻¹) := by
        calc (z * (z * x * c)) * g * c⁻¹ = (z * z) * x * c * g * c⁻¹ := by group
          _ = x * (c * g * c⁻¹) := by rw [hzz]; group

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def projAut (hQ : Q.Nondegenerate) (x : OGroup Q) :
    MulAut ↥(omegaProj hQ) :=
  MulAut.conjNormal (toProj Q x)

theorem coe_projAut (hQ : Q.Nondegenerate) (x : OGroup Q) (p : ↥(omegaProj hQ)) :
    ((projAut hQ x p : ↥(omegaProj hQ)) : ProjOrth Q) =
      toProj Q x * (p : ProjOrth Q) * (toProj Q x)⁻¹ :=
  MulAut.conjNormal_apply (toProj Q x) p

theorem mem_fixSub_projAut_iff (hQ : Q.Nondegenerate) (x : OGroup Q) (p : ↥(omegaProj hQ)) :
    p ∈ fixSub (projAut hQ x) ↔ toProj Q x * (p : ProjOrth Q) = (p : ProjOrth Q) * toProj Q x := by
  rw [mem_fixSub_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [coe_projAut] at h'
    exact mul_inv_eq_iff_eq_mul.mp h'
  · intro h
    apply Subtype.ext
    rw [coe_projAut]
    exact mul_inv_eq_iff_eq_mul.mpr h

@[expose] noncomputable def cOmega (hQ : Q.Nondegenerate) (x : OGroup Q) :
    Subgroup ↥(omegaGroup hQ) :=
  (Subgroup.centralizer ({x} : Set (OGroup Q))).comap (omegaGroup hQ).subtype

theorem mem_cOmega_iff (hQ : Q.Nondegenerate) (x : OGroup Q) (g : ↥(omegaGroup hQ)) :
    g ∈ cOmega hQ x ↔ (g : OGroup Q) * x = x * (g : OGroup Q) := by
  change (g : OGroup Q) ∈ Subgroup.centralizer ({x} : Set (OGroup Q)) ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem omegaToProj_mem_fix (hQ : Q.Nondegenerate) {x : OGroup Q} {g : ↥(omegaGroup hQ)}
    (hg : g ∈ cOmega hQ x) : omegaToProj hQ g ∈ fixSub (projAut hQ x) := by
  rw [mem_fixSub_projAut_iff]
  have h := (mem_cOmega_iff hQ x g).mp hg
  change toProj Q x * toProj Q (g : OGroup Q) = toProj Q (g : OGroup Q) * toProj Q x
  rw [← map_mul, ← map_mul, h]

theorem conj_mem_cOmega (hQ : Q.Nondegenerate) {x : OGroup Q} (hx : x * x = 1)
    {c g : ↥(omegaGroup hQ)} (hc : omegaToProj hQ c ∈ fixSub (projAut hQ x))
    (hg : g ∈ cOmega hQ x) : c * g * c⁻¹ ∈ cOmega hQ x := by
  rw [mem_fixSub_projAut_iff] at hc
  have hc' : toProj Q (c : OGroup Q) ∈ Subgroup.centralizer ({toProj Q x} : Set (ProjOrth Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc.symm
  have hcases := (toProj_mem_centralizer_iff hx (c : OGroup Q)).mp hc'
  rw [mem_cOmega_iff]
  have hgx := (mem_cOmega_iff hQ x g).mp hg
  change ((c : OGroup Q) * (g : OGroup Q) * (c : OGroup Q)⁻¹) * x =
    x * ((c : OGroup Q) * (g : OGroup Q) * (c : OGroup Q)⁻¹)
  rcases hcases with h | h
  · exact commute_conj_of_central (z := 1) (Subgroup.one_mem _) (one_mul 1) hgx
      (by rw [h, one_mul])
  · exact commute_conj_of_central (z := piOrth Q) piOrth_mem_center piOrth_mul_self hgx h

theorem isComponentIn_fix (hQ : Q.Nondegenerate) {x : OGroup Q} (hx : x * x = 1)
    {K : Subgroup ↥(omegaGroup hQ)} (hK : K ≤ cOmega hQ x)
    (hn : ∀ g ∈ cOmega hQ x, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hq : CFSG.IsQuasisimple ↥(K.map (omegaToProj hQ))) :
    IsComponentIn (K.map (omegaToProj hQ)) (fixSub (projAut hQ x)) := by
  set N : Subgroup ↥(omegaProj hQ) := (cOmega hQ x).map (omegaToProj hQ) with hNdef
  have hMN : K.map (omegaToProj hQ) ≤ N := Subgroup.map_mono hK
  have hNF : N ≤ fixSub (projAut hQ x) := by
    rintro _ ⟨g, hg, rfl⟩
    exact omegaToProj_mem_fix hQ hg
  have hMn : ∀ n ∈ N, ∀ m ∈ K.map (omegaToProj hQ), n * m * n⁻¹ ∈ K.map (omegaToProj hQ) := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨k, hk, rfl⟩
    exact ⟨g * k * g⁻¹, hn g hg k hk, by rw [map_mul, map_mul, map_inv]⟩
  have hNnorm : ∀ f ∈ fixSub (projAut hQ x), ∀ n ∈ N, f * n * f⁻¹ ∈ N := by
    rintro f hf _ ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ := omegaToProj_surjective hQ f
    exact ⟨c * g * c⁻¹, conj_mem_cOmega hQ hx hf hg, by rw [map_mul, map_mul, map_inv]⟩
  have hNsub : (N.subgroupOf (fixSub (projAut hQ x))).IsSubnormal := by
    have hnorm : (N.subgroupOf (fixSub (projAut hQ x))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hNF]
      intro h k hh hk
      exact hNnorm k hk h hh
    exact hnorm.isSubnormal
  exact isComponentIn_of_subnormal (hMN.trans hNF) hq
    (isSubnormal_subgroupOf_of_normal_le hMN hNF hMn hNsub)

end CFSG.OddStandard.SmallF3.Omega
