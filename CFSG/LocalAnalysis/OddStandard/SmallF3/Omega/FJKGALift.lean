module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutComp
import CFSG.GH74.Uniqueness.Bender.Frame311
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTHullB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fj_lift_pocket {A C : Type} [Group A] [Group C] [Finite A] (φ : A →* C)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A)
    (h2 : ∀ P : Subgroup A, IsPGroup 2 P → P ≤ φ.ker → Nat.card P ≤ 2) {b : C}
    {B : Subgroup C} (hb2 : orderOf b = 2) (hB : Sl23PocketIn ⊤ b B) :
    ∃ b₁ : A, φ b₁ = b ∧ orderOf b₁ = 2 ∧ Sl23PocketIn ⊤ b₁ (l34g_oddHull φ B) := by
  classical
  obtain ⟨hbB, hBle, hBsub, hBSL⟩ := hB
  have hbsq : b * b = 1 := sec63P_mul_self hb2
  have hHle : l34g_oddHull φ B ≤ B.comap φ := l34g_oddHull_le φ B
  have hmap : (l34g_oddHull φ B).map φ = B := l34g_map_oddHull φ hφ hBSL
  have hodd : Odd (Nat.card ↥(l34g_oddHull φ B ⊓ φ.ker)) :=
    l34g_odd_card_oddHull_inf_ker φ hφ hker h2 hBSL
  have hSL : IsSL23Mod ↥(l34g_oddHull φ B) := l34g_isSL23Mod_oddHull φ hφ hker h2 hBSL
  obtain ⟨d, hdH, hdb⟩ : ∃ d ∈ l34g_oddHull φ B, φ d = b :=
    Subgroup.mem_map.mp (by rw [hmap]; exact hbB)
  have hd2 : d ^ 2 ∈ l34g_oddHull φ B ⊓ φ.ker := by
    refine ⟨(l34g_oddHull φ B).pow_mem hdH 2, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_pow, hdb, pow_two, hbsq]
  have hmodd : Odd (orderOf (d ^ 2)) :=
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hd2)
  have hb₁sq : d ^ orderOf (d ^ 2) * d ^ orderOf (d ^ 2) = 1 := by
    calc d ^ orderOf (d ^ 2) * d ^ orderOf (d ^ 2) = (d ^ 2) ^ orderOf (d ^ 2) := by
          rw [← pow_add, ← two_mul, pow_mul]
      _ = 1 := pow_orderOf_eq_one _
  have hφb₁ : φ (d ^ orderOf (d ^ 2)) = b := by
    obtain ⟨k, hk⟩ := hmodd
    rw [map_pow, hdb, hk, pow_succ, pow_mul, pow_two, hbsq, one_pow, one_mul]
  have hb₁ne : d ^ orderOf (d ^ 2) ≠ 1 := by
    intro h
    have h1 := congrArg φ h
    rw [hφb₁, map_one] at h1
    rw [h1, orderOf_one] at hb2
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb₁ord : orderOf (d ^ orderOf (d ^ 2)) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hb₁sq) hb₁ne
  refine ⟨d ^ orderOf (d ^ 2), hφb₁, hb₁ord, ?_⟩
  set b₁ : A := d ^ orderOf (d ^ 2) with hb₁def
  have hcent : l34g_oddHull φ B ≤ Subgroup.centralizer ({b₁} : Set A) :=
    l34g_oddHull_le_centralizer φ hker (hBle.trans inf_le_right) hb₁sq hφb₁
  refine ⟨(l34g_oddHull φ B).pow_mem hdH _, le_inf le_top hcent, ?_, hSL⟩
  set M : Subgroup A := ⊤ ⊓ Subgroup.centralizer ({b₁} : Set A) with hM
  set M' : Subgroup C := ⊤ ⊓ Subgroup.centralizer ({b} : Set C) with hM'
  have hθ : ∀ a : ↥M, (φ.comp M.subtype) a ∈ M' := by
    intro a
    refine ⟨trivial, ?_⟩
    have h1 : (a : A) * b₁ = b₁ * a := Subgroup.mem_centralizer_singleton_iff.mp a.2.2
    have h2' := congrArg φ h1
    rw [map_mul, map_mul, hφb₁] at h2'
    exact Subgroup.mem_centralizer_singleton_iff.mpr h2'
  let θ : ↥M →* ↥M' := (φ.comp M.subtype).codRestrict M' hθ
  have hcomap : ((B.subgroupOf M').comap θ).IsSubnormal := hBsub.comap θ
  have heq : (B.subgroupOf M').comap θ = (B.comap φ).subgroupOf M := by
    ext a
    simp [θ, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  rw [heq] at hcomap
  have hHM : (l34g_oddHull φ B).subgroupOf M ≤ (B.comap φ).subgroupOf M :=
    fun x hx => hHle hx
  have hnorm : (((l34g_oddHull φ B).subgroupOf M).subgroupOf
      ((B.comap φ).subgroupOf M)).Normal := by
    constructor
    intro n hn g
    have hn' : (((n : ↥((B.comap φ).subgroupOf M)) : ↥M) : A) ∈ l34g_oddHull φ B := hn
    have hg' : φ (((g : ↥((B.comap φ).subgroupOf M)) : ↥M) : A) ∈ B := g.2
    exact l34g_oddHull_conj φ B hg' hn'
  exact Subgroup.IsSubnormal.trans hHM hnorm.isSubnormal hcomap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_card_le_two_of_le_ker (hQ : Q.Nondegenerate) {P : Subgroup (omegaGroup hQ)}
    (hP : P ≤ (omegaToProj hQ).ker) : Nat.card P ≤ 2 := by
  have h1 : (P : Set (omegaGroup hQ)).ncard ≤ ({1, piOrth Q} : Set (OGroup Q)).ncard :=
    Set.ncard_le_ncard_of_injOn (fun p : omegaGroup hQ => (p : OGroup Q))
      (fun p hp => (omegaToProj_eq_one_iff hQ p).mp (hP hp)) (fun a _ b _ h => Subtype.ext h)
      (Set.toFinite _)
  have h2 : ({1, piOrth Q} : Set (OGroup Q)).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : OGroup Q) ({piOrth Q} : Set (OGroup Q))
    rwa [Set.ncard_singleton] at this
  calc Nat.card P = (P : Set (omegaGroup hQ)).ncard := Nat.card_coe_set_eq _
    _ ≤ 2 := h1.trans h2

theorem fj_lift_pocket_omega (hQ : Q.Nondegenerate) {y : omegaProj hQ}
    {B : Subgroup (omegaProj hQ)} (hy : orderOf y = 2) (hB : Sl23PocketIn ⊤ y B) :
    ∃ z : omegaGroup hQ, omegaToProj hQ z = y ∧ orderOf z = 2 ∧
      Sl23PocketIn ⊤ z (l34g_oddHull (omegaToProj hQ) B) := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  exact fj_lift_pocket (omegaToProj hQ) (omegaToProj_surjective hQ)
    (fun m hm => Subgroup.mem_center_iff.mpr fun g =>
      omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g)
    (fun _ _ hP => fj_card_le_two_of_le_ker hQ hP) hy hB

theorem fj_mem_cOmega_of_odd (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {ω : omegaGroup hQ} (hodd : Odd (orderOf ω))
    (hfix : omegaToProj hQ ω ∈ fixSub (projAut hQ s)) : ω ∈ cOmega hQ s := by
  rw [mem_cOmega_iff]
  have hc : toProj Q (ω : OGroup Q) ∈ Subgroup.centralizer ({toProj Q s} : Set (ProjOrth Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((mem_fixSub_projAut_iff hQ s _).mp hfix).symm
  have hcases := (toProj_mem_centralizer_iff hs (ω : OGroup Q)).mp hc
  have hsq : ((ω : OGroup Q) * ω) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hcases with h | h
    · have h' : (ω : OGroup Q) * s = s * ω := mul_inv_eq_iff_eq_mul.mp h
      calc (ω : OGroup Q) * ω * s = ω * (ω * s) := mul_assoc _ _ _
        _ = ω * (s * ω) := by rw [h']
        _ = (ω * s) * ω := (mul_assoc _ _ _).symm
        _ = (s * ω) * ω := by rw [h']
        _ = s * (ω * ω) := mul_assoc _ _ _
    · have h' : (ω : OGroup Q) * s = piOrth Q * s * ω := mul_inv_eq_iff_eq_mul.mp h
      calc (ω : OGroup Q) * ω * s = ω * (ω * s) := mul_assoc _ _ _
        _ = ω * (piOrth Q * s * ω) := by rw [h']
        _ = (ω * piOrth Q) * s * ω := by group
        _ = (piOrth Q * ω) * s * ω := by rw [mul_piOrth_comm]
        _ = piOrth Q * (ω * s) * ω := by group
        _ = piOrth Q * (piOrth Q * s * ω) * ω := by rw [h']
        _ = (piOrth Q * piOrth Q) * s * (ω * ω) := by group
        _ = s * (ω * ω) := by rw [piOrth_mul_self, one_mul]
  have hodd' : Odd (orderOf (ω : OGroup Q)) := by
    rw [Subgroup.orderOf_coe]
    exact hodd
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (CFSG.GH74.Uniqueness.Bender.mem_of_mul_self_mem_of_odd
      (F := Subgroup.centralizer ({s} : Set (OGroup Q))) hodd' hsq)

theorem fj_oddHull_le_cOmega (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {B : Subgroup (omegaProj hQ)} (hfix : ∀ b ∈ B, projAut hQ s b = b) :
    l34g_oddHull (omegaToProj hQ) B ≤ cOmega hQ s := by
  rw [l34g_oddHull, Subgroup.closure_le]
  rintro g ⟨hgB, hodd⟩
  exact fj_mem_cOmega_of_odd hQ hs hodd (mem_fixSub_iff.mpr (hfix _ hgB))

end CFSG.OddStandard.SmallF3.Omega
