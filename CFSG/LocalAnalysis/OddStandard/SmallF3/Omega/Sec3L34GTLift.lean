module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTHullB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem l34g_lift {A C : Type} [Group A] [Group C] [Finite A] (φ : A →* C)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A)
    (h2 : ∀ P : Subgroup A, IsPGroup 2 P → P ≤ φ.ker → Nat.card P ≤ 2) {b : C}
    (hb : IsI4PlusIn (⊤ : Subgroup C) b) :
    ∃ b₁ : A, φ b₁ = b ∧ IsI4PlusIn (⊤ : Subgroup A) b₁ := by
  classical
  obtain ⟨hb2, B, hbB, hBle, hBsub, hBSL⟩ := hb
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
  refine ⟨d ^ orderOf (d ^ 2), hφb₁, hb₁ord, l34g_oddHull φ B, ?_⟩
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

end CFSG.OddStandard.SmallF3.Omega
