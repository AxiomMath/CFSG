module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7e

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_V_le_M3 (c : Ctx7 G L) (hb : B5Std c) : cen c.s.fr.B ≤ M3 c.s :=
  (y54_V_le_F hb.hH).trans (le_sup_right : c.s.fr.F ≤ M3 c.s)

theorem y7b_cent_W_eq_V (c : Ctx7 G L) (hb : B5Std c) :
    M3 c.s ⊓ centralizer (y7bW c.s : Set G) = cen c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxM3, hxcent⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ c.s.H := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      exact (Subgroup.mem_centralizer_iff.mp hxcent c.s.t (y7b_t_mem_W c hb)).symm
    have hxF : x ∈ c.s.fr.F := by
      have : x ∈ c.s.H ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨hxH, hxM3⟩
      rwa [y54_H_inf_M3 c.toCtx5 hb.hH] at this
    exact Subgroup.mem_inf.mpr ⟨y54_F_le_B hb.hH hxF,
      Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx) hxcent⟩
  · intro v hv
    have hvM3 : v ∈ M3 c.s := y7b_V_le_M3 c hb hv
    have hvcentB : v ∈ centralizer (c.s.fr.B : Set G) := hv.2
    have hvF : v ∈ c.s.fr.F := y54_V_le_F hb.hH hv
    have hvcentW : v ∈ centralizer (y7bW c.s : Set G) := by
      have hW : y7bW c.s ≤ centralizer (Subgroup.zpowers v : Set G) := by
        rw [y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
        refine sup_le ?_ (sup_le ?_ ?_)
        · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact hvcentB
        · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
          exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr
            (y7b_M3_elem c hb).1) hvM3
        · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le,
            Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
            Subgroup.mem_centralizer_singleton_iff]
          exact y54_t_comm_F c.s v hvF
      have hW' : Subgroup.zpowers v ≤ centralizer (y7bW c.s : Set G) :=
        Subgroup.le_centralizer_iff.mp hW
      exact Subgroup.zpowers_le.mp hW'
    exact Subgroup.mem_inf.mpr ⟨hvM3, hvcentW⟩

theorem y7b_X_le_NV (c : Ctx7 G L) (hb : B5Std c) :
    y7bX c.s ≤ normalizer (cen c.s.fr.B : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have hv' : v ∈ M3 c.s ⊓ centralizer (y7bW c.s : Set G) := by
    rw [y7b_cent_W_eq_V c hb]
    exact hv
  obtain ⟨hvM3, hvcentW⟩ := Subgroup.mem_inf.mp hv'
  obtain ⟨hxW, hxM3⟩ := Subgroup.mem_inf.mp hx
  rw [← y7b_cent_W_eq_V c hb]
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hxM3 v).mp hvM3, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hxin : x⁻¹ * w * x ∈ y7bW c.s :=
    (Subgroup.mem_normalizer_iff''.mp hxW w).mp hw
  have hcomm := Subgroup.mem_centralizer_iff.mp hvcentW (x⁻¹ * w * x) hxin
  calc w * (x * v * x⁻¹) = x * ((x⁻¹ * w * x) * v) * x⁻¹ := by group
    _ = x * (v * (x⁻¹ * w * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * v * x⁻¹) * w := by group

theorem y7b_BM_sq_mem_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, u ^ 2 ∈ M3 c.s := by
  intro u hu
  obtain ⟨b, hbB, m, hmM3, rfl⟩ := (y7b_mem_BM c hb).mp hu
  have hb2 : b ^ 2 ∈ M3 c.s :=
    y7b_V_le_M3 c hb (y7b_B_sq_mem_V hb.hH b hbB)
  have hbmb : b⁻¹ * m * b ∈ M3 c.s :=
    (Subgroup.mem_normalizer_iff''.mp (y7b_B_le_NM3 c hb hbB) m).mp hmM3
  rw [show (b * m) ^ 2 = b ^ 2 * (b⁻¹ * m * b) * m by
    rw [pow_two]
    group]
  exact (M3 c.s).mul_mem ((M3 c.s).mul_mem hb2 hbmb) hmM3

theorem y7b_M3_normal_BM (c : Ctx7 G L) (hb : B5Std c) :
    ((M3 c.s).subgroupOf (y7bBM c.s)).Normal := by
  have hle : y7bBM c.s ≤ normalizer (M3 c.s : Set G) :=
    sup_le (y7b_B_le_NM3 c hb) Subgroup.le_normalizer
  rw [Subgroup.normal_subgroupOf_iff le_sup_right]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.mp (hle hk) h).mp hh

theorem y7b_X7_le_X (c : Ctx7 G L) : X7 c.s ≤ y7bX c.s := by
  simp only [X7, y7bX, y7bW]
  exact inf_le_left

theorem y7b_mem_X7 (c : Ctx7 G L) (hb : B5Std c) {x : G} :
    x ∈ X7 c.s ↔ x ∈ y7bX c.s ∧ ∀ u ∈ y7bBM c.s, ⁅x, u⁆ ∈ M3 c.s := by
  unfold X7
  constructor
  · intro hx
    obtain ⟨hxX, hxCS⟩ := Subgroup.mem_inf.mp hx
    refine ⟨hxX, fun u hu => ?_⟩
    have h := hxCS.2.2 u hu
    rw [← commutatorElement_inv (g₁ := u) (g₂ := x)]
    exact (M3 c.s).inv_mem h
  · rintro ⟨hxX, hcomm⟩
    refine Subgroup.mem_inf.mpr
      ⟨hxX, ⟨?_, (Subgroup.mem_inf.mp hxX).2, fun k hk => ?_⟩⟩
    · refine Subgroup.mem_normalizer_fintype fun u hu => ?_
      exact y7b_X_norm_BM c hb x hxX u hu
    · have h := hcomm k hk
      rw [← commutatorElement_inv (g₁ := x) (g₂ := k)]
      exact (M3 c.s).inv_mem h

theorem y7b_X7_normal (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bX c.s, ∀ y ∈ X7 c.s, x * y * x⁻¹ ∈ X7 c.s := by
  intro x hxX y hyX
  rw [y7b_mem_X7 c hb] at hyX ⊢
  obtain ⟨hyX', hycomm⟩ := hyX
  refine ⟨?_, ?_⟩
  · exact (y7bX c.s).mul_mem ((y7bX c.s).mul_mem hxX hyX') ((y7bX c.s).inv_mem hxX)
  · intro u hu
    have hxinv : x⁻¹ ∈ y7bX c.s := (y7bX c.s).inv_mem hxX
    have hxin : x⁻¹ * u * x ∈ y7bBM c.s := by
      simpa using y7b_X_norm_BM c hb x⁻¹ hxinv u hu
    have hxNM3 : x ∈ normalizer (M3 c.s : Set G) := (Subgroup.mem_inf.mp hxX).2
    have hconj : x * ⁅y, x⁻¹ * u * x⁆ * x⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp hxNM3 ⁅y, x⁻¹ * u * x⁆).mp (hycomm _ hxin)
    convert hconj using 1
    rw [commutatorElement_def, commutatorElement_def]
    group

end CFSG.OddStandard.HigherRank.YamadaG23
