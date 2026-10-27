module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Dih
public import CFSG.GH74.GLS.Stage2.Final.ModelIVKFam
public import CFSG.GH74.GLS.Stage2.Final.ModelLUSyl
public import CFSG.GH74.GLS.Stage2.Final.ModelRefl
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Bg.TwoGroups.Statements
public import CFSG.GH74.GLS.SP.Consistency
public import CFSG.GH74.GLS.SP.Generic
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMain
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

open Subgroup CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5

namespace CFSG.GH74.GLS.IVK.Proofs2

local notation "dg4" => CFSG.GH74.L5U5.diagGL

section GroupRel

variable {G : Type} [Group G]

theorem dih412_of_relations [Finite G] {A ν ρ₁ ρ₂ : G} {n : ℕ} (hn : 3 ≤ n)
    (h1 : orderOf ρ₁ = 2 ^ (n - 1)) (h2 : orderOf ρ₂ = 2 ^ (n - 1))
    (hAA : A * A = 1) (hνν : ν * ν = 1) (hAν : A * ν = ν * A) (hAρ₁ : A * ρ₁ = ρ₁ * A)
    (hνρ₁ : ν * ρ₁ * ν⁻¹ = ρ₁⁻¹) (hAρ₂ : A * ρ₂ * A⁻¹ = ρ₂⁻¹) (hνρ₂ : ν * ρ₂ * ν⁻¹ = ρ₂⁻¹)
    (hρ : ρ₁ * ρ₂ = ρ₂ * ρ₁) (hne : ρ₁ ^ 2 ^ (n - 2) ≠ ρ₂ ^ 2 ^ (n - 2)) :
    Dih412 G n (ρ₁ ^ 2 ^ (n - 2)) := by
  have hAρ₁' : A * ρ₁ * A⁻¹ = ρ₁ := by rw [hAρ₁]; group
  have hAρ₂inv : A * ρ₂⁻¹ * A⁻¹ = ρ₂ := by
    calc A * ρ₂⁻¹ * A⁻¹ = (A * ρ₂ * A⁻¹)⁻¹ := by group
      _ = ρ₂ := by rw [hAρ₂]; group
  refine dih412_of_pairs (σ₁ := A * ν) (σ₂ := A) hn h1 h2 ?_ hAA ?_ hAρ₂ hρ hAρ₁.symm ?_ ?_ hne
  · calc A * ν * (A * ν) = A * (ν * A) * ν := by group
      _ = A * (A * ν) * ν := by rw [← hAν]
      _ = (A * A) * (ν * ν) := by group
      _ = 1 := by rw [hAA, hνν]; group
  · calc A * ν * ρ₁ * (A * ν)⁻¹ = A * (ν * ρ₁ * ν⁻¹) * A⁻¹ := by group
      _ = A * ρ₁⁻¹ * A⁻¹ := by rw [hνρ₁]
      _ = (A * ρ₁ * A⁻¹)⁻¹ := by group
      _ = ρ₁⁻¹ := by rw [hAρ₁']
  · calc A * ν * ρ₂ = A * (ν * ρ₂ * ν⁻¹) * ν := by group
      _ = A * ρ₂⁻¹ * ν := by rw [hνρ₂]
      _ = (A * ρ₂⁻¹ * A⁻¹) * A * ν := by group
      _ = ρ₂ * (A * ν) := by rw [hAρ₂inv]; group
  · calc A * ν * A = A * (ν * A) := by group
      _ = A * (A * ν) := by rw [hAν]

end GroupRel

section Model

variable {F : Type} [Field F]

theorem mkP_xK (M : ModelData F) : mkP M M.xK = 1 :=
  (QuotientGroup.eq_one_iff _).2 (xK_mem_Zs M)

theorem mkP_xK_mul (M : ModelData F) (g : ↥M.K4) : mkP M (M.xK * g) = mkP M g := by
  rw [map_mul, mkP_xK, one_mul]

theorem conj_rel_of_xmul {M : ModelData F} {a b : ↥M.K4} (h : a * b * a⁻¹ = M.xK * b⁻¹) :
    mkP M a * mkP M b * (mkP M a)⁻¹ = (mkP M b)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul, h, mkP_xK_mul, map_inv]

theorem mkP_comm_of_comm {M : ModelData F} {a b : ↥M.K4} (h : a * b = b * a) :
    mkP M a * mkP M b = mkP M b * mkP M a := by
  rw [← map_mul, ← map_mul, h]

theorem tP_comm_yP (M : ModelData F) : tP M * yP M = yP M * tP M := by
  have h : tP M * yP M * (tP M)⁻¹ = yP M := by
    rw [tP, yP, ← map_inv, ← map_mul, ← map_mul]
    have : M.wK * M.yK * M.wK⁻¹ = M.xyK := Subtype.ext swapGL_mul_yGL_mul_inv
    rw [this, mkP_xyK]
  exact mul_inv_eq_iff_eq_mul.1 h

structure RotData (M : ModelData F) where
  R : GL (Fin 2) F
  hR : R ∈ M.U2
  hd : dRefl F ∈ M.U2
  hdet : (R : Matrix (Fin 2) (Fin 2) F).det * (R : Matrix (Fin 2) (Fin 2) F).det = 1
  hcR : dRefl F * R * dRefl F = -R⁻¹

theorem swapGL_comm_dg4 (a : GL (Fin 2) F) : swapGL F * dg4 a a = dg4 a a * swapGL F := by
  have := swapGL_mul_diagGL_mul_inv a a
  exact mul_inv_eq_iff_eq_mul.1 this

theorem yGL_comm_dg4 (a b : GL (Fin 2) F) : yGL F * dg4 a b = dg4 a b * yGL F :=
  (diagGL_comm_yGL a b).symm

theorem dRefl_inv' : (dRefl F)⁻¹ = dRefl F := inv_eq_of_mul_eq_one_right dRefl_mul_self

variable {M : ModelData F}

theorem tP_yP_sq : (tP M * yP M) * (tP M * yP M) = 1 := by
  calc tP M * yP M * (tP M * yP M) = tP M * (yP M * tP M) * yP M := by group
    _ = tP M * (tP M * yP M) * yP M := by rw [tP_comm_yP]
    _ = (tP M * tP M) * (yP M * yP M) := by group
    _ = 1 := by rw [tP_sq, yP_sq, one_mul]

variable (D : RotData M)

include D

theorem RotData.mem_rr : dg4 D.R D.R ∈ M.K4 := M.diagGL_mem_K4_iff.2 ⟨D.hR, D.hR, D.hdet⟩

theorem RotData.mem_nu : dg4 (dRefl F) (dRefl F) ∈ M.K4 :=
  M.diagGL_mem_K4_iff.2 ⟨D.hd, D.hd, by rw [det_dRefl]; norm_num⟩

@[expose] noncomputable def RotData.rho1 : PG M := mkP M ⟨dg4 D.R D.R, D.mem_rr⟩

@[expose] noncomputable def RotData.rho2 : PG M := dP M D.R D.hR

@[expose] noncomputable def RotData.nu : PG M := mkP M ⟨dg4 (dRefl F) (dRefl F), D.mem_nu⟩

theorem RotData.nu_nu : D.nu * D.nu = 1 := by
  rw [RotData.nu, ← map_mul]
  have : (⟨dg4 (dRefl F) (dRefl F), D.mem_nu⟩ : ↥M.K4) * ⟨dg4 (dRefl F) (dRefl F), D.mem_nu⟩ = 1 := by
    apply Subtype.ext
    show dg4 (dRefl F) (dRefl F) * dg4 (dRefl F) (dRefl F) = 1
    rw [diagGL_mul, dRefl_mul_self, diagGL_one]
  rw [this, map_one]

theorem RotData.t_nu : tP M * D.nu = D.nu * tP M := by
  rw [RotData.nu, tP]
  refine mkP_comm_of_comm (Subtype.ext ?_)
  show swapGL F * dg4 (dRefl F) (dRefl F) = dg4 (dRefl F) (dRefl F) * swapGL F
  exact swapGL_comm_dg4 _

theorem RotData.y_nu : yP M * D.nu = D.nu * yP M := by
  rw [RotData.nu, yP]
  refine mkP_comm_of_comm (Subtype.ext ?_)
  show yGL F * dg4 (dRefl F) (dRefl F) = dg4 (dRefl F) (dRefl F) * yGL F
  exact yGL_comm_dg4 _ _

theorem RotData.t_rho1 : tP M * D.rho1 = D.rho1 * tP M := by
  rw [RotData.rho1, tP]
  refine mkP_comm_of_comm (Subtype.ext ?_)
  show swapGL F * dg4 D.R D.R = dg4 D.R D.R * swapGL F
  exact swapGL_comm_dg4 _

theorem RotData.y_rho1 : yP M * D.rho1 = D.rho1 * yP M := by
  rw [RotData.rho1, yP]
  refine mkP_comm_of_comm (Subtype.ext ?_)
  show yGL F * dg4 D.R D.R = dg4 D.R D.R * yGL F
  exact yGL_comm_dg4 _ _

theorem RotData.y_rho2 : yP M * D.rho2 = D.rho2 * yP M := by
  rw [RotData.rho2, dP, yP]
  refine mkP_comm_of_comm (Subtype.ext ?_)
  show yGL F * dg4 D.R D.R⁻¹ = dg4 D.R D.R⁻¹ * yGL F
  exact yGL_comm_dg4 _ _

theorem RotData.rho1_rho2 : D.rho1 * D.rho2 = D.rho2 * D.rho1 := by
  rw [RotData.rho1, RotData.rho2, dP]
  refine mkP_comm_of_comm (Subtype.ext ?_)
  show dg4 D.R D.R * dg4 D.R D.R⁻¹ = dg4 D.R D.R⁻¹ * dg4 D.R D.R
  rw [diagGL_mul, diagGL_mul, mul_inv_cancel, inv_mul_cancel]

theorem RotData.nu_rho1 : D.nu * D.rho1 * D.nu⁻¹ = D.rho1⁻¹ := by
  rw [RotData.nu, RotData.rho1]
  apply conj_rel_of_xmul
  apply Subtype.ext
  show dg4 (dRefl F) (dRefl F) * dg4 D.R D.R * (dg4 (dRefl F) (dRefl F))⁻¹ =
    dg4 (-1 : GL (Fin 2) F) (-1) * (dg4 D.R D.R)⁻¹
  rw [diagGL_inv, diagGL_inv, diagGL_mul, diagGL_mul, diagGL_mul, dRefl_inv', D.hcR, neg_one_mul]

theorem RotData.nu_rho2 : D.nu * D.rho2 * D.nu⁻¹ = D.rho2⁻¹ := by
  rw [RotData.nu, RotData.rho2, dP]
  apply conj_rel_of_xmul
  apply Subtype.ext
  show dg4 (dRefl F) (dRefl F) * dg4 D.R D.R⁻¹ * (dg4 (dRefl F) (dRefl F))⁻¹ =
    dg4 (-1 : GL (Fin 2) F) (-1) * (dg4 D.R D.R⁻¹)⁻¹
  have h2 : dRefl F * D.R⁻¹ * dRefl F = -D.R := by
    have e : dRefl F * D.R⁻¹ * dRefl F = (dRefl F * D.R * dRefl F)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, dRefl_inv']
      group
    rw [e, D.hcR, inv_neg, inv_inv]
  rw [diagGL_inv, diagGL_inv, diagGL_mul, diagGL_mul, diagGL_mul, dRefl_inv', D.hcR, h2, inv_inv,
    neg_one_mul, neg_one_mul]

theorem RotData.A_nu : (tP M * yP M) * D.nu = D.nu * (tP M * yP M) := by
  calc tP M * yP M * D.nu = tP M * (yP M * D.nu) := by group
    _ = tP M * (D.nu * yP M) := by rw [D.y_nu]
    _ = (tP M * D.nu) * yP M := by group
    _ = (D.nu * tP M) * yP M := by rw [D.t_nu]
    _ = D.nu * (tP M * yP M) := by group

theorem RotData.A_rho1 : (tP M * yP M) * D.rho1 = D.rho1 * (tP M * yP M) := by
  calc tP M * yP M * D.rho1 = tP M * (yP M * D.rho1) := by group
    _ = tP M * (D.rho1 * yP M) := by rw [D.y_rho1]
    _ = (tP M * D.rho1) * yP M := by group
    _ = (D.rho1 * tP M) * yP M := by rw [D.t_rho1]
    _ = D.rho1 * (tP M * yP M) := by group

theorem RotData.A_rho2 : (tP M * yP M) * D.rho2 * (tP M * yP M)⁻¹ = D.rho2⁻¹ := by
  have hy : yP M * D.rho2 * (yP M)⁻¹ = D.rho2 := by rw [D.y_rho2]; group
  calc tP M * yP M * D.rho2 * (tP M * yP M)⁻¹ = tP M * (yP M * D.rho2 * (yP M)⁻¹) * (tP M)⁻¹ := by
        group
    _ = tP M * D.rho2 * (tP M)⁻¹ := by rw [hy]
    _ = D.rho2⁻¹ := by rw [RotData.rho2]; exact tP_conj_dP M D.hR


theorem RotData.coe_g1_pow (j : ℕ) :
    (((⟨dg4 D.R D.R, D.mem_rr⟩ : ↥M.K4) ^ j : ↥M.K4) : GL (Fin 4) F) = dg4 (D.R ^ j) (D.R ^ j) := by
  rw [Subgroup.coe_pow, diagGL_pow]

theorem RotData.coe_g2_pow (j : ℕ) :
    (((⟨dg4 D.R D.R⁻¹, diag_inv_mem_K4 M D.hR⟩ : ↥M.K4) ^ j : ↥M.K4) : GL (Fin 4) F) =
      dg4 (D.R ^ j) (D.R⁻¹ ^ j) := by
  rw [Subgroup.coe_pow, diagGL_pow]

theorem RotData.rho1_pow (j : ℕ) :
    D.rho1 ^ j = mkP M ((⟨dg4 D.R D.R, D.mem_rr⟩ : ↥M.K4) ^ j) := by
  rw [RotData.rho1, map_pow]

theorem RotData.rho2_pow (j : ℕ) :
    D.rho2 ^ j = mkP M ((⟨dg4 D.R D.R⁻¹, diag_inv_mem_K4 M D.hR⟩ : ↥M.K4) ^ j) := by
  rw [RotData.rho2, dP, map_pow]

omit D in
theorem neg_one_gl_inv : (-1 : GL (Fin 2) F)⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by simp)

omit D in
theorem neg_one_gl_ne_one (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 :=
  ModelData.neg_one_ne_one_gl2 h2

theorem RotData.rho1_pow_half {n : ℕ} (hRn : D.R ^ 2 ^ (n - 1) = -1) : D.rho1 ^ 2 ^ (n - 1) = 1 := by
  rw [D.rho1_pow]
  have : ((⟨dg4 D.R D.R, D.mem_rr⟩ : ↥M.K4) ^ 2 ^ (n - 1)) = M.xK := by
    apply Subtype.ext
    rw [D.coe_g1_pow, hRn]
    rfl
  rw [this, mkP_xK]

theorem RotData.rho2_pow_half {n : ℕ} (hRn : D.R ^ 2 ^ (n - 1) = -1) : D.rho2 ^ 2 ^ (n - 1) = 1 := by
  rw [D.rho2_pow]
  have : ((⟨dg4 D.R D.R⁻¹, diag_inv_mem_K4 M D.hR⟩ : ↥M.K4) ^ 2 ^ (n - 1)) = M.xK := by
    apply Subtype.ext
    rw [D.coe_g2_pow, inv_pow, hRn, neg_one_gl_inv]
    rfl
  rw [this, mkP_xK]


omit D in
theorem pow_two_pow_sub_one {α : Type*} [Monoid α] (x : α) {n : ℕ} (hn : 3 ≤ n) :
    x ^ 2 ^ (n - 1) = (x ^ 2 ^ (n - 2)) ^ 2 := by
  rw [← pow_mul]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [pow_succ]

theorem RotData.false_of_pow_mem (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    (hRn : D.R ^ 2 ^ (n - 1) = -1) {a b : GL (Fin 2) F} (ha : a = D.R ^ 2 ^ (n - 2))
    (hmem : dg4 a b = 1 ∨ dg4 a b = dg4 (-1 : GL (Fin 2) F) (-1)) : False := by
  have hsq := pow_two_pow_sub_one D.R hn
  rw [hRn, ← ha] at hsq
  rcases hmem with h | h
  · have h3 : dg4 a b = dg4 1 1 := by rw [h, diagGL_one]
    have h4 := (diagGL_inj h3).1
    rw [h4, one_pow] at hsq
    exact neg_one_gl_ne_one h2 hsq
  · have h4 := (diagGL_inj h).1
    rw [h4, neg_one_sq] at hsq
    exact neg_one_gl_ne_one h2 hsq

theorem RotData.rho1_pow_ne_one (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) {n : ℕ} (hn : 3 ≤ n)
    (hRn : D.R ^ 2 ^ (n - 1) = -1) : D.rho1 ^ 2 ^ (n - 2) ≠ 1 := by
  intro h
  rw [D.rho1_pow] at h
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  refine D.false_of_pow_mem h2 hn hRn (a := D.R ^ 2 ^ (n - 2)) (b := D.R ^ 2 ^ (n - 2)) rfl ?_
  rcases hZ _ hmem with h1 | h1
  · left
    have := congrArg Subtype.val h1
    rw [D.coe_g1_pow] at this
    exact this
  · right
    have := congrArg Subtype.val h1
    rw [D.coe_g1_pow] at this
    exact this

theorem RotData.rho2_pow_ne_one (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) {n : ℕ} (hn : 3 ≤ n)
    (hRn : D.R ^ 2 ^ (n - 1) = -1) : D.rho2 ^ 2 ^ (n - 2) ≠ 1 := by
  intro h
  rw [D.rho2_pow] at h
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  refine D.false_of_pow_mem h2 hn hRn (a := D.R ^ 2 ^ (n - 2)) (b := D.R⁻¹ ^ 2 ^ (n - 2)) rfl ?_
  rcases hZ _ hmem with h1 | h1
  · left
    have := congrArg Subtype.val h1
    rw [D.coe_g2_pow] at this
    exact this
  · right
    have := congrArg Subtype.val h1
    rw [D.coe_g2_pow] at this
    exact this

theorem RotData.orderOf_rho1 (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) {n : ℕ} (hn : 3 ≤ n)
    (hRn : D.R ^ 2 ^ (n - 1) = -1) : orderOf D.rho1 = 2 ^ (n - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : n - 1 = n - 2 + 1 := by omega
  rw [e]
  exact orderOf_eq_prime_pow (D.rho1_pow_ne_one h2 hZ hn hRn) (by rw [← e]; exact D.rho1_pow_half hRn)

theorem RotData.orderOf_rho2 (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) {n : ℕ} (hn : 3 ≤ n)
    (hRn : D.R ^ 2 ^ (n - 1) = -1) : orderOf D.rho2 = 2 ^ (n - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : n - 1 = n - 2 + 1 := by omega
  rw [e]
  exact orderOf_eq_prime_pow (D.rho2_pow_ne_one h2 hZ hn hRn) (by rw [← e]; exact D.rho2_pow_half hRn)

theorem RotData.rho1_pow_ne_rho2_pow (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    (hRn : D.R ^ 2 ^ (n - 1) = -1) : D.rho1 ^ 2 ^ (n - 2) ≠ D.rho2 ^ 2 ^ (n - 2) := by
  intro h
  rw [D.rho1_pow, D.rho2_pow] at h
  have h1mem : dg4 (D.R ^ 2 ^ (n - 2)) (D.R ^ 2 ^ (n - 2)) ∈ M.K4 := by
    have := ((⟨dg4 D.R D.R, D.mem_rr⟩ : ↥M.K4) ^ 2 ^ (n - 2)).2
    rwa [D.coe_g1_pow] at this
  have h2mem : dg4 (D.R ^ 2 ^ (n - 2)) (D.R⁻¹ ^ 2 ^ (n - 2)) ∈ M.K4 := by
    have := ((⟨dg4 D.R D.R⁻¹, diag_inv_mem_K4 M D.hR⟩ : ↥M.K4) ^ 2 ^ (n - 2)).2
    rwa [D.coe_g2_pow] at this
  have e1 : (⟨dg4 D.R D.R, D.mem_rr⟩ : ↥M.K4) ^ 2 ^ (n - 2) =
      ⟨dg4 (D.R ^ 2 ^ (n - 2)) (D.R ^ 2 ^ (n - 2)), h1mem⟩ := Subtype.ext (D.coe_g1_pow _)
  have e2 : (⟨dg4 D.R D.R⁻¹, diag_inv_mem_K4 M D.hR⟩ : ↥M.K4) ^ 2 ^ (n - 2) =
      ⟨dg4 (D.R ^ 2 ^ (n - 2)) (D.R⁻¹ ^ 2 ^ (n - 2)), h2mem⟩ := Subtype.ext (D.coe_g2_pow _)
  rw [e1, e2] at h
  obtain ⟨c, hc1, hc2⟩ := (mkP_diag_eq_iff h1mem h2mem).1 h
  have hsc : (sc2 c : GL (Fin 2) F) = 1 :=
    mul_right_cancel (b := D.R ^ 2 ^ (n - 2)) (by rw [one_mul]; exact hc1.symm)
  rw [hsc, one_mul, inv_pow] at hc2
  have hsq := pow_two_pow_sub_one D.R hn
  rw [hRn, pow_two] at hsq
  have : D.R ^ 2 ^ (n - 2) * D.R ^ 2 ^ (n - 2) = 1 := by
    nth_rewrite 1 [← hc2]
    exact inv_mul_cancel _
  rw [this] at hsq
  exact neg_one_gl_ne_one h2 hsq

theorem RotData.hasSqLift {n : ℕ} (hn : 3 ≤ n) (hRn : D.R ^ 2 ^ (n - 1) = -1) :
    HasSqLift M (D.rho1 ^ 2 ^ (n - 2)) M.xK := by
  refine ⟨(⟨dg4 D.R D.R, D.mem_rr⟩ : ↥M.K4) ^ 2 ^ (n - 2), D.rho1_pow _ |>.symm, ?_⟩
  rw [← pow_add]
  have e : 2 ^ (n - 2) + 2 ^ (n - 2) = 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp [pow_succ]
    ring
  rw [e]
  apply Subtype.ext
  rw [D.coe_g1_pow, hRn]
  rfl

theorem RotData.dih412 [Finite F] (h2 : (2 : F) ≠ 0) (hZ : ZsTwo M) {n : ℕ} (hn : 3 ≤ n)
    (hRn : D.R ^ 2 ^ (n - 1) = -1) : Dih412 (PG M) n (D.rho1 ^ 2 ^ (n - 2)) :=
  dih412_of_relations (A := tP M * yP M) (ν := D.nu) hn (D.orderOf_rho1 h2 hZ hn hRn)
    (D.orderOf_rho2 h2 hZ hn hRn) (tP_yP_sq) D.nu_nu D.A_nu D.A_rho1 D.nu_rho1 D.A_rho2 D.nu_rho2
    D.rho1_rho2 (D.rho1_pow_ne_rho2_pow h2 hn hRn)

omit D in
theorem not_isCentralInvolution_of_sqLift [Finite F] (hG : GoodModel M) (hZ : ZsTwo M) {u : PG M}
    (hu : HasSqLift M u M.xK) : ¬ CFSG.GH74.IsCentralInvolution u := by
  intro hc
  obtain ⟨S₀, hS₀⟩ := hG.exists_center_sylow
  have hconj : IsConj (yP M) u := central_inv_conj (orderOf_yP M hG.two_ne_zero) hS₀ hc
  have hy : HasSqLift M (yP M) 1 := ⟨M.yK, rfl, M.yK_mul_self⟩
  have h1 : HasSqLift M u 1 := HasSqLift.conj (Subgroup.one_mem _) hy hconj
  have := HasSqLift.unique hZ h1 hu
  have hx : M.xK ≠ 1 := by
    intro h
    have := M.orderOf_xK hG.two_ne_zero
    rw [h, orderOf_one] at this
    omega
  exact hx this.symm

omit D in
theorem isConj_of_not_central [Finite F] (hG : GoodModel M) (hZ : ZsTwo M) (hC : ClsFacts M)
    {u v : PG M} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (hnu : ¬ CFSG.GH74.IsCentralInvolution u) (hnv : ¬ CFSG.GH74.IsCentralInvolution v) :
    IsConj u v := by
  have hy : CFSG.GH74.IsCentralInvolution (yP M) := by
    obtain ⟨S, hS⟩ := hG.exists_center_sylow
    refine ⟨orderOf_yP M hG.two_ne_zero, S, ?_, ?_⟩
    · exact ((hS _).2 (Subgroup.mem_zpowers _)).1
    · exact ((hS _).2 (Subgroup.mem_zpowers _)).2
  have key : ∀ w : PG M, orderOf w = 2 → ¬ CFSG.GH74.IsCentralInvolution w →
      IsConj (tP M * yP M) w := by
    intro w hw hnw
    rcases all_inv_classes hG hZ hC hw with h | h
    · exfalso
      apply hnw
      obtain ⟨g, hg⟩ := isConj_iff.1 h
      rw [← hg]
      exact isCentralInvolution_conj hy g
    · exact h
  exact (key u hu hnu).symm.trans (key v hv hnv)

omit D in
theorem card_PG_eq_of_good [Finite F] (hG : GoodModel M) (hZ : ZsTwo M) {m : ℕ}
    (hU : Nat.card ↥M.U2 = Nat.card ↥M.H2 * m) :
    ∃ o : ℕ, Odd o ∧ Nat.card (PG M) = o * (m * Nat.card ↥M.H2 ^ 2) := by
  refine ⟨(Nsub M).index, hG.odd_index, ?_⟩
  have h1 : (Cg M).index * Nat.card ↥(Cg M) = Nat.card (PG M) := Subgroup.index_mul_card (Cg M)
  rw [index_C M] at h1
  have h2 := card_Cg_eq_UH hG.two_ne_zero hZ
  rw [hU] at h2
  rw [← h1, h2]
  ring

theorem prop412_of_rotData [Finite F] (hG : GoodModel M) (hZ : ZsTwo M) (hC : ClsFacts M) {n : ℕ}
    (hn : 3 ≤ n) (hRn : D.R ^ 2 ^ (n - 1) = -1) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card (PG M) = 2 ^ (2 * n + 1) * m) : Prop412 (PG M) :=
  ⟨fun _ _ hu hv hnu hnv => isConj_of_not_central hG hZ hC hu hv hnu hnv, n, m, hm, hcard,
    D.rho1 ^ 2 ^ (n - 2), not_isCentralInvolution_of_sqLift hG hZ (D.hasSqLift hn hRn),
    D.dih412 hG.two_ne_zero hZ hn hRn⟩

end Model
