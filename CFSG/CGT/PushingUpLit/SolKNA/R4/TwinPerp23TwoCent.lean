module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoTrans
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoAlg

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace Perp23

namespace Two

section Cent

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W K K' : Subgroup Y} {t : Y}

theorem mem_normalizer_closure_pair {a b g : Y}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b} : Set Y))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b} : Set Y)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set Y) : Set Y) := by
  set E := Subgroup.closure ({a, b} : Set Y) with hE
  have hle : conjSub g E ≤ E := by
    rw [hE, conjSub_closure_pair, Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact ha
    · rw [Set.mem_singleton_iff.mp h]; exact hb
  have hcard : Nat.card E ≤ Nat.card (conjSub g E) := by
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem conj_mem_mgrp (hΩ : ConjInvariant Ω) {n : Y} (hn : n ∈ Subgroup.normalizer (W : Set Y))
    {x : Y} (hx : x ∈ MGrp Ω W) : n * x * n⁻¹ ∈ MGrp Ω W := by
  have h : MGrp Ω W ≤ (MGrp Ω W).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun R hR y hy => ?_
    have hRn : conjSub n R ∈ DSet Ω W := by
      have := conj_mem_DSet hΩ hR n
      rwa [mem_normalizer_iff_conjSub_eq.mp hn] at this
    exact (le_iSup₂_of_le (f := fun (R : Subgroup Y) (_ : R ∈ DSet Ω W) => R) (conjSub n R) hRn
      le_rfl) (conj_mem_conjSub hy)
  simpa using h hx

namespace TwoFrame

variable (D : TwoFrame Ω W K K' t)

include D

theorem j_mem_W : D.F.j ∈ W := D.z₃ ▸ W.pow_mem D.x₃_mem_W _

theorem j_sq : D.F.j * D.F.j = 1 := D.F.hj.sq

theorem r_j (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.F.ρ.r * D.F.j * D.F.ρ.r⁻¹ = D.F.j * t := by
  have h : D.F.ρ.r * D.x₃ ^ (2 * D.m) * D.F.ρ.r⁻¹ = D.x₃ ^ (2 * D.m) * D.x₁ ^ (2 * D.m) := by
    rw [← conj_pow, D.r₃]
    exact Commute.mul_pow (hc _ D.x₃_mem_W _ D.x₁_mem_W) _
  rwa [D.z₃, D.z₁] at h

theorem t_j (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.F.ρ'.r * D.F.j * D.F.ρ'.r⁻¹ = D.F.j * t := by
  have h : D.F.ρ'.r * D.x₃ ^ (2 * D.m) * D.F.ρ'.r⁻¹ = D.x₃ ^ (2 * D.m) * D.x₂ ^ (2 * D.m) := by
    rw [← conj_pow, D.t₃]
    exact Commute.mul_pow (hc _ D.x₃_mem_W _ D.x₂_mem_W) _
  rwa [D.z₃, D.z₂] at h

theorem s_t (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹ = t * D.F.j := by
  have h : D.F.ρ₃.r * D.x₁ ^ (2 * D.m) * D.F.ρ₃.r⁻¹ = D.x₁ ^ (2 * D.m) * D.x₃ ^ (2 * D.m) := by
    rw [← conj_pow, D.s₁]
    exact Commute.mul_pow (hc _ D.x₁_mem_W _ D.x₃_mem_W) _
  rwa [D.z₃, D.z₁] at h

theorem s_j : D.F.ρ₃.r * D.F.j * D.F.ρ₃.r⁻¹ = D.F.j := by
  have h : D.F.ρ₃.r * D.x₃ ^ (2 * D.m) * D.F.ρ₃.r⁻¹ = (D.x₃ ^ (2 * D.m))⁻¹ := by
    rw [← conj_pow, D.s₃, inv_pow]
  rw [D.z₃] at h
  rw [h]
  exact inv_eq_of_mul_eq_one_right D.j_sq

theorem mgrp_le_normalizer (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (c : Q3CL.Thompson.Ctx Ω W) :
    MGrp Ω W ≤ Subgroup.normalizer (Subgroup.closure ({t, D.F.j} : Set Y) : Set Y) := by
  have hc := WTool.comm_of_mem_wSet hΩ hW
  set E := Subgroup.closure ({t, D.F.j} : Set Y) with hE
  have ht : t ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hj : D.F.j ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrt : D.F.ρ.r * t * D.F.ρ.r⁻¹ = t := by
    rw [D.r_t]; group
  have hr't : D.F.ρ'.r * t * D.F.ρ'.r⁻¹ = t := by
    have := (TwoFrame.hzK' D).commute_of_mem D.r'_mem_K'
    rw [← this]; group
  refine D.mgrp_le hΩ hW c ?_ ?_ ?_ ?_
  · refine mem_normalizer_closure_pair ?_ ?_
    · rw [hrt]; exact ht
    · rw [D.r_j hc]; exact E.mul_mem hj ht
  · refine mem_normalizer_closure_pair ?_ ?_
    · rw [hr't]; exact ht
    · rw [D.t_j hc]; exact E.mul_mem hj ht
  · refine mem_normalizer_closure_pair ?_ ?_
    · rw [D.s_t hc]; exact E.mul_mem ht hj
    · rw [D.s_j]; exact hj
  · have hWC : W ⊔ OCW W ≤ Subgroup.centralizer (W : Set Y) := by
      refine sup_le (fun x hx => ?_) (Thompson.OCW_le_centralizer W)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hc y hy x hx
    intro w hw
    have hwc := Subgroup.mem_centralizer_iff.mp (hWC hw)
    refine mem_normalizer_closure_pair ?_ ?_
    · have : w * t * w⁻¹ = t := by rw [← hwc t D.t_mem_W]; group
      rw [this]; exact ht
    · have : w * D.F.j * w⁻¹ = D.F.j := by rw [← hwc D.F.j D.j_mem_W]; group
      rw [this]; exact hj

theorem r_mem_mgrp : D.F.ρ.r ∈ MGrp Ω W :=
  (le_iSup₂_of_le (f := fun (R : Subgroup Y) (_ : R ∈ DSet Ω W) => R) D.F.ρ.R D.F.ρ.hR le_rfl)
    D.F.ρ.hr

theorem r'_mem_mgrp : D.F.ρ'.r ∈ MGrp Ω W :=
  (le_iSup₂_of_le (f := fun (R : Subgroup Y) (_ : R ∈ DSet Ω W) => R) D.F.ρ'.R D.F.ρ'.hR le_rfl)
    D.F.ρ'.hr

theorem s_mem_mgrp : D.F.ρ₃.r ∈ MGrp Ω W :=
  (le_iSup₂_of_le (f := fun (R : Subgroup Y) (_ : R ∈ DSet Ω W) => R) D.F.ρ₃.R D.F.ρ₃.hR le_rfl)
    D.F.ρ₃.hr

theorem b_mem_K : D.b ∈ K := by
  have := D.F.ρ.hRK.1 D.b_mem_R
  rwa [D.hρK] at this

theorem b'_mem_K' : D.b' ∈ K' := by
  have := D.F.ρ'.hRK.1 D.b'_mem_R
  rwa [D.hρ'K] at this

@[expose] def ce : Y := (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m

theorem e_mem_W : D.ce ∈ W :=
  W.pow_mem (W.mul_mem (W.mul_mem D.x₁_mem_W (W.inv_mem D.x₂_mem_W)) (W.pow_mem D.x₃_mem_W 2)) _

theorem e_nf (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    D.ce = D.x₁ ^ (D.m : ℤ) * D.x₂ ^ (-(D.m : ℤ)) * D.x₃ ^ (2 * (D.m : ℤ)) := by
  rw [ce, ← zpow_natCast]
  exact A3Mod.pow_triple (hc _ D.x₁_mem_W _ D.x₂_mem_W) (hc _ D.x₁_mem_W _ D.x₃_mem_W)
    (hc _ D.x₂_mem_W _ D.x₃_mem_W) _

theorem pow_four_m (x : Y) (hx : orderOf x = 4 * D.m) (k : ℤ) :
    x ^ (k + ((4 * D.m : ℕ) : ℤ)) = x ^ k := by
  rw [zpow_add, zpow_natCast, ← hx, pow_orderOf_eq_one, mul_one]

theorem r_e (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.F.ρ.r * D.ce * D.F.ρ.r⁻¹ = D.ce := by
  rw [D.e_nf hc, A3Mod.conj_nf_r (hc _ D.x₁_mem_W _ D.x₂_mem_W) (hc _ D.x₁_mem_W _ D.x₃_mem_W)
    D.r₁ D.r₂ D.r₃]
  rw [show 2 * (D.m : ℤ) - (D.m : ℤ) = (D.m : ℤ) by ring]

theorem t_e (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.F.ρ'.r * D.ce * D.F.ρ'.r⁻¹ = D.ce := by
  rw [D.e_nf hc, A3Mod.conj_nf_t (hc _ D.x₂_mem_W _ D.x₃_mem_W) D.t₁ D.t₂ D.t₃]
  rw [show 2 * (D.m : ℤ) - -(D.m : ℤ) = -(D.m : ℤ) + ((4 * D.m : ℕ) : ℤ) by push_cast; ring,
    D.pow_four_m D.x₂ D.o₂]

theorem s_e (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.F.ρ₃.r * D.ce * D.F.ρ₃.r⁻¹ = D.ce := by
  rw [D.e_nf hc, A3Mod.conj_nf_s (hc _ D.x₁_mem_W _ D.x₃_mem_W) (hc _ D.x₂_mem_W _ D.x₃_mem_W)
    D.s₁ D.s₂ D.s₃]
  congr 1
  have h := D.pow_four_m D.x₃ D.o₃ ((D.m : ℤ) + -(D.m : ℤ) - 2 * (D.m : ℤ))
  rw [show (D.m : ℤ) + -(D.m : ℤ) - 2 * (D.m : ℤ) + ((4 * D.m : ℕ) : ℤ) = 2 * (D.m : ℤ) by
    push_cast; ring] at h
  exact h.symm

theorem mgrp_fix_e (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (c : Q3CL.Thompson.Ctx Ω W) :
    ∀ g ∈ MGrp Ω W, g * D.ce = D.ce * g := by
  have hc := WTool.comm_of_mem_wSet hΩ hW
  have hle : MGrp Ω W ≤ Subgroup.centralizer ({D.ce} : Set Y) := by
    refine D.mgrp_le hΩ hW c ?_ ?_ ?_ ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (D.r_e hc))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (D.t_e hc))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (D.s_e hc))
    · refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc w hw D.ce D.e_mem_W)
      · have := Subgroup.mem_centralizer_iff.mp (Thompson.OCW_le_centralizer W hw) D.ce D.e_mem_W
        exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

theorem e_central (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (c : Q3CL.Thompson.Ctx Ω W)
    (he1 : D.ce ≠ 1) {n : Y} (hn : n ∈ Subgroup.normalizer (W : Set Y)) :
    n * D.ce = D.ce * n := by
  have hc := WTool.comm_of_mem_wSet hΩ hW
  have hMfix := D.mgrp_fix_e hΩ hW c
  have hn' : n⁻¹ ∈ Subgroup.normalizer (W : Set Y) := Subgroup.inv_mem _ hn
  have haW : n * D.ce * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hn D.ce).mp D.e_mem_W
  have hfix : ∀ g ∈ MGrp Ω W, g * (n * D.ce * n⁻¹) * g⁻¹ = n * D.ce * n⁻¹ := by
    intro g hg
    have h1 := conj_mem_mgrp hΩ.conjInvariant hn' hg
    rw [inv_inv] at h1
    have h2 := hMfix _ h1
    calc g * (n * D.ce * n⁻¹) * g⁻¹
        = n * ((n⁻¹ * g * n) * D.ce * (n⁻¹ * g * n)⁻¹) * n⁻¹ := by group
      _ = n * D.ce * n⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr h2]
  have hcl : W ≤ Subgroup.closure ({D.x₁, D.x₂, D.x₃} : Set Y) :=
    D.F.W_le_closure c D.he D.hab D.hcomm D.hac D.h₁ D.h₂ D.h₃ D.r₂ D.r₃ D.t₃
  have hfix1 := A3Mod.fixed_eq_one_or (m := D.m) (hc _ D.x₁_mem_W _ D.x₂_mem_W)
    (hc _ D.x₁_mem_W _ D.x₃_mem_W) (hc _ D.x₂_mem_W _ D.x₃_mem_W) D.o₁ D.o₂ D.o₃
    (D.z₁.trans D.z₂.symm) D.r₁ D.r₂ D.r₃ D.t₁ D.t₂ D.t₃ D.s₁ D.s₂ D.s₃ (hcl haW)
    (hfix _ D.r_mem_mgrp) (hfix _ D.r'_mem_mgrp) (hfix _ D.s_mem_mgrp)
  rcases hfix1 with h | h
  · exfalso
    apply he1
    have : D.ce = n⁻¹ * (n * D.ce * n⁻¹) * n := by group
    rw [this, h]; group
  · exact mul_inv_eq_iff_eq_mul.mp h

theorem e_eq_one (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (c : Q3CL.Thompson.Ctx Ω W)
    (hnc : ¬ TwinPerp.WCentralNontrivial W) : D.ce = 1 := by
  by_contra he1
  exact hnc ⟨D.ce, D.e_mem_W, he1, fun g hg => D.e_central hΩ hW c he1 hg⟩

theorem u_mul_e (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : D.u * D.ce = D.F.j := by
  have h4 : D.x₃ ^ (4 * D.m) = 1 := by rw [← D.o₃]; exact pow_orderOf_eq_one _
  have := (A3Mod.triple_facts (hc _ D.x₁_mem_W _ D.x₂_mem_W) (hc _ D.x₁_mem_W _ D.x₃_mem_W)
    (hc _ D.x₂_mem_W _ D.x₃_mem_W) h4 (D.z₁.trans D.z₂.symm)).2.2
  rw [D.z₃] at this
  exact this

theorem j_mem_sup (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (c : Q3CL.Thompson.Ctx Ω W)
    (hnc : ¬ TwinPerp.WCentralNontrivial W) : D.F.j ∈ K ⊔ K' := by
  have hc := WTool.comm_of_mem_wSet hΩ hW
  have h := D.u_mul_e hc
  rw [D.e_eq_one hΩ hW c hnc, mul_one] at h
  rw [← h]
  exact (K ⊔ K').mul_mem (Subgroup.mem_sup_left D.b_mem_K)
    ((K ⊔ K').inv_mem (Subgroup.mem_sup_right D.b'_mem_K'))

theorem conj_mem_sup (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (c : Q3CL.Thompson.Ctx Ω W)
    (hnc : ¬ TwinPerp.WCentralNontrivial W) {g : Y} (hg : g ∈ MGrp Ω W) :
    g * t * g⁻¹ ∈ K ⊔ K' := by
  have hj := D.j_mem_sup hΩ hW c hnc
  have hN := D.mgrp_le_normalizer hΩ hW c hg
  have h1 : g * t * g⁻¹ ∈ conjSub g (Subgroup.closure ({t, D.F.j} : Set Y)) :=
    conj_mem_conjSub (Subgroup.subset_closure (Set.mem_insert _ _))
  rw [mem_normalizer_iff_conjSub_eq.mp hN] at h1
  have hE : Subgroup.closure ({t, D.F.j} : Set Y) ≤ K ⊔ K' := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact Subgroup.mem_sup_left (TwoFrame.hzK D).mem
    · rw [Set.mem_singleton_iff.mp h]; exact hj
  exact hE h1

end TwoFrame

end Cent

end Two

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
