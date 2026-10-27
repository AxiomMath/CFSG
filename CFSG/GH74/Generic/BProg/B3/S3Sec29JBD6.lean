module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBMu
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D6

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace S3Sec29JB

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J R : Subgroup G}

theorem part_b_of_MuL (hKS : S3Sec29C.S16cKG) {L : Subgroup G} (hMu : MuPkgL K A Q y L)
    (hy : orderOf y = 2) {u : G} (hu : u ∈ Q) (hu2 : orderOf u = 2) :
    y ∉ perfectCoreOf (Jss y L ⊓ centralizer ({u} : Set G)) := by
  obtain ⟨M, hM, h3, hyM, -, hN, hFix⟩ := hMu u hu hu2
  set P := Jss y L ⊓ centralizer ({u} : Set G) with hP
  have hPu : P ≤ centralizer ({u} : Set G) := inf_le_right
  have hPy : P ≤ centralizer ({y} : Set G) := inf_le_left.trans (S3Sec29D5.Jss_le_centralizer _)
  have hPM : P ≤ normalizer (M : Set G) := fun g hg => hN g (Subgroup.mem_inf.2 ⟨hPu hg, hPy hg⟩)
  have hPL : S3Sec29C.FixesLayer u M y P := S3Sec29D5.FixesLayer.mono hFix (fun g hg =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hPu hg, hPy hg⟩,
      S3Sec29D5.Jss_le_cSec _ (Subgroup.mem_inf.1 hg).1⟩)
  have hcore := S3Sec29C.perfectCore_le_cSec hKS hM h3 hyM hy hPu hPM hPL
  intro hyP
  have hZ := B1.PilotS3.center_trivial_of_shape3 hM h3
  have h1 : y = 1 := S3Ctx29.eq_one_of_mem_cSec hZ (Subgroup.zpowers_le.2 hyM)
    (S3Sec29D6.isPGroup_zpowers_of_orderOf_two hy) (Subgroup.mem_zpowers y) (hcore hyP)
  rw [h1, orderOf_one] at hy
  omega

theorem piC_y_eq_central_L (hKS : S3Sec29C.S16cKG) (h : Ctx29w G x K A B Q y y D J)
    {L : Subgroup G} (hBL : B ≤ normalizer (L : Set G))
    (hQL : Q ≤ normalizer (L : Set G)) (hyL : y ∈ cSec L) (hJL : J ≤ cSec L)
    (hR : IsSylowOf 2 R (Jss y L ⊔ Q ⊔ zpowers y))
    (hRB : ∀ g ∈ B ⊓ cSec K, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (h297a : ∀ r ∈ R ⊓ centralizer ({x} : Set G), r * r ∈ Q → r ∈ Q ∨ r * y⁻¹ ∈ Q)
    (h297c : Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) = ⊥) (hMu : MuPkgL K A Q y L)
    {z : ↥(S3.imgBar y J)} (hz : SL2Data ↥(S3.imgBar y J) z) :
    (z : CentralizerBar y) = piC y y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := S3Sec29D2.J_comp h
  set JS := Jss y L with hJS
  have hy2 : y * y = 1 := S3Sec29D6.mul_self_of_orderOf_two h.y_ord
  have hyC : y ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hBy := S3Sec29D2.B_le_centralizer_y h
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := S3Sec29D2.exists_E h
  obtain ⟨hxB0, -⟩ := S3Sec29D2.B_decomp h ⟨hEK, hAE, hEel, hE4⟩
  have hxB : x ∈ B := (Subgroup.mem_inf.1 hxB0).1
  have hxQ : x ∈ Q := h.B0_le_Q hxB0
  have hx2' : orderOf x = 2 := h.circ.1.1.1.1
  have hx2 : x * x = 1 := S3Sec29D6.mul_self_of_orderOf_two hx2'
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxC : x ∈ centralizer ({y} : Set G) := hBy hxB
  have hxL : x ∈ normalizer ((L : Subgroup G) : Set G) := hBL hxB
  have hHy : JS ⊔ Q ⊔ zpowers y ≤ centralizer ({y} : Set G) :=
    sup_le (sup_le (S3Sec29D5.Jss_le_centralizer _) (S3Sec29D5.Q_le_centralizer_y h))
      (Subgroup.zpowers_le.2 hyC)
  have hHL : JS ⊔ Q ⊔ zpowers y ≤ normalizer ((L : Subgroup G) : Set G) :=
    sup_le (sup_le ((S3Sec29D5.Jss_le_cSec _).trans fun g hg => hg.1)
      hQL)
      (Subgroup.zpowers_le.2 hyL.1)
  have hRC : R ≤ centralizer ({y} : Set G) := hR.le.trans hHy
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  have hJJS : J ≤ JS := S3Sec29D5.le_Jss hJ hJL
  have hS1 : IsSylowOf 2 (R ⊓ JS) JS :=
    hR.inf_of_le_normalizer (le_sup_left.trans le_sup_left) (S3Sec29D5.le_normalizer_Jss hHy hHL)
  have hS2 : IsSylowOf 2 (R ⊓ JS ⊓ J) J :=
    hS1.inf_of_le_normalizer hJJS (S3Sec29D5.Jss_le_normalizer_J hJ L)
  rw [inf_assoc, inf_eq_right.2 hJJS] at hS2
  have hzz : (z : CentralizerBar y) * z = 1 := congrArg Subtype.val hz.z_sq
  have hzc : ∀ c ∈ S3.imgBar y J, c * z = z * c := fun c hc =>
    congrArg Subtype.val (hz.z_comm ⟨c, hc⟩)
  obtain ⟨w, hwS, hwz⟩ := S3Sec29D4.exists_lift_central hJ.1 hS2 z.2 hzz hzc
  obtain ⟨hwR, hwJ⟩ := Subgroup.mem_inf.1 hwS
  have hwC : w ∈ centralizer ({y} : Set G) := hRC hwR
  have hww : w * w = 1 := S3Sec29D4.eq_of_piC_eq hRC hR2 (mul_mem hwR hwR) (one_mem R) (by
    rw [piC_mul y hwC hwC, hwz, hzz, piC_one])
  have hw1 : w ≠ 1 := fun h1 => hz.z_ne (Subtype.ext (by rw [← hwz, h1, piC_one]; rfl))
  have hwcJ : w ∈ cSec J := S3Sec29C.mem_cSec_of_piC hJ hwC fun g hg => by
    rw [hwz]
    have := hzc (piC y g) (S3.mem_imgBar.2 ⟨⟨g, hJ.1 hg⟩, hg, (piC_of_mem y (hJ.1 hg)).symm⟩)
    rw [← this]; group
  have hwZ : w ∈ Zstar (Jstar B J) := S3Sec29D5.mem_Zstar_Jstar hJ hBy hwJ hwcJ
  have key : ∀ v ∈ R, v ∈ centralizer ({x} : Set G) → v ∈ Zstar (Jstar B J) → v * v = 1 →
      v = 1 ∨ v = y := by
    intro v hvR hvx hvZ hvv
    have hvR0 : v ∈ (R ⊓ Zstar (Jstar B J)) ⊔ zpowers y :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hvR, hvZ⟩)
    rcases h297a v (Subgroup.mem_inf.2 ⟨hvR, hvx⟩) (by rw [hvv]; exact one_mem Q) with h1 | h1
    · left
      have : v ∈ Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) := Subgroup.mem_inf.2 ⟨h1, hvR0⟩
      rwa [h297c, Subgroup.mem_bot] at this
    · right
      have h2 : v * y⁻¹ ∈ (R ⊓ Zstar (Jstar B J)) ⊔ zpowers y :=
        mul_mem hvR0 (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers y)))
      have : v * y⁻¹ ∈ Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) := Subgroup.mem_inf.2 ⟨h1, h2⟩
      rw [h297c, Subgroup.mem_bot] at this
      exact mul_inv_eq_one.1 this
  have hxR : x * w * x⁻¹ ∈ R := hRB x hxB0 w hwR
  have hxZ : x * w * x⁻¹ ∈ Zstar (Jstar B J) :=
    S3Sec29C.Zstar_conj_mem _ (S3Sec29C.mem_normalizer_Jstar hxB) hwZ
  have hpxw : piC y (x * w * x⁻¹) = piC y x * z * (piC y x)⁻¹ := by
    rw [S3Sec29D4.piC_conj hxC hwC, hwz]
  by_cases hxN : x ∈ normalizer (J : Set G)
  ·
    have hz'mem : piC y x * z * (piC y x)⁻¹ ∈ S3.imgBar y J := by
      rw [← hpxw]
      exact S3.mem_imgBar.2 ⟨⟨x * w * x⁻¹, hRC hxR⟩, (Subgroup.mem_normalizer_iff.1 hxN w).1 hwJ,
        (piC_of_mem y (hRC hxR)).symm⟩
    have hz'z : piC y x * z * (piC y x)⁻¹ = z := by
      set z' : ↥(S3.imgBar y J) := ⟨_, hz'mem⟩ with hz'def
      have hz'2 : z' * z' = 1 := Subtype.ext (by
        show piC y x * z * (piC y x)⁻¹ * (piC y x * z * (piC y x)⁻¹) = 1
        calc piC y x * z * (piC y x)⁻¹ * (piC y x * z * (piC y x)⁻¹) =
            piC y x * ((z : CentralizerBar y) * z) * (piC y x)⁻¹ := by group
          _ = 1 := by rw [hzz]; group)
      rcases hz.invol_eq z' hz'2 with h1 | h1
      · exfalso
        have h2 : piC y x * z * (piC y x)⁻¹ = 1 := congrArg Subtype.val h1
        apply hz.z_ne
        apply Subtype.ext
        have : (z : CentralizerBar y) = (piC y x)⁻¹ * (piC y x * z * (piC y x)⁻¹) * piC y x := by
          group
        rw [this, h2]; simp
      · exact congrArg Subtype.val h1
    have hxw : x * w * x⁻¹ = w := S3Sec29D4.eq_of_piC_eq hRC hR2 hxR hwR (by rw [hpxw, hz'z, hwz])
    have hwx : w ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 (by
      calc w * x = (x * w * x⁻¹) * x := by rw [hxw]
        _ = x * w := by group)
    rcases key w hwR hwx hwZ hww with h1 | h1
    · exact absurd h1 hw1
    · rw [← hwz, h1]
  ·
    have hcc := S3Sec29D5.commConj_of_not_mem_normalizer hJ hxC hxN
    have hcomm : w * (x * w * x⁻¹) = (x * w * x⁻¹) * w := by
      refine S3Sec29D4.eq_of_piC_eq hRC hR2 (mul_mem hwR hxR) (mul_mem hxR hwR) ?_
      rw [piC_mul y hwC (hRC hxR), piC_mul y (hRC hxR) hwC, hpxw, hwz]
      exact hcc z z.2 z z.2
    have hvR : w * (x * w * x⁻¹) ∈ R := mul_mem hwR hxR
    have hvZ : w * (x * w * x⁻¹) ∈ Zstar (Jstar B J) := mul_mem hwZ hxZ
    have hvx : w * (x * w * x⁻¹) ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (by
        calc w * (x * w * x⁻¹) * x = (x * w * x⁻¹) * w * x := by rw [hcomm]
          _ = x * (w * (x⁻¹ * w * x)) := by group
          _ = x * (w * (x * w * x⁻¹)) := by rw [hxi])
    have hvv : w * (x * w * x⁻¹) * (w * (x * w * x⁻¹)) = 1 := by
      calc w * (x * w * x⁻¹) * (w * (x * w * x⁻¹))
          = w * ((x * w * x⁻¹) * w) * (x * w * x⁻¹) := by group
        _ = w * (w * (x * w * x⁻¹)) * (x * w * x⁻¹) := by rw [hcomm]
        _ = (w * w) * (x * (w * w) * x⁻¹) := by group
        _ = 1 := by rw [hww]; group
    rcases key _ hvR hvx hvZ hvv with h1 | h1
    ·
      have hxw : x * w * x⁻¹ = w := by
        have : x * w * x⁻¹ = w⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]; exact inv_eq_of_mul_eq_one_right hww
      have hwx : w ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 (by
        calc w * x = (x * w * x⁻¹) * x := by rw [hxw]
          _ = x * w := by group)
      rcases key w hwR hwx hwZ hww with h2 | h2
      · exact absurd h2 hw1
      · rw [← hwz, h2]
    ·
      exfalso
      have hq := S3Sec29D5.isQuasisimple_imgBar hJ
      set φ := S3Sec29D3.diagHom (S3.imgBar y J) (piC y x) hcc with hφ
      have hπx2 : piC y x * piC y x = 1 := by rw [← piC_mul y hxC hxC, hx2, piC_one]
      have hyw : piC y y = z * (piC y x * z * (piC y x)⁻¹) := by
        have h3 : piC y (w * (x * w * x⁻¹)) = z * (piC y x * z * (piC y x)⁻¹) := by
          rw [piC_mul y hwC (hRC hxR), hpxw, hwz]
        rw [← h3, h1]
      have hyΔ : piC y y ∈ φ.range := ⟨z, by rw [S3Sec29D3.diagHom_apply, hyw]⟩
      have hxJS : x ∈ normalizer ((JS : Subgroup G) : Set G) :=
        S3Sec29D5.le_normalizer_Jss (T := zpowers x) (Subgroup.zpowers_le.2 hxC)
          (Subgroup.zpowers_le.2 hxL) (Subgroup.mem_zpowers x)
      have hΔ : φ.range ≤ S3.imgBar y (JS ⊓ centralizer ({x} : Set G)) := by
        rw [S3Sec29D4.imgBar_inf_centralizer hxC hx2 hxJS]
        rintro _ ⟨c, rfl⟩
        refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2
          (S3Sec29D3.diagHom_comm hcc hπx2 c)⟩
        obtain ⟨c', hc'J, hc'e⟩ := S3.mem_imgBar.1 c.2
        have hc'C : (c' : G) ∈ centralizer ({y} : Set G) := c'.2
        have hxc : x * c' * x⁻¹ ∈ JS :=
          S3Sec29D5.conj_le_Jss hJ hJL hxC hxL ⟨c', hc'J, rfl⟩
        have hxcC : x * c' * x⁻¹ ∈ centralizer ({y} : Set G) :=
          mul_mem (mul_mem hxC hc'C) (inv_mem hxC)
        refine S3.mem_imgBar.2 ⟨⟨c' * (x * c' * x⁻¹), mul_mem hc'C hxcC⟩,
          mul_mem (hJJS hc'J) hxc, ?_⟩
        rw [← piC_of_mem y (mul_mem hc'C hxcC), piC_mul y hc'C hxcC,
          S3Sec29D4.piC_conj hxC hc'C, piC_of_mem y hc'C, hc'e, S3Sec29D3.diagHom_apply]
      have hyP := S3Sec29D4.mem_perfectCoreOf_of_img hΔ
        (S3Sec29D3.diag_perfect hcc hq.1) hyΔ hy2
      exact part_b_of_MuL hKS hMu h.y_ord hxQ hx2' hyP

end S3Sec29JB

end CFSG.GH74.Generic.BProg.B3
