module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XPsi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XCd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XNrm

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T : Subgroup G}

private theorem fzrAux_conj_pow_succ (g m : G) (k : ℕ) :
    g ^ (k + 1) * m * (g ^ (k + 1))⁻¹ = g * (g ^ k * m * (g ^ k)⁻¹) * g⁻¹ := by
  group

theorem fzr_excl_abstract [Finite G] (h : FzStr t tau lam rho Z E W Q R T)
    (hP : t ∈ ⁅Q, zpowers rho⁆) : False := by
  obtain ⟨x1, x2, hx1, hx2, hlam, hb, hE, hZ⟩ := fzr_x_basis h
  obtain ⟨q, hq, hqW⟩ := h.lam_Q
  obtain ⟨hn2Q, hn2W, haW, haE⟩ := fzr_x_sq_mem h hP hq hqW
  obtain ⟨m, hmW, hm⟩ := fzr_x_comm_tau h hq
  obtain ⟨z, hzZ, hzt⟩ := fzr_x_conj_t h hq
  obtain ⟨⟨z1, hz1Z, hz1⟩, ⟨z2, hz2Z, hz2⟩⟩ := fzr_x_conj_x12 h hq hx1 hx2 hlam
  set g : G := q * lam with hg
  have hgT : g ∈ T := T.mul_mem (h.RT (h.QR hq)) h.lam_T
  have hgW : ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun w hw => h.nrm_W g hgT w hw
  have htW : t ∈ W := h.t_mem
  have hx1W : x1 ∈ W := h.EW hx1
  have hx2W : x2 ∈ W := h.EW hx2
  have hzW : ∀ u ∈ Z, u ∈ W := fun u hu => h.EW (h.ZE hu)
  have hZc : ∀ u ∈ Z, fzXZ (fzxCd t x1 x2 u) := fun u hu =>
    hZ _ (by rw [fzxElt_cd hb (hzW u hu)]; exact hu)
  have e_t : fzxCd t x1 x2 (g * t * g⁻¹) = (1, 0, 0) + fzxCd t x1 x2 z := by
    rw [hzt, fzxCd_mul hb htW (hzW z hzZ), fzxCd_t hb]
  have e_1 : fzxCd t x1 x2 (g * x1 * g⁻¹) = (0, 0, 1) + fzxCd t x1 x2 z1 := by
    rw [hz1, fzxCd_mul hb hx2W (hzW z1 hz1Z), fzxCd_x2 hb]
  have e_2 : fzxCd t x1 x2 (g * x2 * g⁻¹) = (0, 1, 0) + fzxCd t x1 x2 z2 := by
    rw [hz2, fzxCd_mul hb hx1W (hzW z2 hz2Z), fzxCd_x1 hb]
  set φ : FzXW → FzXW := fzXMap ((1, 0, 0) + fzxCd t x1 x2 z) ((0, 0, 1) + fzxCd t x1 x2 z1)
    ((0, 1, 0) + fzxCd t x1 x2 z2) with hφ
  have hconj : ∀ w ∈ W, fzxCd t x1 x2 (g * w * g⁻¹) = φ (fzxCd t x1 x2 w) := by
    intro w hw
    rw [fzxCd_conj hb hgW hw, e_t, e_1, e_2]
  have hgaa : g * g ^ 4 * g⁻¹ = g ^ 4 := by group
  have hfix : φ (fzxCd t x1 x2 (g ^ 4)) = fzxCd t x1 x2 (g ^ 4) := by
    rw [← hconj _ haW, hgaa]
  have hone : (fzxCd t x1 x2 (g ^ 4)).1 = 1 := by
    by_contra hne
    apply haE
    have h0 : (fzxCd t x1 x2 (g ^ 4)).1 = 0 := by
      revert hne
      generalize (fzxCd t x1 x2 (g ^ 4)).1 = x
      revert x
      decide
    have := (hE (fzxCd t x1 x2 (g ^ 4))).2 h0
    rwa [fzxElt_cd hb haW] at this
  have hN := fzx_norm4 h.tau_W hm haW
  have hm1W : g * m * g⁻¹ ∈ W := hgW m hmW
  have hm2W : g ^ 2 * m * (g ^ 2)⁻¹ ∈ W := by
    have e : g ^ 2 * m * (g ^ 2)⁻¹ = g * (g * m * g⁻¹) * g⁻¹ := by
      simpa using fzrAux_conj_pow_succ g m 1
    rw [e]; exact hgW _ hm1W
  have hm3W : g ^ 3 * m * (g ^ 3)⁻¹ ∈ W := by
    have e : g ^ 3 * m * (g ^ 3)⁻¹ = g * (g ^ 2 * m * (g ^ 2)⁻¹) * g⁻¹ := by
      simpa using fzrAux_conj_pow_succ g m 2
    rw [e]; exact hgW _ hm2W
  have c1 : fzxCd t x1 x2 (g * m * g⁻¹) = φ (fzxCd t x1 x2 m) := hconj m hmW
  have c2 : fzxCd t x1 x2 (g ^ 2 * m * (g ^ 2)⁻¹) = φ (φ (fzxCd t x1 x2 m)) := by
    have e : g ^ 2 * m * (g ^ 2)⁻¹ = g * (g * m * g⁻¹) * g⁻¹ := by
      simpa using fzrAux_conj_pow_succ g m 1
    rw [e, hconj _ hm1W, c1]
  have c3 : fzxCd t x1 x2 (g ^ 3 * m * (g ^ 3)⁻¹) = φ (φ (φ (fzxCd t x1 x2 m))) := by
    have e : g ^ 3 * m * (g ^ 3)⁻¹ = g * (g ^ 2 * m * (g ^ 2)⁻¹) * g⁻¹ := by
      simpa using fzrAux_conj_pow_succ g m 2
    rw [e, hconj _ hm2W, c2]
  have hN2 : fzXN4 ((1, 0, 0) + fzxCd t x1 x2 z) ((0, 0, 1) + fzxCd t x1 x2 z1)
      ((0, 1, 0) + fzxCd t x1 x2 z2) (fzxCd t x1 x2 m) =
        (2 : ℕ) • fzxCd t x1 x2 (g ^ 4) := by
    have hsum := congrArg (fzxCd t x1 x2) hN
    rw [fzxCd_mul hb (W.mul_mem (W.mul_mem hm3W hm2W) hm1W) hmW,
      fzxCd_mul hb (W.mul_mem hm3W hm2W) hm1W, fzxCd_mul hb hm3W hm2W, c1, c2, c3,
      fzxCd_pow hb haW] at hsum
    unfold fzXN4
    rw [← hsum]
    abel
  have hchk := fzx_check (hZc z hzZ) (hZc z1 hz1Z) (hZc z2 hz2Z) hone hfix hN2
  have htg : g * t * g⁻¹ ∈ W := hgW t htW
  have h2 : fzxCd t x1 x2 (g * (g * t * g⁻¹) * g⁻¹) = fzxCd t x1 x2 t := by
    rw [hconj _ htg, hconj t htW, fzxCd_t hb]
    exact hchk
  have h3 : g * (g * t * g⁻¹) * g⁻¹ = t := by
    have e1 := fzxElt_cd hb (hgW _ htg)
    have e2 := fzxElt_cd hb htW
    rw [h2] at e1
    exact e1.symm.trans e2
  have e : g ^ 2 * t * (g ^ 2)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by
    simpa using fzrAux_conj_pow_succ g t 1
  exact h.Q_t (g ^ 2) hn2Q hn2W (by rw [e]; exact h3)

end CFSG.OddStandard.SmallF3.FritzII
