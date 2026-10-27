module

public import CFSG.ClassicalInvolution.Phan.PhanQ27Move

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section LeafA

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem wc_conj (z : V8 K) (k : Fin 4) : wc (conj D z) k = D.τ (wc z k) := by
  fin_cases k <;> rfl

theorem colK_of_orth {x y : V8 K} (hB : B8 x y = 0) (hxy : her D x y = 0) (hx : her D x x ≠ 0)
    (hy : her D y y ≠ 0) : ColK D x y := by
  refine ⟨hB, ?_⟩
  unfold gram
  rw [hxy, zero_mul, sub_zero]
  exact mul_ne_zero hx hy

@[expose] def anisoFF (r1 r2 r3 r4 : K) : V8 K :=
  wvec (-D.θ * r1 + r4) (-D.θ * r2 - r3) (D.θ ^ 2 * r2 + D.θ * r3) (-D.θ ^ 2 * r1 + D.θ * r4)

theorem inW2_anisoFF (r1 r2 r3 r4 : K) : InW2 (anisoFF D r1 r2 r3 r4) := inW2_wvec _ _ _ _

theorem Q8_anisoFF (r1 r2 r3 r4 : K) : Q8 (anisoFF D r1 r2 r3 r4) = 0 := by
  rw [anisoFF, Q8_wvec]
  ring

theorem B8_anisoFF_r (r1 r2 r3 r4 : K) :
    B8 (anisoFF D r1 r2 r3 r4) (wvec r1 r2 r3 r4) = 0 := by
  rw [anisoFF, B8_wvec_wvec]
  ring

theorem her_anisoFF {r1 r2 r3 r4 : K} (hr1 : D.τ r1 = r1) (hr2 : D.τ r2 = r2)
    (hr3 : D.τ r3 = r3) (hr4 : D.τ r4 = r4) :
    her D (anisoFF D r1 r2 r3 r4) (anisoFF D r1 r2 r3 r4) =
      4 * D.θ ^ 2 * (r1 * r3 + r2 * r4) := by
  rw [anisoFF, her_wvec_left]
  simp only [wvec_apply_inl2, wvec_apply_inl3, wvec_apply_inr2, wvec_apply_inr3, map_add, map_sub,
    map_mul, map_neg, map_pow, D.tau_theta, hr1, hr2, hr3, hr4]
  ring

theorem leaf_A (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {a b c d : V8 K} (Fr : QFrame D a b c d)
    {r1 r2 r3 r4 ρc ρd : K} (hr1 : D.τ r1 = r1) (hr2 : D.τ r2 = r2) (hr3 : D.τ r3 = r3)
    (hr4 : D.τ r4 = r4) (hr : r1 * r3 + r2 * r4 ≠ 0)
    (hc : ∀ k, wc c k = ρc * ![r1, r2, r3, r4] k)
    (hd : ∀ k, wc d k = ρd * ![r1, r2, r3, r4] k) : Resolved D a b c d := by
  have hxW : InW2 (anisoFF D r1 r2 r3 r4) := inW2_anisoFF D r1 r2 r3 r4
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hHne : her D (anisoFF D r1 r2 r3 r4) (anisoFF D r1 r2 r3 r4) ≠ 0 := by
    rw [her_anisoFF D hr1 hr2 hr3 hr4]
    exact mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 (theta_ne_zero D hε))) hr
  have orth : ∀ (z : V8 K) (ρ : K), (∀ k, wc z k = ρ * ![r1, r2, r3, r4] k) →
      B8 (anisoFF D r1 r2 r3 r4) z = 0 ∧ her D (anisoFF D r1 r2 r3 r4) z = 0 := by
    intro z ρ hz
    constructor
    · rw [B8_W2_of_coord hxW ρ (d := wvec r1 r2 r3 r4) (fun k => by rw [hz k, wc_wvec]),
        B8_anisoFF_r, mul_zero]
    · have e : ∀ k, wc (conj D z) k = D.τ ρ * wc (wvec r1 r2 r3 r4) k := by
        intro k
        rw [wc_conj, hz k, map_mul, wc_wvec]
        fin_cases k <;> simp [hr1, hr2, hr3, hr4]
      rw [her, B8_W2_of_coord hxW (D.τ ρ) e, B8_anisoFF_r, mul_zero]
  refine Or.inl ⟨anisoFF D r1 r2 r3 r4, ⟨Q8_anisoFF D r1 r2 r3 r4, hHne⟩, ?_, ?_, ?_, ?_⟩
  · exact colK_of_orth D (B8_zero_of_W2_W0 hxW Fr.ha) (her_zero_of_W2_W0 D hxW Fr.ha) hHne
      Fr.haf.2
  · exact colK_of_orth D (B8_zero_of_W2_W0 hxW Fr.hb) (her_zero_of_W2_W0 D hxW Fr.hb) hHne
      Fr.hbf.2
  · obtain ⟨h1, h1'⟩ := orth c ρc hc
    exact colK_of_orth D h1 h1' hHne Fr.hcf.2
  · obtain ⟨h1, h1'⟩ := orth d ρd hd
    exact colK_of_orth D h1 h1' hHne Fr.hdf.2

end LeafA

end CFSG.ClassicalInvolution.PhanQ
