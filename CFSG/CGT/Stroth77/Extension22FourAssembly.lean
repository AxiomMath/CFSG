module
public import CFSG.CGT.Stroth77.Extension22FourBeta

public section
namespace CFSG.CGT.Stroth77
open scoped IsMulCommutative
namespace TorusBasisEquivFour

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}
variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
variable (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
variable (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)

lemma uv0
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) : conjTorusFour D hBC E (hL D.uv_mem_L) (gen (Type200.k m) (0 : Fin 3)) =
    ((Type201.action m).φuv (gen (Type201.k m) (0 : Fin 3)) : Torus (Type200.k m)) := by
  rw [action_eq_printed_add_cocycle E (hL D.uv_mem_L) ((Type200.action m).φuv)]
  change (Type200.action m).φuv (gen (Type200.k m) 0) +
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 0) =
    ((Type201.action m).φuv (gen (Type201.k m) 0) : Torus (Type200.k m))
  rw [cocycleUV_gen0 he hf E hL, add_zero, Type200.uv_c, Type201.uv_c]
  change (-3 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
      (-4 : ℤ) • gen (Type200.k m) 2 =
    (-3 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
      (-4 : ℤ) • gen (Type200.k m) 2
  rfl

lemma uv1 (β : ℤ) (hβ : β = (2:ℤ)^(m+1))
    (huv1 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 2) : conjTorusFour D hBC E (hL D.uv_mem_L) (gen (Type200.k m) (1 : Fin 3)) =
    ((Type201.action m).φuv (gen (Type201.k m) (1 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.uv_a]
  change conjTorusFour D hBC E (hL D.uv_mem_L) (gen (Type200.k m) 1) =
    (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
      (2 * (2:ℤ) ^ m + 2 : ℤ) • gen (Type200.k m) 2
  rw [action_eq_printed_add_cocycle E (hL D.uv_mem_L) ((Type200.action m).φuv)]
  change (Type200.action m).φuv (gen (Type200.k m) 1) +
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) =
    (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
      (2 * (2:ℤ) ^ m + 2 : ℤ) • gen (Type200.k m) 2
  rw [huv1, hβ, Type200.uv_a]
  rw [show (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m by rw [pow_succ]; ring]
  rw [show Torus.c = gen (Type200.k m) 0 from rfl,
    show Torus.a = gen (Type200.k m) 1 from rfl,
    show Torus.b = gen (Type200.k m) 2 from rfl]
  calc (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
        (2 : ℤ) • gen (Type200.k m) 2 + (2 * (2 : ℤ) ^ m) • gen (Type200.k m) 2
      = (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
          ((2 : ℤ) • gen (Type200.k m) 2 + (2 * (2 : ℤ) ^ m) • gen (Type200.k m) 2) := by abel
    _ = (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
          ((2 : ℤ) + 2 * (2 : ℤ) ^ m) • gen (Type200.k m) 2 := by rw [add_zsmul]
    _ = (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
          (2 * (2 : ℤ) ^ m + 2) • gen (Type200.k m) 2 := by
          rw [show (2 : ℤ) + 2 * (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ m + 2 by ring]

lemma uv2 (β : ℤ) (hβ : β = (2:ℤ)^(m+1))
    (huv2 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1) : conjTorusFour D hBC E (hL D.uv_mem_L) (gen (Type200.k m) (2 : Fin 3)) =
    ((Type201.action m).φuv (gen (Type201.k m) (2 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.uv_b]
  change conjTorusFour D hBC E (hL D.uv_mem_L) (gen (Type200.k m) 2) =
    (1 : ℤ) • gen (Type200.k m) 0 +
      (4 * ((2:ℤ) ^ m) ^ 2 + 6 * (2:ℤ) ^ m + 2 : ℤ) • gen (Type200.k m) 1 +
      (1 : ℤ) • gen (Type200.k m) 2
  rw [action_eq_printed_add_cocycle E (hL D.uv_mem_L) ((Type200.action m).φuv)]
  change (Type200.action m).φuv (gen (Type200.k m) 2) +
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) =
    (1 : ℤ) • gen (Type200.k m) 0 +
      (4 * ((2:ℤ) ^ m) ^ 2 + 6 * (2:ℤ) ^ m + 2 : ℤ) • gen (Type200.k m) 1 +
      (1 : ℤ) • gen (Type200.k m) 2
  rw [huv2, hβ, Type200.uv_b]
  rw [show (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m by rw [pow_succ]; ring]
  rw [show Torus.c = gen (Type200.k m) 0 from rfl,
    show Torus.a = gen (Type200.k m) 1 from rfl,
    show Torus.b = gen (Type200.k m) 2 from rfl]
  have htors : ((2 : ℤ) ^ (m + 2)) • gen (Type200.k m) 1 = 0 := by
    rw [zsmul_gen_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hk : Type200.k m 1 ≤ m + 2 := by simp [Type200.k]
    exact_mod_cast pow_dvd_pow 2 hk
  have hdiff : (4 * ((2:ℤ) ^ m) ^ 2 + 6 * (2:ℤ) ^ m + 2 : ℤ) =
      2 + 2 * (2:ℤ) ^ m + (2:ℤ) ^ (m + 2) * (((2:ℤ) ^ m + 1)) := by
    rw [pow_succ]
    ring
  have hbig : ((2 : ℤ) ^ (m + 2) * ((2 : ℤ) ^ m + 1)) •
      gen (Type200.k m) 1 = 0 := by
    rw [show (2 : ℤ) ^ (m + 2) * ((2 : ℤ) ^ m + 1) =
      ((2 : ℤ) ^ m + 1) * (2 : ℤ) ^ (m + 2) by ring]
    rw [mul_zsmul, htors, zsmul_zero]
  rw [hdiff, add_zsmul, add_zsmul, hbig, add_zero]
  abel

lemma t0
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) : conjTorusFour D hBC E (hL D.t_mem_L) (gen (Type200.k m) (0 : Fin 3)) =
    ((Type201.action m).φt (gen (Type201.k m) (0 : Fin 3)) : Torus (Type200.k m)) := by
  rw [action_eq_printed_add_cocycle E (hL D.t_mem_L) ((Type200.action m).φt)]
  change (Type200.action m).φt (gen (Type200.k m) 0) +
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 0) =
    ((Type201.action m).φt (gen (Type201.k m) 0) : Torus (Type200.k m))
  rw [cocycleT_gen0 he hf E hL, add_zero, Type200.t_c, Type201.t_c]
  change (1 : ℤ) • gen (Type200.k m) 0 + (4 : ℤ) • gen (Type200.k m) 1 =
    (1 : ℤ) • gen (Type200.k m) 0 + (4 : ℤ) • gen (Type200.k m) 1
  rfl

lemma t1 (β : ℤ) (hβ : β = (2:ℤ)^(m+1))
    (ht1 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 1) : conjTorusFour D hBC E (hL D.t_mem_L) (gen (Type200.k m) (1 : Fin 3)) =
    ((Type201.action m).φt (gen (Type201.k m) (1 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.t_a]
  change conjTorusFour D hBC E (hL D.t_mem_L) (gen (Type200.k m) 1) =
    (2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 1
  rw [action_eq_printed_add_cocycle E (hL D.t_mem_L) ((Type200.action m).φt)]
  change (Type200.action m).φt (gen (Type200.k m) 1) +
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) =
    (2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 1
  rw [ht1, hβ, Type200.t_a]
  rw [show (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m by rw [pow_succ]; ring]
  rw [← add_zsmul]
  rw [show (-1 : ℤ) + 2 * (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ m - 1 by ring]

lemma t2 (β : ℤ) (hβ : β = (2:ℤ)^(m+1))
    (ht2 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1 + β • gen (Type200.k m) 2) : conjTorusFour D hBC E (hL D.t_mem_L) (gen (Type200.k m) (2 : Fin 3)) =
    ((Type201.action m).φt (gen (Type201.k m) (2 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.t_b]
  change conjTorusFour D hBC E (hL D.t_mem_L) (gen (Type200.k m) 2) =
    (-2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 0 +
      (-2 * (2:ℤ) ^ m - 2 : ℤ) • gen (Type200.k m) 1 +
      (-2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 2
  rw [action_eq_printed_add_cocycle E (hL D.t_mem_L) ((Type200.action m).φt)]
  change (Type200.action m).φt (gen (Type200.k m) 2) +
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) =
    (-2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 0 +
      (-2 * (2:ℤ) ^ m - 2 : ℤ) • gen (Type200.k m) 1 +
      (-2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 2
  rw [ht2, hβ, Type200.t_b]
  rw [show (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m by rw [pow_succ]; ring]
  rw [show Torus.c = gen (Type200.k m) 0 from rfl,
    show Torus.a = gen (Type200.k m) 1 from rfl,
    show Torus.b = gen (Type200.k m) 2 from rfl]
  have hc : ((2 : ℤ) ^ (m + 1)) • gen (Type200.k m) 0 = 0 := by
    rw [zsmul_gen_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast pow_dvd_pow 2 (by omega : m ≤ m + 1)
  have ha : ((2 : ℤ) ^ (m + 2)) • gen (Type200.k m) 1 = 0 := by
    rw [zsmul_gen_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hk : Type200.k m 1 ≤ m + 2 := by simp [Type200.k]
    exact_mod_cast pow_dvd_pow 2 hk
  have hb : ((2 : ℤ) ^ (m + 2)) • gen (Type200.k m) 2 = 0 := by
    rw [zsmul_gen_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hk : Type200.k m 2 ≤ m + 2 := by simp [Type200.k]
    exact_mod_cast pow_dvd_pow 2 hk
  have hzero : (-2 * (2:ℤ) ^ m : ℤ) • gen (Type200.k m) 0 +
      (-4 * (2:ℤ) ^ m : ℤ) • gen (Type200.k m) 1 +
      (-4 * (2:ℤ) ^ m : ℤ) • gen (Type200.k m) 2 = 0 := by
    rw [show (-2 * (2:ℤ) ^ m : ℤ) = -(2 : ℤ) ^ (m + 1) by rw [pow_succ]; ring,
      show (-4 * (2:ℤ) ^ m : ℤ) = -(2 : ℤ) ^ (m + 2) by rw [show m + 2 = m + 1 + 1 by omega, pow_succ]; ring]
    rw [neg_zsmul, neg_zsmul, neg_zsmul, hc, ha, hb]
    simp
  have hident : (-2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 0 +
        (-2 * (2:ℤ) ^ m - 2 : ℤ) • gen (Type200.k m) 1 +
        (-2 * (2:ℤ) ^ m - 1 : ℤ) • gen (Type200.k m) 2 =
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-2 : ℤ) • gen (Type200.k m) 1 +
          (-1 : ℤ) • gen (Type200.k m) 2 +
          (2 * (2:ℤ) ^ m) • gen (Type200.k m) 1 +
          (2 * (2:ℤ) ^ m) • gen (Type200.k m) 2) +
        ((-2 * (2:ℤ) ^ m : ℤ) • gen (Type200.k m) 0 +
          (-4 * (2:ℤ) ^ m : ℤ) • gen (Type200.k m) 1 +
          (-4 * (2:ℤ) ^ m : ℤ) • gen (Type200.k m) 2) := by
    module
  rw [hident, hzero, add_zero]
  abel

lemma u0
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) : conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) (0 : Fin 3)) =
    ((Type201.action m).φu (gen (Type201.k m) (0 : Fin 3)) : Torus (Type200.k m)) := by
  rw [action_eq_printed_add_cocycle E (hL D.u_mem_L) ((Type200.action m).φu)]
  change (Type200.action m).φu (gen (Type200.k m) 0) +
      cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 0) =
    ((Type201.action m).φu (gen (Type201.k m) 0) : Torus (Type200.k m))
  have hz : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 0) = 0 := by rw [hu]; rfl
  rw [hz, add_zero, Type200.u_c, Type201.u_c]
  change (1 : ℤ) • gen (Type200.k m) 0 = (1 : ℤ) • gen (Type200.k m) 0
  rfl

lemma u1
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) : conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) (1 : Fin 3)) =
    ((Type201.action m).φu (gen (Type201.k m) (1 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.u_a]
  change conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 1) =
    (1 : ℤ) • gen (Type200.k m) 2
  rw [action_eq_printed_add_cocycle E (hL D.u_mem_L) ((Type200.action m).φu)]
  change (Type200.action m).φu (gen (Type200.k m) 1) +
      cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) =
    (1 : ℤ) • gen (Type200.k m) 2
  have hz : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by rw [hu]; rfl
  rw [hz, add_zero, Type200.u_a]

lemma u2
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) : conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) (2 : Fin 3)) =
    ((Type201.action m).φu (gen (Type201.k m) (2 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.u_b]
  change conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 2) =
    (1 : ℤ) • gen (Type200.k m) 1
  rw [action_eq_printed_add_cocycle E (hL D.u_mem_L) ((Type200.action m).φu)]
  change (Type200.action m).φu (gen (Type200.k m) 2) +
      cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) =
    (1 : ℤ) • gen (Type200.k m) 1
  have hz : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by rw [hu]; rfl
  rw [hz, add_zero, Type200.u_b]

lemma rho0
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) : conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) (0 : Fin 3)) =
    ((Type201.action m).φρ (gen (Type201.k m) (0 : Fin 3)) : Torus (Type200.k m)) := by
  rw [action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)]
  change (Type200.action m).φρ (gen (Type200.k m) 0) +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 0) =
    ((Type201.action m).φρ (gen (Type201.k m) 0) : Torus (Type200.k m))
  have hz : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 0) = 0 := by rw [hρ]; rfl
  rw [hz, add_zero, Type200.rho_c, Type201.rho_c]
  change (1 : ℤ) • gen (Type200.k m) 0 = (1 : ℤ) • gen (Type200.k m) 0
  rfl

lemma rho1
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) : conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) (1 : Fin 3)) =
    ((Type201.action m).φρ (gen (Type201.k m) (1 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.rho_a]
  change conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 1) =
    (1 : ℤ) • gen (Type200.k m) 2
  rw [action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)]
  change (Type200.action m).φρ (gen (Type200.k m) 1) +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) =
    (1 : ℤ) • gen (Type200.k m) 2
  have hz : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by rw [hρ]; rfl
  rw [hz, add_zero, Type200.rho_a]

lemma rho2
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) : conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) (2 : Fin 3)) =
    ((Type201.action m).φρ (gen (Type201.k m) (2 : Fin 3)) : Torus (Type200.k m)) := by
  rw [Type201.rho_b]
  change conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 2) =
    (-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
      (-1 : ℤ) • gen (Type200.k m) 2
  rw [action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)]
  change (Type200.action m).φρ (gen (Type200.k m) 2) +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) =
    (-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
      (-1 : ℤ) • gen (Type200.k m) 2
  have hz : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by rw [hρ]; rfl
  rw [hz, add_zero, Type200.rho_b]

theorem conjTorusFour_uv_type201
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (β : ℤ) (hβ : β = (2:ℤ)^(m+1))
    (huv1 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 2)
    (huv2 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1) (j : Fin 3) :
    conjTorusFour D hBC E (hL D.uv_mem_L) (gen (Type200.k m) j) =
      ((Type201.action m).φuv (gen (Type201.k m) j) : Torus (Type200.k m)) := by
  fin_cases j
  · exact uv0 E hL he hf
  · exact uv1 E hL β hβ huv1
  · exact uv2 E hL β hβ huv2

theorem conjTorusFour_t_type201
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (β : ℤ) (hβ : β = (2:ℤ)^(m+1))
    (ht1 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 1)
    (ht2 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1 + β • gen (Type200.k m) 2)
    (j : Fin 3) :
    conjTorusFour D hBC E (hL D.t_mem_L) (gen (Type200.k m) j) =
      ((Type201.action m).φt (gen (Type201.k m) j) : Torus (Type200.k m)) := by
  fin_cases j
  · exact t0 E hL he hf
  · exact t1 E hL β hβ ht1
  · exact t2 E hL β hβ ht2

theorem conjTorusFour_u_type201
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) (j : Fin 3) :
    conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) j) =
      ((Type201.action m).φu (gen (Type201.k m) j) : Torus (Type200.k m)) := by
  fin_cases j
  · exact u0 E hL hu
  · exact u1 E hL hu
  · exact u2 E hL hu

theorem conjTorusFour_ρ_type201
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) (j : Fin 3) :
    conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) j) =
      ((Type201.action m).φρ (gen (Type201.k m) j) : Torus (Type200.k m)) := by
  fin_cases j
  · exact rho0 E hL hρ
  · exact rho1 E hL hρ
  · exact rho2 E hL hρ

theorem type201Images_of_cocycle_forms
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (β : ℤ) (hβ : β = (2:ℤ)^(m+1))
    (huv1 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 2)
    (huv2 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1)
    (ht1 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 1)
    (ht2 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1 + β • gen (Type200.k m) 2) :
    Type201Images D hBC hL e f E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    change (E.symm : Additive C ≃+ Torus (Type201.k m))
      (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElemsFour D hBC e f j))) =
      (Type201.action m).φuv (gen (Type201.k m) j)
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.uv_mem_L) (j := j)]
    exact conjTorusFour_uv_type201 E hL he hf β hβ huv1 huv2 j
  · intro j
    change (E.symm : Additive C ≃+ Torus (Type201.k m))
      (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElemsFour D hBC e f j))) =
      (Type201.action m).φt (gen (Type201.k m) j)
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.t_mem_L) (j := j)]
    exact conjTorusFour_t_type201 E hL he hf β hβ ht1 ht2 j
  · intro j
    change (E.symm : Additive C ≃+ Torus (Type201.k m))
      (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElemsFour D hBC e f j))) =
      (Type201.action m).φu (gen (Type201.k m) j)
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.u_mem_L) (j := j)]
    exact conjTorusFour_u_type201 E hL hu j
  · intro j
    change (E.symm : Additive C ≃+ Torus (Type201.k m))
      (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElemsFour D hBC e f j))) =
      (Type201.action m).φρ (gen (Type201.k m) j)
    rw [← conjTorusFour_basis (D := D) (hBC := hBC) (e := e) (f := f) (E := E)
      (hgC := hL D.ρ_mem_L) (j := j)]
    exact conjTorusFour_ρ_type201 E hL hρ j

theorem type200Images_of_beta_zero
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (β : ℤ) (hβ : β = 0)
    (huv1 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 2)
    (huv2 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1)
    (ht1 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = β • gen (Type200.k m) 1)
    (ht2 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = β • gen (Type200.k m) 1 + β • gen (Type200.k m) 2) :
    Type200Images D hBC hL e f E := by
  refine type200Images_of_cocycle_values_eq_zero E hL he hf hu hρ ?_ ?_ ?_ ?_
  · rw [huv1, hβ]; simp
  · rw [huv2, hβ]; simp
  · rw [ht1, hβ]; simp
  · rw [ht2, hβ]; simp

theorem hasType200Or201AdjustedBasis_of_torusBasis
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    HasType200Or201AdjustedBasis D hBC hL e f he hf E := by
  classical
  obtain ⟨z, w, hz, hw, he1, hf1, E1, hu1⟩ := exists_u_normalized_all E hL he hf
  obtain ⟨z', w', hz', hw', he2, hf2, E2, hu2, hρ2⟩ :=
    exists_rho_normalized_all E1 hL he1 hf1 hu1
  obtain ⟨β, hβcases, huv1, huv2, ht1, ht2⟩ :=
    cocycleUV_cocycleT_forms E2 hL he2 hf2 hu2 hρ2
  haveI : IsMulCommutative C := isMulCommutative_of_torusBasisEquivFour E
  refine ⟨z * z', w * w', ?_, ?_, ?_⟩
  · calc (z * z') * (z * z') = (z * z) * (z' * z') := by
          rw [mul_mul_mul_comm]
      _ = 1 := by rw [hz, hz', mul_one]
  · calc (w * w') * (w * w') = (w * w) * (w' * w') := by
          rw [mul_mul_mul_comm]
      _ = 1 := by rw [hw, hw', mul_one]
  · rw [← mul_assoc, ← mul_assoc]
    refine ⟨E2, ?_⟩
    rcases hβcases with hβ0 | hβ2
    · exact Or.inl (type200Images_of_beta_zero E2 hL he2 hf2 hu2 hρ2 β hβ0
        huv1 huv2 ht1 ht2)
    · exact Or.inr (type201Images_of_cocycle_forms E2 hL he2 hf2 hu2 hρ2 β hβ2
        huv1 huv2 ht1 ht2)

end TorusBasisEquivFour

variable {S : Type*} [Group S] [Finite S]

variable {B C S' : Subgroup S}

end CFSG.CGT.Stroth77
