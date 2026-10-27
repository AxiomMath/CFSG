module

public import CFSG.CGT.Stroth77.Extension22Cocycle

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

theorem t100k_zero (m : ℕ) : (StrothTypeIndex.t100 m).k 0 = m := k100_zero m

theorem t100k_one (m : ℕ) : (StrothTypeIndex.t100 m).k 1 = m + 1 := k100_one m

theorem t100k_two (m : ℕ) : (StrothTypeIndex.t100 m).k 2 = m + 1 := k100_two m

section Cross

variable (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
  (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
  {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S))
  (hL : D.L ≤ Subgroup.normalizer C)

theorem wUV_form :
    wUV D hBC hrel hdC hdB hL =
      Φρ D (Φρ D (yT D hBC hrel hdC hdB hL + Φt D (zR D hBC hrel hdC hdB hL) -
        zR D hBC hrel hdC hdB hL)) := by
  have h := rel_bR_bUV D hBC hrel hdC hdB hL
  have h' := congrArg (fun x => Φρ D (Φρ D x)) h
  simp only [map_add, map_sub] at h' ⊢
  rw [Φρ_three D] at h'
  linear_combination h'

theorem Φρ_apply_gens (a b c : ℤ) :
    Φρ D (a • gen (StrothTypeIndex.t100 m).k 0 + b • gen (StrothTypeIndex.t100 m).k 1 +
        c • gen (StrothTypeIndex.t100 m).k 2) =
      (a - 2 * c) • gen (StrothTypeIndex.t100 m).k 0 + (-c) • gen (StrothTypeIndex.t100 m).k 1 +
        (b - c) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [Φρ, matAct_zsmul_gens]
  have hr00 : (StrothTypeIndex.t100 m).action.ρ 0 0 = 1 := by
    show Type100.ρM 0 0 = 1
    decide
  have hr01 : (StrothTypeIndex.t100 m).action.ρ 0 1 = 0 := by
    show Type100.ρM 0 1 = 0
    decide
  have hr02 : (StrothTypeIndex.t100 m).action.ρ 0 2 = -2 := by
    show Type100.ρM 0 2 = -2
    decide
  have hr10 : (StrothTypeIndex.t100 m).action.ρ 1 0 = 0 := by
    show Type100.ρM 1 0 = 0
    decide
  have hr11 : (StrothTypeIndex.t100 m).action.ρ 1 1 = 0 := by
    show Type100.ρM 1 1 = 0
    decide
  have hr12 : (StrothTypeIndex.t100 m).action.ρ 1 2 = -1 := by
    show Type100.ρM 1 2 = -1
    decide
  have hr20 : (StrothTypeIndex.t100 m).action.ρ 2 0 = 0 := by
    show Type100.ρM 2 0 = 0
    decide
  have hr21 : (StrothTypeIndex.t100 m).action.ρ 2 1 = 1 := by
    show Type100.ρM 2 1 = 1
    decide
  have hr22 : (StrothTypeIndex.t100 m).action.ρ 2 2 = -1 := by
    show Type100.ρM 2 2 = -1
    decide
  rw [hr00, hr01, hr02, hr10, hr11, hr12, hr20, hr21, hr22]
  simp only [zero_mul, one_mul, zero_add, add_zero]
  congr 1 <;> ring

theorem Φu_apply_gens (a b c : ℤ) :
    Φu D (a • gen (StrothTypeIndex.t100 m).k 0 + b • gen (StrothTypeIndex.t100 m).k 1 +
        c • gen (StrothTypeIndex.t100 m).k 2) =
      a • gen (StrothTypeIndex.t100 m).k 0 + c • gen (StrothTypeIndex.t100 m).k 1 +
        b • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [Φu, matAct_zsmul_gens]
  have hu00 : (StrothTypeIndex.t100 m).action.u 0 0 = 1 := by
    show Type100.uM 0 0 = 1
    decide
  have hu01 : (StrothTypeIndex.t100 m).action.u 0 1 = 0 := by
    show Type100.uM 0 1 = 0
    decide
  have hu02 : (StrothTypeIndex.t100 m).action.u 0 2 = 0 := by
    show Type100.uM 0 2 = 0
    decide
  have hu10 : (StrothTypeIndex.t100 m).action.u 1 0 = 0 := by
    show Type100.uM 1 0 = 0
    decide
  have hu11 : (StrothTypeIndex.t100 m).action.u 1 1 = 0 := by
    show Type100.uM 1 1 = 0
    decide
  have hu12 : (StrothTypeIndex.t100 m).action.u 1 2 = 1 := by
    show Type100.uM 1 2 = 1
    decide
  have hu20 : (StrothTypeIndex.t100 m).action.u 2 0 = 0 := by
    show Type100.uM 2 0 = 0
    decide
  have hu21 : (StrothTypeIndex.t100 m).action.u 2 1 = 1 := by
    show Type100.uM 2 1 = 1
    decide
  have hu22 : (StrothTypeIndex.t100 m).action.u 2 2 = 0 := by
    show Type100.uM 2 2 = 0
    decide
  rw [hu00, hu01, hu02, hu10, hu11, hu12, hu20, hu21, hu22]
  simp only [zero_mul, one_mul, zero_add, add_zero]

theorem bit_eta (hm : 1 ≤ m) {ε δ θ η : ℕ} (hδ : δ ≤ 1) (hη : η ≤ 1)
    (hX : xU D hBC hrel hdC hdB hL = ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t100 m).k 0 +
      ((δ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((δ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2)
    (hZ : zR D hBC hrel hdC hdB hL = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      ((η : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((θ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2) :
    η = δ := by
  have h := rel_bU_bR D hBC hrel hdC hdB hL
  rw [hX, hZ] at h
  rw [Φρ_apply_gens, Φu_apply_gens] at h
  rw [Φu_apply_gens, Φρ_apply_gens] at h
  rw [Φρ_apply_gens] at h
  rw [gens_add, gens_add, gens_add] at h
  have h' := gens_coord_two_of_eq_zero h
  rw [t100k_two] at h'
  have h2 : (((2 * (θ : ℤ) - (η : ℤ) + (δ : ℤ)) * 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) = 0 := by
    rw [← h']
    push_cast
    ring
  have hdvd : (((2 : ℤ) ^ (m + 1)) : ℤ) ∣ (2 * (θ : ℤ) - (η : ℤ) + (δ : ℤ)) * 2 ^ m := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 * (θ : ℤ) - (η : ℤ) + (δ : ℤ)) * 2 ^ m)
      (2 ^ (m + 1))).1 h2
    simpa using this
  have hsplit : ((2 : ℤ) ^ (m + 1)) = 2 * (2 : ℤ) ^ m := by rw [pow_succ]; ring
  rw [hsplit] at hdvd
  obtain ⟨tt, ht⟩ := hdvd
  have h2m : (0 : ℤ) < (2 : ℤ) ^ m := by positivity
  have h2dvd : (2 : ℤ) ∣ (2 * (θ : ℤ) - (η : ℤ) + (δ : ℤ)) := by
    refine ⟨tt, ?_⟩
    nlinarith [ht]
  omega

theorem Φt_apply_gens (a b c : ℤ) :
    Φt D (a • gen (StrothTypeIndex.t100 m).k 0 + b • gen (StrothTypeIndex.t100 m).k 1 +
        c • gen (StrothTypeIndex.t100 m).k 2) =
      (a - 2 * c) • gen (StrothTypeIndex.t100 m).k 0 +
        (2 * a - b - 2 * c) • gen (StrothTypeIndex.t100 m).k 1 +
        (-c) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [Φt, matAct_zsmul_gens]
  have ht00 : (StrothTypeIndex.t100 m).action.t 0 0 = 1 := by
    show Type100.tM 0 0 = 1; decide
  have ht01 : (StrothTypeIndex.t100 m).action.t 0 1 = 0 := by
    show Type100.tM 0 1 = 0; decide
  have ht02 : (StrothTypeIndex.t100 m).action.t 0 2 = -2 := by
    show Type100.tM 0 2 = -2; decide
  have ht10 : (StrothTypeIndex.t100 m).action.t 1 0 = 2 := by
    show Type100.tM 1 0 = 2; decide
  have ht11 : (StrothTypeIndex.t100 m).action.t 1 1 = -1 := by
    show Type100.tM 1 1 = -1; decide
  have ht12 : (StrothTypeIndex.t100 m).action.t 1 2 = -2 := by
    show Type100.tM 1 2 = -2; decide
  have ht20 : (StrothTypeIndex.t100 m).action.t 2 0 = 0 := by
    show Type100.tM 2 0 = 0; decide
  have ht21 : (StrothTypeIndex.t100 m).action.t 2 1 = 0 := by
    show Type100.tM 2 1 = 0; decide
  have ht22 : (StrothTypeIndex.t100 m).action.t 2 2 = -1 := by
    show Type100.tM 2 2 = -1; decide
  rw [ht00, ht01, ht02, ht10, ht11, ht12, ht20, ht21, ht22]
  simp only [zero_mul, one_mul, zero_add, add_zero]
  congr 1 <;> ring

theorem Φuv_apply_gens (a b c : ℤ) :
    Φuv D (a • gen (StrothTypeIndex.t100 m).k 0 + b • gen (StrothTypeIndex.t100 m).k 1 +
        c • gen (StrothTypeIndex.t100 m).k 2) =
      (-3 * a + 2 * b + 2 * c) • gen (StrothTypeIndex.t100 m).k 0 +
        (-2 * a + b + 2 * c) • gen (StrothTypeIndex.t100 m).k 1 +
        (-2 * a + 2 * b + c) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [Φuv, matAct_zsmul_gens]
  have hv00 : (StrothTypeIndex.t100 m).action.uv 0 0 = -3 := by
    show Type100.uvM 0 0 = -3; decide
  have hv01 : (StrothTypeIndex.t100 m).action.uv 0 1 = 2 := by
    show Type100.uvM 0 1 = 3 - 1; decide
  have hv02 : (StrothTypeIndex.t100 m).action.uv 0 2 = 2 := by
    show Type100.uvM 0 2 = 2; decide
  have hv10 : (StrothTypeIndex.t100 m).action.uv 1 0 = -2 := by
    show Type100.uvM 1 0 = -2; decide
  have hv11 : (StrothTypeIndex.t100 m).action.uv 1 1 = 1 := by
    show Type100.uvM 1 1 = 1; decide
  have hv12 : (StrothTypeIndex.t100 m).action.uv 1 2 = 2 := by
    show Type100.uvM 1 2 = 2; decide
  have hv20 : (StrothTypeIndex.t100 m).action.uv 2 0 = -2 := by
    show Type100.uvM 2 0 = -2; decide
  have hv21 : (StrothTypeIndex.t100 m).action.uv 2 1 = 2 := by
    show Type100.uvM 2 1 = 2; decide
  have hv22 : (StrothTypeIndex.t100 m).action.uv 2 2 = 1 := by
    show Type100.uvM 2 2 = 1; decide
  rw [hv00, hv01, hv02, hv10, hv11, hv12, hv20, hv21, hv22]
  simp only [zero_mul, one_mul, zero_add, add_zero]

theorem neg_gens {k : Fin 3 → ℕ} (a b c : ℤ) :
    -(a • gen k 0 + b • gen k 1 + c • gen k 2) =
      (-a) • gen k 0 + (-b) • gen k 1 + (-c) • gen k 2 := by
  rw [← neg_one_smul ℤ (a • gen k 0 + b • gen k 1 + c • gen k 2), smul_add, smul_add,
    smul_smul, smul_smul, smul_smul]
  norm_num

theorem bit_q (hm : 1 ≤ m) {ε δ α q θ η : ℕ} (hq : q ≤ 1) (hε : ε ≤ 1)
    (hX : xU D hBC hrel hdC hdB hL = ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t100 m).k 0 +
      ((δ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((δ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2)
    (hY : yT D hBC hrel hdC hdB hL = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      ((1 : ℤ) + (α : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((q : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2)
    (hZ : zR D hBC hrel hdC hdB hL = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      ((η : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((θ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2) :
    q = ε := by
  have h := rel_bU_bUV D hBC hrel hdC hdB hL
  rw [wUV_form, hX, hY, hZ] at h
  rw [Φt_apply_gens] at h
  rw [sub_eq_add_neg, neg_gens] at h
  simp only [gens_add] at h
  rw [Φρ_apply_gens, Φρ_apply_gens] at h
  rw [Φu_apply_gens, Φuv_apply_gens] at h
  simp only [gens_add] at h
  have h' := gens_coord_one h
  rw [t100k_one] at h'
  push_cast at h'
  have h2 : (((2 * (θ : ℤ) * 2 ^ m - 2 * (δ : ℤ) * 2 ^ m - (q : ℤ) * 2 ^ m +
      2 * (ε : ℤ) * 2 ^ (m - 1) : ℤ)) : ZMod (2 ^ (m + 1))) = 0 := by
    push_cast
    linear_combination h'
  have h2m : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := by
    have h1 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm]
      rw [pow_succ]
      ring
    exact h1.symm
  have h2p : (((2 ^ (m + 1) : ℕ)) : ℤ) = 2 * (2 : ℤ) ^ m := by
    push_cast
    rw [pow_succ]
    ring
  have htheta : (((2 * (θ : ℤ) * 2 ^ m : ℤ)) : ZMod (2 ^ (m + 1))) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨(θ : ℤ), ?_⟩
    rw [h2p]
    ring
  have hdelta : (((2 * (δ : ℤ) * 2 ^ m : ℤ)) : ZMod (2 ^ (m + 1))) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨(δ : ℤ), ?_⟩
    rw [h2p]
    ring
  have h2b : (((2 * (θ : ℤ) * 2 ^ m - 2 * (δ : ℤ) * 2 ^ m - (q : ℤ) * 2 ^ m +
      (ε : ℤ) * 2 ^ m : ℤ)) : ZMod (2 ^ (m + 1))) = 0 := by
    have he : (2 * (θ : ℤ) * 2 ^ m - 2 * (δ : ℤ) * 2 ^ m - (q : ℤ) * 2 ^ m +
        2 * (ε : ℤ) * 2 ^ (m - 1) : ℤ) =
        (2 * (θ : ℤ) * 2 ^ m - 2 * (δ : ℤ) * 2 ^ m - (q : ℤ) * 2 ^ m +
          (ε : ℤ) * 2 ^ m : ℤ) := by
      linear_combination (ε : ℤ) * h2m
    rw [he] at h2
    exact h2
  have hdvd : ((2 : ℤ) ^ (m + 1)) ∣
      (2 * (θ : ℤ) * 2 ^ m - 2 * (δ : ℤ) * 2 ^ m - (q : ℤ) * 2 ^ m + (ε : ℤ) * 2 ^ m) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ (m + 1))).1 h2b
  have he : (2 * (θ : ℤ) * 2 ^ m - 2 * (δ : ℤ) * 2 ^ m - (q : ℤ) * 2 ^ m +
      (ε : ℤ) * 2 ^ m : ℤ) = ((ε : ℤ) - (q : ℤ) + 2 * (θ : ℤ) - 2 * (δ : ℤ)) * 2 ^ m := by
    ring
  rw [he] at hdvd
  have hsplit : ((2 : ℤ) ^ (m + 1)) = 2 * (2 : ℤ) ^ m := by rw [pow_succ]; ring
  rw [hsplit] at hdvd
  obtain ⟨tt, ht⟩ := hdvd
  have h2mpos : (0 : ℤ) < (2 : ℤ) ^ m := by positivity
  have h2dvd : (2 : ℤ) ∣ ((ε : ℤ) - (q : ℤ) + 2 * (θ : ℤ) - 2 * (δ : ℤ)) := by
    refine ⟨tt, ?_⟩
    nlinarith [ht]
  omega

noncomputable def zAdj (D : StrothTypeData B (StrothTypeIndex.t100 m)) (α θ δ : ℕ) : B :=
  D.c ^ (((α : ℤ) * 2 ^ (m - 1))) * D.a ^ (((θ : ℤ) * 2 ^ m)) *
    D.b ^ ((((θ : ℤ) - (δ : ℤ)) * 2 ^ m))

theorem ec_zAdj (D : StrothTypeData B (StrothTypeIndex.t100 m)) (α θ δ : ℕ) :
    D.ec (zAdj D α θ δ) = ((α : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t100 m).k 0 +
      ((θ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      (((θ : ℤ) - (δ : ℤ)) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [zAdj, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

theorem two_pow_succ_int {m : ℕ} (hm : 1 ≤ m) : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

theorem two_mul_two_pow_int (m : ℕ) : 2 * (2 : ℤ) ^ m = 2 ^ (m + 1) := by
  rw [pow_succ]
  ring

theorem two_pow_pred_mul {m : ℕ} (hm : 1 ≤ m) : (2 : ℤ) ^ (m - 1) * 2 = 2 ^ m := by
  rw [mul_comm]
  exact two_pow_succ_int hm

theorem two_pow_mul_two (m : ℕ) : (2 : ℤ) ^ m * 2 = 2 ^ (m + 1) := by
  rw [mul_comm]
  exact two_mul_two_pow_int m

theorem two_pow_succ_eq_four {m : ℕ} (hm : 1 ≤ m) : (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) := by
  have h1 : m + 1 = (m - 1) + 2 := by omega
  rw [h1, pow_add]
  norm_num
  ring

theorem zAdj_sq (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (α θ δ : ℕ) : zAdj D α θ δ * zAdj D α θ δ = 1 := by
  apply D.ec_injective
  rw [D.ec_mul, ec_zAdj, D.ec_one]
  rw [gens_add]
  have h2m : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := two_pow_succ_int hm
  have h2m' : 2 * (2 : ℤ) ^ m = 2 ^ (m + 1) := two_mul_two_pow_int m
  have h0 : ((((α : ℤ) * 2 ^ (m - 1)) + ((α : ℤ) * 2 ^ (m - 1)) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) = 0 := by
    rw [t100k_zero]
    have he : (((α : ℤ) * 2 ^ (m - 1)) + ((α : ℤ) * 2 ^ (m - 1)) : ℤ) =
        ((α * 2 ^ m : ℕ) : ℤ) := by
      push_cast
      linear_combination (α : ℤ) * h2m
    rw [he, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left _ _
  have h1 : ((((θ : ℤ) * 2 ^ m) + ((θ : ℤ) * 2 ^ m) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) = 0 := by
    rw [t100k_one]
    have he : (((θ : ℤ) * 2 ^ m) + ((θ : ℤ) * 2 ^ m) : ℤ) = ((θ * 2 ^ (m + 1) : ℕ) : ℤ) := by
      push_cast
      linear_combination (θ : ℤ) * h2m'
    rw [he, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left _ _
  have h2 : (((((θ : ℤ) - (δ : ℤ)) * 2 ^ m) + (((θ : ℤ) - (δ : ℤ)) * 2 ^ m) : ℤ) :
      ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) = 0 := by
    rw [t100k_two]
    have he : ((((θ : ℤ) - (δ : ℤ)) * 2 ^ m) + (((θ : ℤ) - (δ : ℤ)) * 2 ^ m) : ℤ) =
        ((((θ : ℤ) - (δ : ℤ)) * 2 ^ (m + 1) : ℤ)) := by
      linear_combination ((θ : ℤ) - (δ : ℤ)) * h2m'
    rw [he]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨((θ : ℤ) - (δ : ℤ)), ?_⟩
    push_cast
    ring
  rw [show (0 : Torus (StrothTypeIndex.t100 m).k) =
    (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 + (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 +
      (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 by simp]
  refine gens_eq_of_coord ?_ ?_ ?_
  · simpa using h0
  · simpa using h1
  · simpa using h2

theorem eq_c_zpow_mul_a_b (D : StrothTypeData B (StrothTypeIndex.t100 m)) {β : B} {i j l : ℤ}
    (h : D.ec β = i • gen (StrothTypeIndex.t100 m).k 0 + j • gen (StrothTypeIndex.t100 m).k 1 +
      l • gen (StrothTypeIndex.t100 m).k 2) :
    β = D.c ^ i * D.a ^ j * D.b ^ l := by
  apply D.ec_injective
  rw [h, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

theorem E_e_inclusion (E : TorusBasisEquiv D hBC d hdC) (hd2 : d * d = (D.c : S))
    (β : B) {i j l : ℤ}
    (hβ : D.ec β = i • gen (StrothTypeIndex.t100 m).k 0 + j • gen (StrothTypeIndex.t100 m).k 1 +
      l • gen (StrothTypeIndex.t100 m).k 2) :
    E.e (Additive.ofMul (⟨β, hBC β.2⟩ : C)) =
      (2 * i) • gen (Type300.k (m + 1)) 0 + j • gen (Type300.k (m + 1)) 1 +
        l • gen (Type300.k (m + 1)) 2 := by
  have hβ' : β = D.c ^ i * D.a ^ j * D.b ^ l := eq_c_zpow_mul_a_b D hβ
  have hdc : (⟨D.c, hBC D.c.2⟩ : C) = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ :=
    (dC_sq D hBC hdC hd2).symm
  have hcimg : E.e (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = (2 : ℤ) • gen (Type300.k (m + 1)) 0 := by
    rw [hdc, ofMul_mul, map_add, E.e_d, two_zsmul]
  have hci : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C)) =
      n • ((2 : ℤ) • gen (Type300.k (m + 1)) 0) := by
    intro n
    have hsub : (⟨D.c ^ n, hBC (D.c ^ n).2⟩ : C) = ⟨D.c, hBC D.c.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, hcimg]
  have hai : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C)) =
      n • gen (Type300.k (m + 1)) 1 := by
    intro n
    have hsub : (⟨D.a ^ n, hBC (D.a ^ n).2⟩ : C) = ⟨D.a, hBC D.a.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, E.e_a]
  have hbi : ∀ n : ℤ, E.e (Additive.ofMul (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C)) =
      n • gen (Type300.k (m + 1)) 2 := by
    intro n
    have hsub : (⟨D.b ^ n, hBC (D.b ^ n).2⟩ : C) = ⟨D.b, hBC D.b.2⟩ ^ n := rfl
    rw [hsub, ofMul_zpow, map_zsmul, E.e_b]
  have hprod : (⟨β, hBC β.2⟩ : C) = ⟨D.c ^ i, hBC (D.c ^ i).2⟩ * ⟨D.a ^ j, hBC (D.a ^ j).2⟩ *
      ⟨D.b ^ l, hBC (D.b ^ l).2⟩ := by
    apply Subtype.ext
    simp [hβ']
  rw [hprod]
  rw [show Additive.ofMul (⟨D.c ^ i, hBC (D.c ^ i).2⟩ * ⟨D.a ^ j, hBC (D.a ^ j).2⟩ *
      ⟨D.b ^ l, hBC (D.b ^ l).2⟩ : C) =
      Additive.ofMul ⟨D.c ^ i, hBC (D.c ^ i).2⟩ + Additive.ofMul ⟨D.a ^ j, hBC (D.a ^ j).2⟩ +
        Additive.ofMul ⟨D.b ^ l, hBC (D.b ^ l).2⟩ by rw [ofMul_mul, ofMul_mul]]
  rw [map_add, map_add, hci, hai, hbi, smul_smul]
  module



end Cross
section Adjust

noncomputable def zS (D : StrothTypeData B (StrothTypeIndex.t100 m)) (α θ δ : ℕ) : S :=
  (zAdj D α θ δ : S)

noncomputable def dAdj (D : StrothTypeData B (StrothTypeIndex.t100 m)) (d : S) (α θ δ : ℕ) : S :=
  d * zS D α θ δ

theorem zS_mem {B : Subgroup S} (D : StrothTypeData B (StrothTypeIndex.t100 m)) (α θ δ : ℕ) :
    zS D α θ δ ∈ B := by
  show ((zAdj D α θ δ : B) : S) ∈ B
  exact (zAdj D α θ δ).2

theorem zS_sq (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) (α θ δ : ℕ) :
    zS D α θ δ * zS D α θ δ = 1 := by
  have h := zAdj_sq D hm α θ δ
  simpa [zS] using congrArg (Subtype.val) h

theorem dAdj_mem {B C : Subgroup S} (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) {d : S} (hdC : d ∈ C) (α θ δ : ℕ) : dAdj D d α θ δ ∈ C :=
  C.mul_mem hdC (hBC (zAdj D α θ δ).2)

theorem dAdj_notMem {B : Subgroup S} (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) {d : S} (hdB : d ∉ B) (α θ δ : ℕ) : dAdj D d α θ δ ∉ B := by
  intro h
  apply hdB
  have hz : zS D α θ δ * zS D α θ δ = 1 := zS_sq D hm α θ δ
  show d ∈ B
  rw [show d = d * (zS D α θ δ * zS D α θ δ) by rw [hz, mul_one], ← mul_assoc]
  exact B.mul_mem h (zS_mem D α θ δ)

theorem dAdj_sq {B C : Subgroup S} (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C)
    (hd2 : d * d = (D.c : S)) (hm : 1 ≤ m) (α θ δ : ℕ) :
    dAdj D d α θ δ * dAdj D d α θ δ = (D.c : S) := by
  letI : CommGroup C := { mul_comm := comm_of_le_centralizer D hBC hC hrel }
  have hcomm : (⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C) =
      (⟨d, hdC⟩ : C) * ⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩ := rfl
  have hz : (⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩ : C) * ⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩ = 1 := by
    apply Subtype.ext
    exact zS_sq D hm α θ δ
  have hCeq : (⟨dAdj D d α θ δ * dAdj D d α θ δ,
        C.mul_mem (dAdj_mem D hBC hdC α θ δ) (dAdj_mem D hBC hdC α θ δ)⟩ : C) =
      Subgroup.inclusion hBC D.c := by
    calc (⟨dAdj D d α θ δ * dAdj D d α θ δ,
          C.mul_mem (dAdj_mem D hBC hdC α θ δ) (dAdj_mem D hBC hdC α θ δ)⟩ : C)
        = (⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C) *
            ⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ := rfl
      _ = ((⟨d, hdC⟩ : C) * ⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩) *
            ((⟨d, hdC⟩ : C) * ⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩) := by rw [hcomm]
      _ = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ * (⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩ *
            ⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩) := by
          have h := mul_mul_mul_comm (⟨d, hdC⟩ : C) ⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩
            ⟨d, hdC⟩ ⟨zS D α θ δ, hBC (zS_mem D α θ δ)⟩
          simpa [mul_assoc] using h
      _ = Subgroup.inclusion hBC D.c := by
          rw [show (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ = Subgroup.inclusion hBC D.c from dC_sq D hBC hdC hd2,
            hz, mul_one]
  exact congrArg (Subtype.val) hCeq

end Adjust

section ConjAdj

theorem conj_dAdj {B C : Subgroup S} (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) {d : S} (hdC : d ∈ C) (hm : 1 ≤ m) (α θ δ : ℕ)
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {b : B} (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b) :
    conjBy hgC (⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C) =
      ⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ *
        Subgroup.inclusion hBC (zAdj D α θ δ * b * conjBy hgB (zAdj D α θ δ)) := by
  have hdC' : (⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C) =
      (⟨d, hdC⟩ : C) * Subgroup.inclusion hBC (zAdj D α θ δ) := Subtype.ext rfl
  have hz : Subgroup.inclusion hBC (zAdj D α θ δ) * Subgroup.inclusion hBC (zAdj D α θ δ) = 1 := by
    rw [← map_mul]
    rw [show zAdj D α θ δ * zAdj D α θ δ = 1 from zAdj_sq D hm α θ δ, map_one]
  have hdinv : (⟨d, hdC⟩ : C) = (⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C) *
      Subgroup.inclusion hBC (zAdj D α θ δ) := by
    rw [hdC', mul_assoc, hz, mul_one]
  calc conjBy hgC (⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C)
      = conjBy hgC ((⟨d, hdC⟩ : C) * Subgroup.inclusion hBC (zAdj D α θ δ)) := by rw [hdC']
    _ = conjBy hgC (⟨d, hdC⟩ : C) * conjBy hgC (Subgroup.inclusion hBC (zAdj D α θ δ)) :=
        conjBy_mul hgC _ _
    _ = (⟨d, hdC⟩ * Subgroup.inclusion hBC b) *
        Subgroup.inclusion hBC (conjBy hgB (zAdj D α θ δ)) := by
        rw [hb, conjBy_inclusion hBC hgC hgB]
    _ = ((⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C) *
          Subgroup.inclusion hBC (zAdj D α θ δ)) * Subgroup.inclusion hBC b *
        Subgroup.inclusion hBC (conjBy hgB (zAdj D α θ δ)) := by rw [hdinv]
    _ = (⟨dAdj D d α θ δ, dAdj_mem D hBC hdC α θ δ⟩ : C) *
          Subgroup.inclusion hBC (zAdj D α θ δ * b * conjBy hgB (zAdj D α θ δ)) := by
        rw [map_mul, map_mul]
        group

end ConjAdj

theorem gens_eq_of_dvd {k : Fin 3 → ℕ} {a b c a' b' c' : ℤ}
    (h0 : ((2 : ℤ) ^ k 0) ∣ (a - a')) (h1 : ((2 : ℤ) ^ k 1) ∣ (b - b'))
    (h2 : ((2 : ℤ) ^ k 2) ∣ (c - c')) :
    a • gen k 0 + b • gen k 1 + c • gen k 2 = a' • gen k 0 + b' • gen k 1 + c' • gen k 2 := by
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    simpa using dvd_neg.mpr h0
  · rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    simpa using dvd_neg.mpr h1
  · rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    simpa using dvd_neg.mpr h2

theorem gens_eq_of_mul {k : Fin 3 → ℕ} {a b c a' b' c' : ℤ} {t0 t1 t2 : ℤ}
    (h0 : a - a' = (2 : ℤ) ^ k 0 * t0) (h1 : b - b' = (2 : ℤ) ^ k 1 * t1)
    (h2 : c - c' = (2 : ℤ) ^ k 2 * t2) :
    a • gen k 0 + b • gen k 1 + c • gen k 2 = a' • gen k 0 + b' • gen k 1 + c' • gen k 2 :=
  gens_eq_of_dvd ⟨t0, h0⟩ ⟨t1, h1⟩ ⟨t2, h2⟩

section CocycleAdj

variable {B C : Subgroup S} {m : ℕ}

noncomputable def bU' (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (α θ δ : ℕ) : B :=
  zAdj D α θ δ * bU D hBC hrel hdC hdB hL * conjBy D.u_mem (zAdj D α θ δ)

noncomputable def bT' (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (α θ δ : ℕ) : B :=
  zAdj D α θ δ * bT D hBC hrel hdC hdB hL * conjBy D.t_mem (zAdj D α θ δ)

noncomputable def bR' (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (α θ δ : ℕ) : B :=
  zAdj D α θ δ * bR D hBC hrel hdC hdB hL * conjBy D.ρ_mem (zAdj D α θ δ)

noncomputable def bUV' (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (α θ δ : ℕ) : B :=
  zAdj D α θ δ * bUV D hBC hrel hdC hdB hL * conjBy D.uv_mem (zAdj D α θ δ)

theorem ec_bU' (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) (α θ δ ε : ℕ) (hε : ε ≤ 1)
    (hX : xU D hBC hrel hdC hdB hL = ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t100 m).k 0 +
      ((δ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((δ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2) :
    D.ec (bU' D hBC hrel hdC hdB hL α θ δ) =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (StrothTypeIndex.t100 m).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 +
        (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [xU] at hX
  rw [bU', D.ec_mul, D.ec_mul, ec_conj_u, ec_zAdj, Φu_apply_gens, hX, gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (α : ℤ)) (t1 := (θ : ℤ)) (t2 := (θ : ℤ)) ?_ ?_ ?_
  · rw [t100k_zero]
    have h2m : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := two_pow_succ_int hm
    linear_combination (α : ℤ) * h2m
  · rw [t100k_one]
    have h2m : 2 * (2 : ℤ) ^ m = 2 ^ (m + 1) := two_mul_two_pow_int m
    linear_combination (θ : ℤ) * h2m
  · rw [t100k_two]
    have h2m : 2 * (2 : ℤ) ^ m = 2 ^ (m + 1) := two_mul_two_pow_int m
    linear_combination (θ : ℤ) * h2m

theorem ec_bT' (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) (α θ δ ε q : ℕ) (hq : q = ε)
    (hY : yT D hBC hrel hdC hdB hL = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      ((1 : ℤ) + (α : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((q : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2) :
    D.ec (bT' D hBC hrel hdC hdB hL α θ δ) =
      (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
        (1 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 +
        ((ε : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [yT] at hY
  rw [bT', D.ec_mul, D.ec_mul, ec_conj_t, ec_zAdj, Φt_apply_gens, hY, gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (α : ℤ) - 2 * ((θ : ℤ) - (δ : ℤ)))
    (t1 := (α : ℤ) - ((θ : ℤ) - (δ : ℤ))) (t2 := 0) ?_ ?_ ?_
  · rw [t100k_zero]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring
  · rw [t100k_one]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring
  · rw [t100k_two, hq]
    ring

theorem ec_bR' (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) (α θ δ η : ℕ) (hη : η = δ)
    (hZ : zR D hBC hrel hdC hdB hL = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      ((η : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((θ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2) :
    D.ec (bR' D hBC hrel hdC hdB hL α θ δ) =
      (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
        (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 +
        (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [zR] at hZ
  rw [bR', D.ec_mul, D.ec_mul, ec_conj_ρ, ec_zAdj, Φρ_apply_gens, hZ, gens_add, gens_add]
  refine gens_eq_of_mul (t0 := (α : ℤ) - 2 * ((θ : ℤ) - (δ : ℤ)))
    (t1 := (δ : ℤ)) (t2 := (θ : ℤ)) ?_ ?_ ?_
  · rw [t100k_zero]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring
  · rw [t100k_one, hη]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring
  · rw [t100k_two]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring

theorem ec_bUV' (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) (α θ δ ε q η : ℕ)
    (hq : q = ε) (hη : η = δ)
    (hY : yT D hBC hrel hdC hdB hL = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      ((1 : ℤ) + (α : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((q : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2)
    (hZ : zR D hBC hrel hdC hdB hL = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      ((η : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 1 +
      ((θ : ℤ) * 2 ^ m) • gen (StrothTypeIndex.t100 m).k 2) :
    D.ec (bUV' D hBC hrel hdC hdB hL α θ δ) =
      (-3 * (α : ℤ) * 2 ^ m - 2) • gen (StrothTypeIndex.t100 m).k 0 +
        ((ε : ℤ) * 2 ^ m - 1) • gen (StrothTypeIndex.t100 m).k 1 +
        (-1 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [yT] at hY
  rw [zR] at hZ
  rw [bUV', D.ec_mul, D.ec_mul, ec_conj_uv, ec_zAdj, Φuv_apply_gens]
  rw [show D.ec (bUV D hBC hrel hdC hdB hL) = wUV D hBC hrel hdC hdB hL from rfl, wUV_form,
    yT, zR, hY, hZ]
  rw [Φt_apply_gens]
  simp only [sub_eq_add_neg, neg_gens]
  rw [gens_add, gens_add]
  rw [Φρ_apply_gens, Φρ_apply_gens]
  simp only [gens_add]
  refine gens_eq_of_mul (t0 := 6 * (θ : ℤ) + 2 * (δ : ℤ)) (t1 := 2 * (θ : ℤ) - (α : ℤ))
    (t2 := 3 * (θ : ℤ) - (α : ℤ)) ?_ ?_ ?_
  · rw [t100k_zero, hη]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring
  · rw [t100k_one, hq, hη]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring
  · rw [t100k_two, hη]
    obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    try simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
    rw [pow_succ]
    ring

end CocycleAdj



section Images

variable {B C : Subgroup S} {m : ℕ}

theorem E_image_d (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S)) (E : TorusBasisEquiv D hBC d hdC)
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {b : B} (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    {i j l : ℤ} (h : D.ec b = i • gen (StrothTypeIndex.t100 m).k 0 +
      j • gen (StrothTypeIndex.t100 m).k 1 + l • gen (StrothTypeIndex.t100 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨d, hdC⟩ : C))) =
      (1 + 2 * i) • gen (Type300.k (m + 1)) 0 +
        j • gen (Type300.k (m + 1)) 1 + l • gen (Type300.k (m + 1)) 2 := by
  rw [hb, ofMul_mul, map_add, E.e_d]
  have hsub : Additive.ofMul ((Subgroup.inclusion hBC) b) = Additive.ofMul (⟨b, hBC b.2⟩ : C) :=
    congrArg Additive.ofMul rfl
  rw [hsub, E_e_inclusion (D := D) (hBC := hBC) (hdC := hdC) (hd2 := hd2) (E := E) (β := b) (hβ := h)]
  module

theorem E_image_a (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S)) (E : TorusBasisEquiv D hBC d hdC)
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {i j l : ℤ} (h : D.ec (conjBy hgB D.a) = i • gen (StrothTypeIndex.t100 m).k 0 +
      j • gen (StrothTypeIndex.t100 m).k 1 + l • gen (StrothTypeIndex.t100 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨D.a, hBC D.a.2⟩ : C))) =
      (2 * i) • gen (Type300.k (m + 1)) 0 + j • gen (Type300.k (m + 1)) 1 +
        l • gen (Type300.k (m + 1)) 2 := by
  have hsub : conjBy hgC (⟨D.a, hBC D.a.2⟩ : C) =
      (⟨conjBy hgB D.a, hBC (conjBy hgB D.a).2⟩ : C) := Subtype.ext rfl
  rw [hsub]
  exact E_e_inclusion (D := D) (hBC := hBC) (hdC := hdC) (hd2 := hd2) (E := E) (β := _) (hβ := h)

theorem E_image_b (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S)) (E : TorusBasisEquiv D hBC d hdC)
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {i j l : ℤ} (h : D.ec (conjBy hgB D.b) = i • gen (StrothTypeIndex.t100 m).k 0 +
      j • gen (StrothTypeIndex.t100 m).k 1 + l • gen (StrothTypeIndex.t100 m).k 2) :
    E.e (Additive.ofMul (conjBy hgC (⟨D.b, hBC D.b.2⟩ : C))) =
      (2 * i) • gen (Type300.k (m + 1)) 0 + j • gen (Type300.k (m + 1)) 1 +
        l • gen (Type300.k (m + 1)) 2 := by
  have hsub : conjBy hgC (⟨D.b, hBC D.b.2⟩ : C) =
      (⟨conjBy hgB D.b, hBC (conjBy hgB D.b).2⟩ : C) := Subtype.ext rfl
  rw [hsub]
  exact E_e_inclusion (D := D) (hBC := hBC) (hdC := hdC) (hd2 := hd2) (E := E) (β := _) (hβ := h)

end Images

theorem dvd_six_mul_two_pow (a : ℤ) (m : ℕ) : ((2 : ℤ) ^ (m + 1)) ∣ 6 * a * 2 ^ m :=
  ⟨3 * a, by rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m from (two_mul_two_pow_int m).symm]; ring⟩

section ConjCoords

variable {B C : Subgroup S} {m : ℕ}

theorem ec_conj_a_u (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.u_mem D.a) = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (1 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_u, StrothTypeData.ec_a]
  simpa using Φu_apply_gens (D := D) (m := m) 0 1 0

theorem ec_conj_a_t (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.t_mem D.a) = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (-1 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_t, StrothTypeData.ec_a]
  simpa using Φt_apply_gens (D := D) (m := m) 0 1 0

theorem ec_conj_a_ρ (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.ρ_mem D.a) = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (1 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_ρ, StrothTypeData.ec_a]
  simpa using Φρ_apply_gens (D := D) (m := m) 0 1 0

theorem ec_conj_a_uv (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.uv_mem D.a) = (2 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (1 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (2 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_uv, StrothTypeData.ec_a]
  simpa using Φuv_apply_gens (D := D) (m := m) 0 1 0

theorem ec_conj_b_u (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.u_mem D.b) = (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (1 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (0 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_u, StrothTypeData.ec_b]
  simpa using Φu_apply_gens (D := D) (m := m) 0 0 1

theorem ec_conj_b_t (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.t_mem D.b) = (-2 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (-2 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (-1 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_t, StrothTypeData.ec_b]
  simpa using Φt_apply_gens (D := D) (m := m) 0 0 1

theorem ec_conj_b_ρ (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.ρ_mem D.b) = (-2 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (-1 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (-1 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_ρ, StrothTypeData.ec_b]
  simpa using Φρ_apply_gens (D := D) (m := m) 0 0 1

theorem ec_conj_b_uv (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    D.ec (conjBy D.uv_mem D.b) = (2 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
      (2 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 + (1 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
  rw [ec_conj_uv, StrothTypeData.ec_b]
  simpa using Φuv_apply_gens (D := D) (m := m) 0 0 1

end ConjCoords

section Final

theorem one_le_of_noInvolutionsCentralizing
    {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    1 ≤ m := by
  by_contra hlt
  have hm0 : m = 0 := by omega
  subst hm0
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_of_hasStrothType hB hBC hC hrel hL hH hcS hne
  have hc1 : (hB.data.c : S) = 1 := by
    rw [← orderOf_eq_one_iff]
    have h := hB.data.orderOf_c
    rw [m_t100] at h
    simpa using h
  exact hdB (hH d (hcS hdC) (by rw [hd2, hc1]) (hC hdC))

theorem hasStrothType_t300_or_t310_of_noInvolutionsCentralizing
    {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothType C (StrothTypeIndex.t300 (m + 1)) ∨
    HasStrothType C (StrothTypeIndex.t310 (m + 1)
      (by
        have hm := one_le_of_noInvolutionsCentralizing hB hBC hC hrel hL hH hcS hne
        omega)) := by
  classical
  have hm : 1 ≤ m := one_le_of_noInvolutionsCentralizing hB hBC hC hrel hL hH hcS hne
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_of_hasStrothType hB hBC hC hrel hL hH hcS hne
  obtain ⟨ε, δ, hε1, hδ1, hX⟩ := form_xU hB.data hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨α, q, hα1, hq1, hY⟩ := form_yT hB.data hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨θ, η, hη1, hθ1, hZ⟩ := form_zR hB.data hBC hC hrel hdC hdB hd2 hL hm
  have hqq : q = ε :=
    bit_q (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL)
      hm hq1 hε1 hX hY hZ
  have hee : η = δ :=
    bit_eta (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL)
      hm hδ1 hη1 hX hZ
  let d' : S := dAdj hB.data d α θ δ
  have hd'C : d' ∈ C := dAdj_mem hB.data hBC hdC α θ δ
  have hd'B : d' ∉ B := dAdj_notMem hB.data hm hdB α θ δ
  have hd'2 : d' * d' = (hB.data.c : S) := dAdj_sq hB.data hBC hC hrel hdC hd2 hm α θ δ
  let E : TorusBasisEquiv hB.data hBC d' hd'C :=
    addEquivOfSq hB.data hBC hC hrel hd'C hd'B hd'2
  have hd'C' : d' ∈ C := hd'C
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  rcases hε01 with rfl | rfl
  ·
    left
    refine hasStrothType_t300_of_generator_images hB.data hBC hrel hL hd'C hd'B hd'2 E ?_ ?_ ?_ ?_
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.uv_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.uv_mem_L) hB.data.uv_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.uv_mem_L) hB.data.uv_mem
              (conj_eq_bUV (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bUV' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 0) (q := q) (η := η) (hq := hqq) (hη := hee) (hY := hY) (hZ := hZ)), Type300.uv_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
        refine gens_eq_of_mul (t0 := -3 * (α : ℤ)) (t1 := 0) (t2 := 0) ?_ ?_ ?_
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 0) = 2 ^ (m + 1) by simp [Type300.k]]
          linear_combination (3 * (α : ℤ)) * two_mul_two_pow_int m
        · ring
        · ring
      · change E.e (Additive.ofMul (conjBy (hL hB.data.uv_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) =
          (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.uv_mem_L) hB.data.uv_mem
            (ec_conj_a_uv hB.data), Type300.uv_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.uv_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) =
          (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.uv_mem_L) hB.data.uv_mem
            (ec_conj_b_uv hB.data), Type300.uv_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.t_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.t_mem_L) hB.data.t_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.t_mem_L) hB.data.t_mem
              (conj_eq_bT (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bT' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 0) (q := q) (hq := hqq) (hY := hY)), Type300.t_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.t_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) =
          (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.t_mem_L) hB.data.t_mem
            (ec_conj_a_t hB.data), Type300.t_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.t_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) =
          (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.t_mem_L) hB.data.t_mem
            (ec_conj_b_t hB.data), Type300.t_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.u_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.u_mem_L) hB.data.u_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.u_mem_L) hB.data.u_mem
              (conj_eq_bU (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bU' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 0) (hε := by omega) (hX := hX)), Type300.u_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.u_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) =
          (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.u_mem_L) hB.data.u_mem
            (ec_conj_a_u hB.data), Type300.u_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.u_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) =
          (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.u_mem_L) hB.data.u_mem
            (ec_conj_b_u hB.data), Type300.u_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.ρ_mem_L) hB.data.ρ_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.ρ_mem_L) hB.data.ρ_mem
              (conj_eq_bR (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bR' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (η := η) (hη := hee) (hZ := hZ)), Type300.rho_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) =
          (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.ρ_mem_L) hB.data.ρ_mem
            (ec_conj_a_ρ hB.data), Type300.rho_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) =
          (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.ρ_mem_L) hB.data.ρ_mem
            (ec_conj_b_ρ hB.data), Type300.rho_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
  ·
    right
    refine hasStrothType_t310_of_generator_images hB.data hBC hrel hL hm hd'C hd'B hd'2 E ?_ ?_ ?_ ?_
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.uv_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.uv_mem_L) hB.data.uv_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.uv_mem_L) hB.data.uv_mem
              (conj_eq_bUV (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bUV' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 1) (q := q) (η := η) (hq := hqq) (hη := hee) (hY := hY) (hZ := hZ))]
        rw [show (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 0) =
            (-3 : ℤ) • gen (Type300.k (m + 1)) 0 + ((2 : ℤ) * 2 ^ (m - 1) - 1) • gen (Type300.k (m + 1)) 1 + (-1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.uv_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, zero_smul]
        refine gens_eq_of_mul (t0 := -3 * (α : ℤ)) (t1 := 0) (t2 := 0) ?_ ?_ ?_
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 0) = 2 ^ (m + 1) by simp [Type300.k]]
          linear_combination (3 * (α : ℤ)) * two_mul_two_pow_int m
        · rw [two_pow_succ_int hm]; ring
        · ring
      · change E.e (Additive.ofMul (conjBy (hL hB.data.uv_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.uv_mem_L) hB.data.uv_mem
            (ec_conj_a_uv hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 1) =
            (4 : ℤ) • gen (Type300.k (m + 1)) 0 + (1 : ℤ) • gen (Type300.k (m + 1)) 1 + (2 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.uv_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.uv_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.uv_mem_L) hB.data.uv_mem
            (ec_conj_b_uv hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 2) =
            ((-32 : ℤ) * 2 ^ (m - 1) + 4) • gen (Type300.k (m + 1)) 0 + ((-8 : ℤ) * 2 ^ (m - 1) + 2) • gen (Type300.k (m + 1)) 1 + ((-8 : ℤ) * 2 ^ (m - 1) + 1) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.uv_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        refine gens_eq_of_mul (t0 := 8) (t1 := 2) (t2 := 2) ?_ ?_ ?_
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 0) = 2 ^ (m + 1) by simp [Type300.k],
              two_pow_succ_eq_four hm]
          ring
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 1) = 2 ^ (m + 1) by simp [Type300.k],
              two_pow_succ_eq_four hm]
          ring
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 2) = 2 ^ (m + 1) by simp [Type300.k],
              two_pow_succ_eq_four hm]
          ring
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.t_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.t_mem_L) hB.data.t_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.t_mem_L) hB.data.t_mem
              (conj_eq_bT (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bT' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 1) (q := q) (hq := hqq) (hY := hY))]
        rw [show (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 0) =
            (1 : ℤ) • gen (Type300.k (m + 1)) 0 + (1 : ℤ) • gen (Type300.k (m + 1)) 1 + ((2 : ℤ) * 2 ^ (m - 1)) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.t_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, zero_smul]
        rw [two_pow_succ_int hm]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.t_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.t_mem_L) hB.data.t_mem
            (ec_conj_a_t hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (-1 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.t_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.t_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.t_mem_L) hB.data.t_mem
            (ec_conj_b_t hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 2) =
            (-4 : ℤ) • gen (Type300.k (m + 1)) 0 + (-2 : ℤ) • gen (Type300.k (m + 1)) 1 + (-1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.t_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.u_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.u_mem_L) hB.data.u_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.u_mem_L) hB.data.u_mem
              (conj_eq_bU (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bU' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 1) (hε := by omega) (hX := hX))]
        rw [show (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 0) =
            ((2 : ℤ) * 2 ^ (m - 1) + 1) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.u_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.u_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.u_mem_L) hB.data.u_mem
            (ec_conj_a_u hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.u_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.u_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.u_mem_L) hB.data.u_mem
            (ec_conj_b_u hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 2) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (1 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.u_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
    ·
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := hB.data) hBC hd'C hd'2 E (hL hB.data.ρ_mem_L) hB.data.ρ_mem
            (conj_dAdj (D := hB.data) hBC hdC hm α θ δ (hL hB.data.ρ_mem_L) hB.data.ρ_mem
              (conj_eq_bR (D := hB.data) hBC hrel hdC hdB hL))
            (ec_bR' (D := hB.data) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (η := η) (hη := hee) (hZ := hZ))]
        rw [show (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 0) =
            (1 : ℤ) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.rho_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) (⟨hB.data.a, hBC hB.data.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := hB.data) hBC hd'C hd'2 E (hL hB.data.ρ_mem_L) hB.data.ρ_mem
            (ec_conj_a_ρ hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.rho_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL hB.data.ρ_mem_L) (⟨hB.data.b, hBC hB.data.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := hB.data) hBC hd'C hd'2 E (hL hB.data.ρ_mem_L) hB.data.ρ_mem
            (ec_conj_b_ρ hB.data)]
        rw [show (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 2) =
            (-4 : ℤ) • gen (Type300.k (m + 1)) 0 + (-1 : ℤ) • gen (Type300.k (m + 1)) 1 + (-1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.rho_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module

end Final

end CFSG.CGT.Stroth77
