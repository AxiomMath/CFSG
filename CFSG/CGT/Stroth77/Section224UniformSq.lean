module

public import CFSG.CGT.Stroth77.Section224Uniform
public import CFSG.CGT.Stroth77.Section33

public section

namespace CFSG.CGT.Stroth77

open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem familyOne_disjunction (τ : StrothTypeIndex) (hrel : τ.m + 1 = τ.n) :
    (∃ m : ℕ, τ = StrothTypeIndex.t100 m) ∨
    (∃ n : ℕ, τ = StrothTypeIndex.t101 n) ∨
    (∃ t : ℕ, τ = StrothTypeIndex.t110 t) ∨
    (∃ t : ℕ, τ = StrothTypeIndex.t111 t) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t120 m hm) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t121 m hm) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t130 m hm) ∨
    (∃ (m : ℕ) (hm : 3 ≤ m), τ = StrothTypeIndex.t131 m hm) := by
  cases τ with
  | t100 m => exact Or.inl ⟨m, rfl⟩
  | t101 s => exact Or.inr (Or.inl ⟨s, rfl⟩)
  | t110 t => exact Or.inr (Or.inr (Or.inl ⟨t, rfl⟩))
  | t111 t => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, rfl⟩)))
  | t120 m hm =>
    right; right; right; right; left
    exact ⟨m, hm, rfl⟩
  | t121 m hm =>
    right; right; right; right; right; left
    exact ⟨m, hm, rfl⟩
  | t130 m hm =>
    right; right; right; right; right; right; left
    exact ⟨m, hm, rfl⟩
  | t131 m hm =>
    right; right; right; right; right; right; right
    exact ⟨m, hm, rfl⟩
  | t200 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type200.k] at hrel
  | t201 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type201.k] at hrel
  | t210 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type210.k] at hrel
  | t211 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type211.k] at hrel
  | t220 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type220.k] at hrel
  | t221 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type221.k] at hrel
  | t230 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type230.k] at hrel
  | t231 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type231.k] at hrel
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel

theorem thetaType_ofInt_of_hrel (τ : StrothTypeIndex) (hrel : τ.m + 1 = τ.n)
    (v : Fin 3 → ℤ) :
    thetaType τ (Torus.ofInt τ.k v) =
      Torus.ofInt τ.k (thetaM τ.m *ᵥ v) := by
  cases τ with
  | t100 m => exact theta_ofInt m v
  | t101 s => exact theta_ofInt (s + 1) v
  | t110 t => exact theta_ofInt (t + 2) v
  | t111 t => exact theta_ofInt (t + 2) v
  | t120 m hm => exact theta_ofInt m v
  | t121 m hm => exact theta_ofInt m v
  | t130 m hm => exact theta_ofInt m v
  | t131 m hm => exact theta_ofInt m v
  | t200 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type200.k] at hrel
  | t201 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type201.k] at hrel
  | t210 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type210.k] at hrel
  | t211 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type211.k] at hrel
  | t220 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type220.k] at hrel
  | t221 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type221.k] at hrel
  | t230 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type230.k] at hrel
  | t231 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type231.k] at hrel
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel


theorem thetaD_torus_eq_familyOne (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ∀ d : Z.D,
      Z.dataD.e (Additive.ofMul (thetaD Z s (hF hsF) d)) =
        thetaType Z.τ (Z.dataD.e (Additive.ofMul d)) := by
  classical
  have hs : s ∈ Z.centralizerInMho := hF hsF
  have hfam := familyOne_disjunction Z.τ hrel
  obtain ⟨hφc, hφa, hφb, hφsq⟩ :=
    deviation_form_diag_familyOne_all Z hk hrel F hDF hF hN hidx hcent hsF hsD hfam
  have hΦc : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩) = 0 := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul.2⟩ : Z.D) = 1 :=
      Subtype.ext hφc
    rw [h1]
    simp
  have hΦa : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) =
      (2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k) := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul.2⟩ : Z.D) =
        Z.dataD.a ^ (2 ^ Z.τ.m) := Subtype.ext hφa
    rw [h1, Z.dataD.e_pow, Z.dataD.e_a]
    rw [show ((2 : ℕ) ^ Z.τ.m) • (Torus.a : Torus Z.τ.k) =
        ((2 : ℤ) ^ Z.τ.m) • Torus.a from by
      rw [← natCast_zsmul]
      norm_num]
  have hΦb : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
      (2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k) := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul.2⟩ : Z.D) =
        Z.dataD.b ^ (2 ^ Z.τ.m) := Subtype.ext hφb
    rw [h1, Z.dataD.e_pow, Z.dataD.e_b]
    rw [show ((2 : ℕ) ^ Z.τ.m) • (Torus.b : Torus Z.τ.k) =
        ((2 : ℤ) ^ Z.τ.m) • Torus.b from by
      rw [← natCast_zsmul]
      norm_num]
  intro d
  obtain ⟨i, j, l, hd⟩ := ofMul_eq_gens_zsmul Z d
  have hV : Z.dataD.e (Additive.ofMul d) =
      i • (Torus.c : Torus Z.τ.k) + j • (Torus.a : Torus Z.τ.k) +
        l • (Torus.b : Torus Z.τ.k) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      Z.dataD.e_c, Z.dataD.e_a, Z.dataD.e_b]
  have hΦd : deviationTorus Z s hs (Additive.ofMul d) =
      j • ((2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k)) +
        l • ((2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k)) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hΦc, hΦa, hΦb]
    simp
  have hLHS := thetaD_additive_torus Z s hs d
  rw [hLHS, hV, hΦd]
  have hVof : i • (Torus.c : Torus Z.τ.k) + j • (Torus.a : Torus Z.τ.k) +
      l • (Torus.b : Torus Z.τ.k) = Torus.ofInt Z.τ.k ![i, j, l] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp
  rw [hVof, thetaType_ofInt_of_hrel Z.τ hrel]
  have hthetaM : thetaM Z.τ.m *ᵥ (![i, j, l] : Fin 3 → ℤ) =
      ![2 * i, (2 + (2 : ℤ) ^ Z.τ.m) * j, (2 + (2 : ℤ) ^ Z.τ.m) * l] := by
    rw [thetaM]
    funext r
    rw [Matrix.mulVec_diagonal]
    fin_cases r <;> simp
  rw [hthetaM]
  have hEq : (2 : ℤ) • (Torus.ofInt Z.τ.k ![i, j, l] :
        Torus Z.τ.k) +
      (j • ((2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k)) +
        l • ((2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k))) =
      Torus.ofInt Z.τ.k
        ![2 * i, (2 + (2 : ℤ) ^ Z.τ.m) * j, (2 + (2 : ℤ) ^ Z.τ.m) * l] := by
    funext t
    fin_cases t <;>
      simp [Torus.ofInt_apply, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, gen,
        Pi.single_apply, add_mul, mul_add] <;>
      push_cast <;> ring
  exact hEq


theorem theta_eq_matAct_sub_of_conj_familyOne (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {s l : G} (hs : s ∈ Z.centralizerInMho) (hsqD : s * s ∈ Z.D)
    (hlN : l ∈ Subgroup.normalizer (Z.D : Set G))
    (M : IntMat) (hM : Compat Z.τ.k M)
    (hconj : ∀ d : Z.D, Z.dataD.e (Additive.ofMul (conjBy hlN d)) =
      matAct Z.τ.k M hM (Z.dataD.e (Additive.ofMul d)))
    (hform : ∀ d : Z.D, Z.dataD.e (Additive.ofMul (thetaD Z s hs d)) =
      thetaType Z.τ (Z.dataD.e (Additive.ofMul d)))
    {d : Z.D} (h : l⁻¹ * s * l = s * (d : G)) :
    thetaType Z.τ (Z.dataD.e (Additive.ofMul d)) =
      matAct Z.τ.k M hM (Z.dataD.e (Additive.ofMul ⟨s * s, hsqD⟩)) -
        Z.dataD.e (Additive.ofMul ⟨s * s, hsqD⟩) := by
  let q : Z.D := ⟨s * s, hsqD⟩
  have hconjq : conjBy hlN q = q * thetaD Z s hs d := by
    apply Subtype.ext
    dsimp [conjBy, q]
    rw [show l⁻¹ * (s * s) * l = (l⁻¹ * s * l) * (l⁻¹ * s * l) by group]
    rw [h]
    exact sq_mul_eq_sq_mul_thetaD Z hk hs d.2
  have heq : matAct Z.τ.k M hM (Z.dataD.e (Additive.ofMul q)) =
      Z.dataD.e (Additive.ofMul q) + thetaType Z.τ (Z.dataD.e (Additive.ofMul d)) := by
    calc matAct Z.τ.k M hM (Z.dataD.e (Additive.ofMul q))
        = Z.dataD.e (Additive.ofMul (conjBy hlN q)) := (hconj q).symm
      _ = Z.dataD.e (Additive.ofMul (q * thetaD Z s hs d)) := by rw [hconjq]
      _ = Z.dataD.e (Additive.ofMul q) + Z.dataD.e (Additive.ofMul (thetaD Z s hs d)) := by
        rw [ofMul_mul, map_add]
      _ = Z.dataD.e (Additive.ofMul q) +
          thetaType Z.τ (Z.dataD.e (Additive.ofMul d)) := by rw [hform]
  rw [heq]
  abel


theorem exists_sq_eq_c_of_index_two_of_centOmega_of_familyOne (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) :
    ∃ s ∈ F, s ∉ Z.D ∧ s * s = (Z.dataD.c : G) := by
  classical
  obtain ⟨s0, hs0F, hs0D, hs0sqD⟩ := exists_sq_mem_D_of_index_two Z hk F hF hidx
  have hs : s0 ∈ Z.centralizerInMho := hF hs0F
  have hform := thetaD_torus_eq_familyOne Z hk hrel F hDF hF hN hidx hcent hs0F hs0D
  have huL : Z.dataD.u ∈ X.L := Z.hL ▸ Z.dataD.u_mem_L
  have htL : Z.dataD.t ∈ X.L := Z.hL ▸ Z.dataD.t_mem_L
  have huvL : Z.dataD.uv ∈ X.L := Z.hL ▸ Z.dataD.uv_mem_L
  have hρL : Z.dataD.ρ ∈ X.L := Z.hL ▸ Z.dataD.ρ_mem_L
  obtain ⟨du, hduD, hdu⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hs0F hs0D huL
  obtain ⟨dt, hdtD, hdt⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hs0F hs0D htL
  obtain ⟨duv, hduvD, hduv⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hs0F hs0D huvL
  obtain ⟨dρ, hdρD, hdρ⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hs0F hs0D hρL
  have hmat_uv : ∀ y : Z.D, Z.dataD.e (Additive.ofMul (conjBy Z.dataD.uv_mem y)) =
      matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv
        (Z.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z.dataD.uv_conj]
  have hmat_t : ∀ y : Z.D, Z.dataD.e (Additive.ofMul (conjBy Z.dataD.t_mem y)) =
      matAct Z.τ.k Z.τ.action.t Z.τ.action.compat_t
        (Z.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z.dataD.t_conj]
  have hmat_u : ∀ y : Z.D, Z.dataD.e (Additive.ofMul (conjBy Z.dataD.u_mem y)) =
      matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u
        (Z.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z.dataD.u_conj]
  have hmat_ρ : ∀ y : Z.D, Z.dataD.e (Additive.ofMul (conjBy Z.dataD.ρ_mem y)) =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ
        (Z.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z.dataD.ρ_conj]
  have hcond_uv : ∃ d : Torus Z.τ.k,
      thetaType Z.τ d = matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv
        (Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z.dataD.e (Additive.ofMul ⟨duv, hduvD⟩),
      theta_eq_matAct_sub_of_conj_familyOne Z hk hrel hs hs0sqD Z.dataD.uv_mem
        Z.τ.action.uv Z.τ.action.compat_uv hmat_uv hform
        (d := ⟨duv, hduvD⟩) (by simpa using hduv)⟩
  have hcond_t : ∃ d : Torus Z.τ.k,
      thetaType Z.τ d = matAct Z.τ.k Z.τ.action.t Z.τ.action.compat_t
        (Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z.dataD.e (Additive.ofMul ⟨dt, hdtD⟩),
      theta_eq_matAct_sub_of_conj_familyOne Z hk hrel hs hs0sqD Z.dataD.t_mem
        Z.τ.action.t Z.τ.action.compat_t hmat_t hform
        (d := ⟨dt, hdtD⟩) (by simpa using hdt)⟩
  have hcond_u : ∃ d : Torus Z.τ.k,
      thetaType Z.τ d = matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u
        (Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z.dataD.e (Additive.ofMul ⟨du, hduD⟩),
      theta_eq_matAct_sub_of_conj_familyOne Z hk hrel hs hs0sqD Z.dataD.u_mem
        Z.τ.action.u Z.τ.action.compat_u hmat_u hform
        (d := ⟨du, hduD⟩) (by simpa using hdu)⟩
  have hcond_ρ : ∃ d : Torus Z.τ.k,
      thetaType Z.τ d = matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ
        (Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z.dataD.e (Additive.ofMul ⟨dρ, hdρD⟩),
      theta_eq_matAct_sub_of_conj_familyOne Z hk hrel hs hs0sqD Z.dataD.ρ_mem
        Z.τ.action.ρ Z.τ.action.compat_ρ hmat_ρ hform
        (d := ⟨dρ, hdρD⟩) (by simpa using hdρ)⟩
  have hdich := square_class_dichotomy_uniform Z.τ hk hrel
    (Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) hcond_uv hcond_t hcond_u hcond_ρ
  rcases hdich with ⟨v, hv⟩ | ⟨v, hv⟩
  ·
    exfalso
    obtain ⟨y, hy⟩ := Z.dataD.e.surjective v
    set d : Z.D := Additive.toMul y with hd
    have hed : Z.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z.dataD.e (Additive.ofMul (thetaD Z s0 hs d)) =
        Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) := by
      rw [hform d, hed]
      exact hv
    set d' : Z.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z hk hs (by exact Z.D.inv_mem d.2)).symm
    have he : Z.dataD.e (Additive.ofMul d') = 0 := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd, add_neg_cancel]
    have hz2 : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = 1 := by
      have h1 : d' = 1 := by
        apply Additive.ofMul.injective
        apply Z.dataD.e.injective
        rw [he]
        simp
      rw [← hsq, h1]
      rfl
    have hzS : s0 * (d : G)⁻¹ ∈ (X.S : Subgroup G) :=
      X.S.mul_mem (hF hs0F).1.1 (X.S.inv_mem (Z.hDS d.2))
    have hzA : s0 * (d : G)⁻¹ ∈ Subgroup.centralizer (X.A : Set G) := by
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.centralizer_le (A_le_mhoOne_of_family_one Z hk hrel) hs.2
      · refine Subgroup.mem_centralizer_iff.mpr (fun a ha => ?_)
        have haD : a ∈ Z.D := Z.hAD ha
        have hcomm : a * (d : G) = (d : G) * a :=
          congrArg Subtype.val (Z.dataD.isMulCommutative.is_comm.comm ⟨a, haD⟩ ⟨d, d.2⟩)
        exact (show Commute a (d : G) from hcomm).inv_right.eq
    have hzA' : s0 * (d : G)⁻¹ ∈ X.A := X.hH _ hzS hz2 hzA
    have hzD : s0 * (d : G)⁻¹ ∈ Z.D := Z.hAD hzA'
    exact hs0D (by
      have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
      rw [this]
      exact Z.D.mul_mem hzD d.2)
  ·
    obtain ⟨y, hy⟩ := Z.dataD.e.surjective v
    set d : Z.D := Additive.toMul y with hd
    have hed : Z.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z.dataD.e (Additive.ofMul (thetaD Z s0 hs d)) =
        Z.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) - Torus.c := by
      rw [hform d, hed]
      exact hv
    set d' : Z.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z hk hs (by exact Z.D.inv_mem d.2)).symm
    have he : Z.dataD.e (Additive.ofMul d') =
        Z.dataD.e (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩) := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd,
        Z.dataD.e_c]
      abel
    have hsqc : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = (Z.dataD.c : G) := by
      have h1 : d' = ⟨Z.dataD.c, Z.dataD.c.2⟩ := by
        apply Additive.ofMul.injective
        apply Z.dataD.e.injective
        rw [he]
      rw [← hsq, h1]
    refine ⟨s0 * (d : G)⁻¹, F.mul_mem hs0F (F.inv_mem (hDF d.2)), ?_, hsqc⟩
    intro hmem
    apply hs0D
    have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
    rw [this]
    exact Z.D.mul_mem hmem d.2


theorem closure_deviation_range_eq (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    Subgroup.closure
        (Set.range (fun d : Z.D =>
          ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G))) =
      Subgroup.closure
        ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m), (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G) := by
  classical
  obtain ⟨hφc, hφa, hφb, -⟩ :=
    deviation_form_diag_familyOne_all Z hk hrel F hDF hF hN hidx hcent hsF hsD
      (familyOne_disjunction Z.τ hrel)
  let H : Subgroup G :=
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
      (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y ⟨d, rfl⟩
    change ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G) ∈ H
    obtain ⟨i, j, l, hd⟩ := Z.dataD.exists_zpow_c_a_b d
    have hdev_mul : ∀ x y : Z.D,
        ((deviation Z s (hF hsF) (Additive.ofMul (x * y))).toMul : G) =
          ((deviation Z s (hF hsF) (Additive.ofMul x)).toMul : G) *
            ((deviation Z s (hF hsF) (Additive.ofMul y)).toMul : G) := by
      intro x y
      rw [ofMul_mul, map_add, toMul_add]
      rfl
    have hdev_zpow : ∀ (x : Z.D) (z : ℤ),
        ((deviation Z s (hF hsF) (Additive.ofMul (x ^ z))).toMul : G) =
          ((deviation Z s (hF hsF) (Additive.ofMul x)).toMul : G) ^ z := by
      intro x z
      rw [ofMul_zpow, map_zsmul, toMul_zsmul]
      rfl
    have hy : ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G) =
        ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) ^ i *
          ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) ^ j *
            ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) ^ l := by
      conv_lhs => rw [hd]
      rw [hdev_mul, hdev_mul, hdev_zpow, hdev_zpow, hdev_zpow]
    rw [hy, hφa, hφb, hφc]
    have haH : (Z.dataD.a : G) ^ (2 ^ Z.τ.m) ∈ H :=
      Subgroup.subset_closure (by simp [H])
    have hbH : (Z.dataD.b : G) ^ (2 ^ Z.τ.m) ∈ H :=
      Subgroup.subset_closure (by simp [H])
    simpa using H.mul_mem (H.mul_mem (H.one_mem) (H.zpow_mem haH j)) (H.zpow_mem hbH l)
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure ⟨⟨Z.dataD.a, Z.dataD.a.2⟩, hφa⟩
    · exact Subgroup.subset_closure ⟨⟨Z.dataD.b, Z.dataD.b.2⟩, hφb⟩

theorem commutator_zpow_eq_zpow {s d : G} (hcomm : Commute s ⁅s, d⁆) (n : ℤ) :
    ⁅s ^ n, d⁆ = ⁅s, d⁆ ^ n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using (Commute.commutatorElement_pow_left hcomm k).symm
  · have hpos : ⁅s ^ k, d⁆ = ⁅s, d⁆ ^ k := by
      simpa using (Commute.commutatorElement_pow_left hcomm k).symm
    have hcommk : Commute (s ^ k) ⁅s ^ k, d⁆ := by
      rw [hpos]
      exact (hcomm.pow_left k).pow_right k
    have hinv : ⁅(s ^ k)⁻¹, d⁆ = (⁅s ^ k, d⁆)⁻¹ := by
      rw [commutatorElement_inv_left]
      rw [show ⁅d, s ^ k⁆ = (⁅s ^ k, d⁆)⁻¹ from (commutatorElement_inv (s ^ k) d).symm]
      have hx : Commute (s ^ k) (⁅s ^ k, d⁆)⁻¹ := hcommk.inv_right
      calc (s ^ k)⁻¹ * (⁅s ^ k, d⁆)⁻¹ * s ^ k
          = (s ^ k)⁻¹ * ((⁅s ^ k, d⁆)⁻¹ * s ^ k) := by group
        _ = (s ^ k)⁻¹ * (s ^ k * (⁅s ^ k, d⁆)⁻¹) := by rw [← hx.eq]
        _ = (⁅s ^ k, d⁆)⁻¹ := by group
    rw [show s ^ (-(k : ℤ)) = (s ^ k)⁻¹ from by
      rw [_root_.zpow_neg, _root_.zpow_natCast]]
    rw [show (⁅s, d⁆ : G) ^ (-(k : ℤ)) = ((⁅s, d⁆ : G) ^ k)⁻¹ from by
      rw [_root_.zpow_neg, _root_.zpow_natCast]]
    rw [hinv, hpos]

theorem commutator_zpowers_le_of_image {s : G} {D H : Subgroup G}
    (himg : ∀ d ∈ D, ⁅s, d⁆ ∈ H)
    (hcomm : ∀ d ∈ D, Commute s ⁅s, d⁆) :
    ⁅Subgroup.zpowers s, D⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g hg d hd
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [commutator_zpow_eq_zpow (hcomm d hd) n]
  exact H.zpow_mem (himg d hd) n


theorem commutator_zpowers_s_eq (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ⁅Subgroup.zpowers s, Z.D⁆ =
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
        (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G) := by
  classical
  let H : Subgroup G :=
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
      (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G)
  have hH : Subgroup.closure
      (Set.range (fun d : Z.D =>
        ((deviation Z s (hF hsF) (Additive.ofMul d)).toMul : G))) = H :=
    closure_deviation_range_eq Z hk hrel F hDF hF hN hidx hcent hsF hsD
  apply le_antisymm
  · have himg : ∀ d ∈ Z.D, ⁅s, d⁆ ∈ H := by
      intro d hd
      have hdval : ((deviation Z s (hF hsF) (Additive.ofMul ⟨d, hd⟩)).toMul : G) = ⁅s, d⁆ := by
        rw [deviation_apply]
        rfl
      rw [← hdval, ← hH]
      exact Subgroup.subset_closure ⟨⟨d, hd⟩, rfl⟩
    have hcomm : ∀ d ∈ Z.D, Commute s ⁅s, d⁆ := by
      intro d hd
      have hmem : ⁅s, d⁆ ∈ omegaIn 1 Z.D := by
        have h := commutator_mem_omegaIn_one_of_mem_centralizerInMho (Z := Z) (x := s) (hF hsF) hd
        simpa [commutatorElement_def] using h
      have hmho : ⁅s, d⁆ ∈ mhoOne Z.D := omegaIn_one_le_mhoOne_of_two_le_k Z hk hmem
      exact (Subgroup.mem_centralizer_iff.mp (hF hsF).2 _ hmho).symm
    exact commutator_zpowers_le_of_image himg hcomm
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    obtain ⟨hφc, hφa, hφb, -⟩ :=
      deviation_form_diag_familyOne_all Z hk hrel F hDF hF hN hidx hcent hsF hsD
        (familyOne_disjunction Z.τ hrel)
    rcases hy with rfl | rfl
    · rw [← hφa]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) Z.dataD.a.2
    · rw [← hφb]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) Z.dataD.b.2


theorem map_rho_sub_omegaOne_familyOne (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    AddSubgroup.map
        (matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ - AddMonoidHom.id (Torus Z.τ.k))
        (AddSubgroup.closure ({(2 : ℤ) • (Torus.c : Torus Z.τ.k),
          (2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k),
          (2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k)} : Set (Torus Z.τ.k))) =
      AddSubgroup.closure ({(2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k),
        (2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k)} : Set (Torus Z.τ.k)) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  rcases familyOne_disjunction τ hrel with
    ⟨m, hτ⟩ | ⟨n, hτ⟩ | ⟨t, hτ⟩ | ⟨t, hτ⟩ | ⟨m, hm, hτ⟩ | ⟨m, hm, hτ⟩ |
      ⟨m, hm, hτ⟩ | ⟨m, hm, hτ⟩
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type100.k] using hk 0
    have h := map_rho_sub_omegaOne m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ n + 1 := by simpa [StrothTypeIndex.k, Type101.k] using hk 0
    have h := map_rho_sub_omegaOne (n + 1) hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ t + 2 := by simpa [StrothTypeIndex.k, Type110.k] using hk 0
    have h := map_rho_sub_omegaOne (t + 2) hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ t + 2 := by simpa [StrothTypeIndex.k, Type111.k] using hk 0
    have h := map_rho_sub_omegaOne (t + 2) hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type120.k] using hk 0
    have h := map_rho_sub_omegaOne m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type121.k] using hk 0
    have h := map_rho_sub_omegaOne m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type130.k] using hk 0
    have h := map_rho_sub_omegaOne m hm2
    convert h using 2 <;> rfl
  · subst hτ
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type131.k] using hk 0
    have h := map_rho_sub_omegaOne m hm2
    convert h using 2 <;> rfl


theorem phi_rho_sq_sub_ofInt (Z : StrothDatum X) (hrel : Z.τ.m + 1 = Z.τ.n)
    (v : Fin 3 → ℤ) :
    Z.τ.action.φρ (Z.τ.action.φρ (Torus.ofInt Z.τ.k v)) - Torus.ofInt Z.τ.k v =
      Torus.ofInt Z.τ.k
        (fun i => (Type100.ρM *ᵥ (Type100.ρM *ᵥ v) - v) i) := by
  rw [show Z.τ.action.φρ =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ from rfl]
  rw [matAct_ofInt, matAct_ofInt]
  rw [show Z.τ.action.ρ = Type100.ρM from action_rho_eq_type100 Z.τ hrel]
  rw [← Torus.ofInt_sub]

theorem e_commutator_rho (Z : StrothDatum X) (x : Z.D) :
    Z.dataD.e (Additive.ofMul
        (conjBy (Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G))
      Z.dataD.ρ_mem) x * x⁻¹)) =
      (Z.τ.action.φρ - AddMonoidHom.id (Torus Z.τ.k))
        (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))))) := by
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hconj : conjBy Z.dataD.ρ_mem (conjBy hρinv x) = x := by
    apply Subtype.ext
    simp only [conjBy, Subtype.coe_mk]
    group
  have h1 : Z.τ.action.φρ (Z.dataD.e (Additive.ofMul
        (conjBy hρinv x))) =
      Z.dataD.e (Additive.ofMul x) := by
    rw [← Z.dataD.ρ_conj]
    rw [hconj]
  have h2 : Z.dataD.e (Additive.ofMul
        (conjBy hρinv x)) =
      Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))) := by
    have h3 : Z.τ.action.φρ (Z.τ.action.φρ (Z.τ.action.φρ
          (Z.dataD.e (Additive.ofMul
            (conjBy hρinv x))))) =
        Z.dataD.e (Additive.ofMul
          (conjBy hρinv x)) := by
      have := DFunLike.congr_fun Z.τ.action.rels.rho_cube
        (Z.dataD.e (Additive.ofMul
          (conjBy hρinv x)))
      simpa using this
    calc Z.dataD.e (Additive.ofMul
          (conjBy hρinv x))
        = Z.τ.action.φρ (Z.τ.action.φρ (Z.τ.action.φρ
            (Z.dataD.e (Additive.ofMul
              (conjBy hρinv x))))) := h3.symm
      _ = Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))) := by rw [h1]
  rw [ofMul_mul, map_add, h2, ofMul_inv, map_neg]
  rw [sub_eq_add_neg]
  rw [show Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))) +
      -Z.dataD.e (Additive.ofMul x) =
      (Z.τ.action.φρ + -AddMonoidHom.id (Torus Z.τ.k))
        (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul x))))) from by
    rw [AddMonoidHom.add_apply, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, map_neg]
    have hcube := DFunLike.congr_fun Z.τ.action.rels.rho_cube
      (Z.dataD.e (Additive.ofMul x))
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
    rw [hcube]
    abel]


theorem phi_rho_sq_sub_two_torsion (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) (ε : Fin 3 → ℤ)
    (hε : ∀ i, ε i = 0 ∨ ε i = 1) :
    Z.τ.action.φρ (Z.τ.action.φρ
        (Torus.ofInt Z.τ.k (fun i => ε i * 2 ^ (Z.τ.k i - 1)))) -
        Torus.ofInt Z.τ.k (fun i => ε i * 2 ^ (Z.τ.k i - 1)) =
      Torus.ofInt Z.τ.k
        ![0, (ε 2 - 2 * ε 1) * (2 : ℤ) ^ Z.τ.m,
          -(ε 1 + ε 2) * (2 : ℤ) ^ Z.τ.m] := by
  have hk1 : Z.τ.k 1 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_eq]
    simp [hrel]
  have hk2 : Z.τ.k 2 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_two, hrel]
  set v : Fin 3 → ℤ := fun i => ε i * 2 ^ (Z.τ.k i - 1) with hv
  rw [phi_rho_sq_sub_ofInt Z hrel v]
  have hvec : (fun i => (Type100.ρM *ᵥ (Type100.ρM *ᵥ v) - v) i) =
      ![-2 * (ε 1 * (2 : ℤ) ^ Z.τ.m),
        -2 * (ε 1 * (2 : ℤ) ^ Z.τ.m) + ε 2 * (2 : ℤ) ^ Z.τ.m,
        -ε 1 * (2 : ℤ) ^ Z.τ.m - ε 2 * (2 : ℤ) ^ Z.τ.m] := by
    funext i
    fin_cases i <;>
      simp [v, hk1, hk2, type100_rhoM_mulVec, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] <;>
      ring
  rw [hvec]
  apply Torus.ofInt_eq_ofInt_iff.mpr
  intro i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · rw [Int.modEq_zero_iff_dvd]
    refine ⟨-2 * ε 1, ?_⟩
    change -2 * (ε 1 * (2 : ℤ) ^ Z.τ.m) = (2 : ℤ) ^ Z.τ.m * (-2 * ε 1)
    ring
  · rw [show -2 * (ε 1 * (2 : ℤ) ^ Z.τ.m) + ε 2 * (2 : ℤ) ^ Z.τ.m =
        (ε 2 - 2 * ε 1) * (2 : ℤ) ^ Z.τ.m by ring]
  · rw [show -ε 1 * (2 : ℤ) ^ Z.τ.m - ε 2 * (2 : ℤ) ^ Z.τ.m =
        -(ε 1 + ε 2) * (2 : ℤ) ^ Z.τ.m by ring]
    exact Int.ModEq.refl _






theorem rho_commutator_mem_closure (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    {x : G} (hx : x ∈ omegaIn 1 Z.D) :
    ⁅(Z.dataD.ρ : G), x⁆ ∈
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
        (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G) := by
  classical
  let H : Subgroup G :=
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
      (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G)
  let W : AddSubgroup (Torus Z.τ.k) :=
    AddSubgroup.closure ({(2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k),
      (2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k)} : Set (Torus Z.τ.k))
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hxD, hx2⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hx
  let d : Z.D := ⟨x, hxD⟩
  have hd2 : d * d = 1 := by
    apply Subtype.ext
    simpa [d, pow_two] using hx2
  have h2 : (2 : ℤ) • Z.dataD.e (Additive.ofMul d) = 0 := by
    rw [show (2 : ℤ) • Z.dataD.e (Additive.ofMul d) =
        Z.dataD.e (Additive.ofMul (d * d)) from by
      rw [ofMul_mul, map_add, two_zsmul]]
    rw [hd2, ofMul_one, map_zero]
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  obtain ⟨ε, hε, hεd⟩ := (Torus.two_zsmul_eq_zero_iff hk1all _).mp h2
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hρinv_val : ((conjBy hρinv d * d⁻¹ : Z.D) : G) = ⁅(Z.dataD.ρ : G), x⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjBy, Subtype.coe_mk,
      commutatorElement_def]
    simp only [d, Subtype.coe_mk]
    group
  have hcube := DFunLike.congr_fun Z.τ.action.rels.rho_cube
    (Z.dataD.e (Additive.ofMul d))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
  have heq : Z.dataD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) =
      Torus.ofInt Z.τ.k
        ![0, (ε 2 - 2 * ε 1) * (2 : ℤ) ^ Z.τ.m,
          -(ε 1 + ε 2) * (2 : ℤ) ^ Z.τ.m] := by
    rw [e_commutator_rho]
    rw [show (Z.τ.action.φρ - AddMonoidHom.id (Torus Z.τ.k))
        (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul d))))) =
        (Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul d))) -
          Z.dataD.e (Additive.ofMul d)) from by
      rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_neg]
      rw [hcube]
      abel]
    rw [hεd]
    exact phi_rho_sq_sub_two_torsion Z hk hrel ε hε
  have hW : Z.dataD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) ∈ W := by
    rw [heq]
    refine AddSubgroup.mem_closure_pair.mpr
      ⟨ε 2 - 2 * ε 1, -(ε 1 + ε 2), ?_⟩
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add]
    rw [show (ε 2 - 2 * ε 1) • ((2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k)) =
        ((ε 2 - 2 * ε 1) * (2 : ℤ) ^ Z.τ.m) • Torus.a from by
      rw [← mul_zsmul']; ring]
    rw [show (-(ε 1 + ε 2)) • ((2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k)) =
        (-(ε 1 + ε 2) * (2 : ℤ) ^ Z.τ.m) • Torus.b from by
      rw [← mul_zsmul']; ring]
  have hmem : ⁅(Z.dataD.ρ : G), x⁆ ∈ H := by
    rw [← hρinv_val]
    obtain ⟨p, q, hpq⟩ := AddSubgroup.mem_closure_pair.mp hW
    set g : Z.D := ((⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ Z.τ.m)) ^ p *
        ((⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ ((2 : ℕ) ^ Z.τ.m)) ^ q with hg_def
    have hg_e : Z.dataD.e (Additive.ofMul g) =
        p • ((2 : ℤ) ^ Z.τ.m • (Torus.a : Torus Z.τ.k)) +
          q • ((2 : ℤ) ^ Z.τ.m • (Torus.b : Torus Z.τ.k)) := by
      rw [hg_def, ofMul_mul, map_add, ofMul_zpow, ofMul_zpow, map_zsmul, map_zsmul]
      rw [Z.dataD.e_pow, Z.dataD.e_pow, Z.dataD.e_a, Z.dataD.e_b]
      rw [show ((2 : ℕ) ^ Z.τ.m) • (Torus.a : Torus Z.τ.k) =
          ((2 : ℤ) ^ Z.τ.m) • Torus.a from by
        rw [← natCast_zsmul]; push_cast; ring]
      rw [show ((2 : ℕ) ^ Z.τ.m) • (Torus.b : Torus Z.τ.k) =
          ((2 : ℤ) ^ Z.τ.m) • Torus.b from by
        rw [← natCast_zsmul]; push_cast; ring]
    have heq_g : Z.dataD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) =
        Z.dataD.e (Additive.ofMul g) := by rw [hg_e, hpq]
    have hg_eq : (conjBy hρinv d * d⁻¹ : Z.D) = g :=
      Additive.ofMul.injective (Z.dataD.e.injective heq_g)
    rw [hg_eq]
    show (((Z.dataD.a : G) ^ ((2 : ℕ) ^ Z.τ.m)) ^ p *
        ((Z.dataD.b : G) ^ ((2 : ℕ) ^ Z.τ.m)) ^ q) ∈ H
    exact H.mul_mem
      (H.zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) p)
      (H.zpow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) q)
  exact hmem


theorem commutator_zpowers_le_of_pow_three_central {ρ : G} {K H : Subgroup G}
    (hconj : ∀ x ∈ K, ρ * x * ρ⁻¹ ∈ K)
    (h3 : ρ ^ 3 ∈ Subgroup.centralizer (K : Set G))
    (himg : ∀ x ∈ K, ⁅ρ, x⁆ ∈ H) :
    ⁅Subgroup.zpowers ρ, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g hg x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  let q : ℤ := n / 3
  let r : ℤ := n % 3
  have hn : n = 3 * q + r := by
    dsimp [q, r]
    exact (Int.mul_ediv_add_emod n 3).symm
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg n (by norm_num)
  have hr3 : r < 3 := by
    dsimp [r]
    exact Int.emod_lt_of_pos n (by norm_num)
  have hρn : ρ ^ n = (ρ ^ 3) ^ q * ρ ^ r := by
    rw [hn, _root_.zpow_add, _root_.zpow_mul]
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from by norm_num, _root_.zpow_natCast]
  rw [hρn, commutatorElement_mul_left_eq_conj_mul]
  have h3q_comm : Commute ((ρ ^ 3) ^ q) x := by
    have h : Commute (ρ ^ 3) x := (Subgroup.mem_centralizer_iff.mp h3 x hx).symm
    exact h.zpow_left q
  have h3q_one : ⁅(ρ ^ 3) ^ q, x⁆ = 1 := h3q_comm.commutator_eq
  rw [h3q_one, mul_one]
  have hrK : ⁅ρ ^ r, x⁆ ∈ K := by
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr with h0 | h1 | h2
    · rw [h0]; simp
    · rw [h1, commutatorElement_def]
      exact K.mul_mem (by simpa using hconj x hx) (K.inv_mem hx)
    · rw [h2, show ρ ^ (2 : ℤ) = ρ * ρ from by norm_num [zpow_natCast, pow_two]]
      rw [commutatorElement_def]
      refine K.mul_mem ?_ (K.inv_mem hx)
      have h1 := hconj (ρ * x * ρ⁻¹) (hconj x hx)
      convert h1 using 1
      group
  have hcommA : Commute ((ρ ^ 3) ^ q) ⁅ρ ^ r, x⁆ := by
    have h : Commute (ρ ^ 3) ⁅ρ ^ r, x⁆ :=
      (Subgroup.mem_centralizer_iff.mp h3 _ hrK).symm
    exact h.zpow_left q
  have hconjA : (ρ ^ 3) ^ q * ⁅ρ ^ r, x⁆ * ((ρ ^ 3) ^ q)⁻¹ = ⁅ρ ^ r, x⁆ := by
    rw [hcommA.eq]
    group
  rw [hconjA]
  have hrH : ⁅ρ ^ r, x⁆ ∈ H := by
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr with h0 | h1 | h2
    · rw [h0]; simp
    · rw [h1]; simpa using himg x hx
    · rw [h2, show ρ ^ (2 : ℤ) = ρ * ρ from by norm_num [zpow_natCast, pow_two]]
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hconj_eq : ρ * ⁅ρ, x⁆ * ρ⁻¹ = ⁅ρ, ρ * x * ρ⁻¹⁆ := by
        rw [conjugate_commutatorElement]
        congr 1 <;> group
      rw [hconj_eq]
      exact H.mul_mem (by simpa using himg _ (hconj x hx)) (by simpa using himg x hx)
  exact hrH


theorem commutator_zpowers_rho_le (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆ ≤
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
        (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G) := by
  apply commutator_zpowers_le_of_pow_three_central
  · intro x hx
    simpa only [inv_inv] using conj_mem_omegaIn_one (inv_mem Z.dataD.ρ_mem) hx
  · exact Subgroup.centralizer_le (omegaIn_le 1 Z.D) Z.dataD.rho_cube_mem
  · intro x hx
    exact rho_commutator_mem_closure Z hk hrel hx




theorem e_commutator_rho_ofInt (Z : StrothDatum X) (hrel : Z.τ.m + 1 = Z.τ.n)
    (v : Fin 3 → ℤ) (y : Z.D)
    (hy : Z.dataD.e (Additive.ofMul y) = Torus.ofInt Z.τ.k v) :
    Z.dataD.e (Additive.ofMul
        (conjBy (Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G))
          Z.dataD.ρ_mem) y * y⁻¹)) =
      Torus.ofInt Z.τ.k
        (fun i => (Type100.ρM *ᵥ (Type100.ρM *ᵥ v) - v) i) := by
  have hcube := DFunLike.congr_fun Z.τ.action.rels.rho_cube
    (Z.dataD.e (Additive.ofMul y))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
  rw [e_commutator_rho]
  rw [show (Z.τ.action.φρ - AddMonoidHom.id (Torus Z.τ.k))
      (-(Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul y))))) =
      (Z.τ.action.φρ (Z.τ.action.φρ (Z.dataD.e (Additive.ofMul y))) -
        Z.dataD.e (Additive.ofMul y)) from by
    rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_neg]
    rw [hcube]
    abel]
  rw [hy, phi_rho_sq_sub_ofInt Z hrel v]


theorem rho_commutator_a_pow (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    ⁅(Z.dataD.ρ : G), (Z.dataD.a : G) ^ (2 ^ Z.τ.m)⁆ =
      ((Z.dataD.b : G)⁻¹) ^ (2 ^ Z.τ.m) := by
  classical
  let ya : Z.D := ⟨(Z.dataD.a : G) ^ (2 ^ Z.τ.m), Z.D.pow_mem Z.dataD.a.2 _⟩
  let bb : Z.D := ((⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D)⁻¹) ^ ((2 : ℕ) ^ Z.τ.m)
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hval : ((conjBy hρinv ya * ya⁻¹ : Z.D) : G) =
      ⁅(Z.dataD.ρ : G), (Z.dataD.a : G) ^ (2 ^ Z.τ.m)⁆ := by
    simp only [conjBy, ya, Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  have hk1 : Z.τ.k 1 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hya : Z.dataD.e (Additive.ofMul ya) =
      Torus.ofInt Z.τ.k (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hya_eq : ya = (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ Z.τ.m) := by
      apply Subtype.ext
      rfl
    rw [hya_eq, Z.dataD.e_pow, Z.dataD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk1, Nat.add_sub_cancel, Torus.a, gen, Pi.single_apply]
    module
  have hbb : Z.dataD.e (Additive.ofMul bb) =
      Torus.ofInt Z.τ.k ![0, 0, -(2 : ℤ) ^ Z.τ.m] := by
    have hbb_eq : bb = ((⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D)⁻¹) ^ ((2 : ℕ) ^ Z.τ.m) := by
      apply Subtype.ext
      rfl
    rw [hbb_eq, Z.dataD.e_pow, ofMul_inv, map_neg, Z.dataD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add,
      Torus.b, gen, Pi.single_apply]
    module
  have heq : Z.dataD.e (Additive.ofMul (conjBy hρinv ya * ya⁻¹)) =
      Z.dataD.e (Additive.ofMul bb) := by
    rw [e_commutator_rho_ofInt Z hrel (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) ya hya, hbb]
    apply Torus.ofInt_eq_ofInt_iff.mpr
    intro i
    fin_cases i
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type100_rhoM_mulVec, hk1,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨-2, ?_⟩
      rw [show Z.τ.k 0 = Z.τ.m from rfl]
      ring
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type100_rhoM_mulVec, hk1,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      exact ⟨-1, by ring⟩
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type100_rhoM_mulVec, hk1,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hEqD : (conjBy hρinv ya * ya⁻¹ : Z.D) = bb :=
    Additive.ofMul.injective (Z.dataD.e.injective heq)
  rw [← hval, hEqD]
  rfl


theorem rho_commutator_ab_pow (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    ⁅(Z.dataD.ρ : G),
        (Z.dataD.a : G) ^ (2 ^ Z.τ.m) * (Z.dataD.b : G) ^ (2 ^ Z.τ.m)⁆ =
      ((Z.dataD.a : G)⁻¹) ^ (2 ^ Z.τ.m) := by
  classical
  let ya : Z.D := ⟨(Z.dataD.a : G) ^ (2 ^ Z.τ.m), Z.D.pow_mem Z.dataD.a.2 _⟩
  let yb : Z.D := ⟨(Z.dataD.b : G) ^ (2 ^ Z.τ.m), Z.D.pow_mem Z.dataD.b.2 _⟩
  let y2 : Z.D := ya * yb
  let aa : Z.D := ((⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)⁻¹) ^ ((2 : ℕ) ^ Z.τ.m)
  let hρinv : Z.dataD.ρ⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (Z.D : Set G)) Z.dataD.ρ_mem
  have hval : ((conjBy hρinv y2 * y2⁻¹ : Z.D) : G) =
      ⁅(Z.dataD.ρ : G),
        (Z.dataD.a : G) ^ (2 ^ Z.τ.m) * (Z.dataD.b : G) ^ (2 ^ Z.τ.m)⁆ := by
    simp only [conjBy, y2, ya, yb, Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  have hk1 : Z.τ.k 1 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk2 : Z.τ.k 2 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hy2 : Z.dataD.e (Additive.ofMul y2) =
      Torus.ofInt Z.τ.k (fun i => (![0, 1, 1] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hya_eq : ya = (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ Z.τ.m) := by
      apply Subtype.ext
      rfl
    have hyb_eq : yb = (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ ((2 : ℕ) ^ Z.τ.m) := by
      apply Subtype.ext
      rfl
    rw [show y2 = ya * yb from rfl, ofMul_mul, map_add,
      hya_eq, hyb_eq, Z.dataD.e_pow, Z.dataD.e_pow, Z.dataD.e_a, Z.dataD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk1, hk2, Nat.add_sub_cancel, Torus.a, Torus.b, gen, Pi.single_apply]
    module
  have haa : Z.dataD.e (Additive.ofMul aa) =
      Torus.ofInt Z.τ.k ![0, -(2 : ℤ) ^ Z.τ.m, 0] := by
    have haa_eq : aa = ((⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)⁻¹) ^ ((2 : ℕ) ^ Z.τ.m) := by
      apply Subtype.ext
      rfl
    rw [haa_eq, Z.dataD.e_pow, ofMul_inv, map_neg, Z.dataD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add,
      Torus.a, gen, Pi.single_apply]
    module
  have heq : Z.dataD.e (Additive.ofMul (conjBy hρinv y2 * y2⁻¹)) =
      Z.dataD.e (Additive.ofMul aa) := by
    rw [e_commutator_rho_ofInt Z hrel
      (fun i => (![0, 1, 1] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) y2 hy2, haa]
    apply Torus.ofInt_eq_ofInt_iff.mpr
    intro i
    fin_cases i
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type100_rhoM_mulVec, hk1, hk2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨-2, ?_⟩
      rw [show Z.τ.k 0 = Z.τ.m from rfl]
      ring
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type100_rhoM_mulVec, hk1, hk2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type100_rhoM_mulVec, hk1, hk2,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [Int.modEq_zero_iff_dvd]
      exact ⟨-1, by ring⟩
  have hEqD : (conjBy hρinv y2 * y2⁻¹ : Z.D) = aa :=
    Additive.ofMul.injective (Z.dataD.e.injective heq)
  rw [← hval, hEqD]
  rfl


theorem omegaIn_a_pow (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    (Z.dataD.a : G) ^ (2 ^ Z.τ.m) ∈ omegaIn 1 Z.D := by
  classical
  let ya : Z.D := ⟨(Z.dataD.a : G) ^ (2 ^ Z.τ.m), Z.D.pow_mem Z.dataD.a.2 _⟩
  have hk1 : Z.τ.k 1 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hya : Z.dataD.e (Additive.ofMul ya) =
      Torus.ofInt Z.τ.k (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hya_eq : ya = (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ ((2 : ℕ) ^ Z.τ.m) := by
      apply Subtype.ext
      rfl
    rw [hya_eq, Z.dataD.e_pow, Z.dataD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk1, Nat.add_sub_cancel, Torus.a, gen, Pi.single_apply]
    module
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  have h2 : (2 : ℤ) • Z.dataD.e (Additive.ofMul ya) = 0 := by
    rw [hya]
    exact (Torus.two_zsmul_eq_zero_iff hk1all _).mpr
      ⟨![0, 1, 0], by intro i; fin_cases i <;> simp, rfl⟩
  have hya2 : ya * ya = 1 := by
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [show Additive.ofMul (ya * ya) = Additive.ofMul ya + Additive.ofMul ya from by
      rw [ofMul_mul]]
    rw [map_add, ← two_zsmul, h2, ofMul_one, map_zero]
  simpa [ya] using mem_omegaIn_one_of_mul_self ya.2 (congrArg Subtype.val hya2)


theorem omegaIn_b_pow (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    (Z.dataD.b : G) ^ (2 ^ Z.τ.m) ∈ omegaIn 1 Z.D := by
  classical
  let yb : Z.D := ⟨(Z.dataD.b : G) ^ (2 ^ Z.τ.m), Z.D.pow_mem Z.dataD.b.2 _⟩
  have hk2 : Z.τ.k 2 = Z.τ.m + 1 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hyb : Z.dataD.e (Additive.ofMul yb) =
      Torus.ofInt Z.τ.k (fun i => (![0, 0, 1] : Fin 3 → ℤ) i * 2 ^ (Z.τ.k i - 1)) := by
    have hyb_eq : yb = (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ ((2 : ℕ) ^ Z.τ.m) := by
      apply Subtype.ext
      rfl
    rw [hyb_eq, Z.dataD.e_pow, Z.dataD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply, zero_smul, zero_add, one_mul,
      hk2, Nat.add_sub_cancel, Torus.b, gen, Pi.single_apply]
    module
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  have h2 : (2 : ℤ) • Z.dataD.e (Additive.ofMul yb) = 0 := by
    rw [hyb]
    exact (Torus.two_zsmul_eq_zero_iff hk1all _).mpr
      ⟨![0, 0, 1], by intro i; fin_cases i <;> simp, rfl⟩
  have hyb2 : yb * yb = 1 := by
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [show Additive.ofMul (yb * yb) = Additive.ofMul yb + Additive.ofMul yb from by
      rw [ofMul_mul]]
    rw [map_add, ← two_zsmul, h2, ofMul_one, map_zero]
  simpa [yb] using mem_omegaIn_one_of_mul_self yb.2 (congrArg Subtype.val hyb2)

theorem omegaIn_ab_pow (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    ((Z.dataD.a : G) ^ (2 ^ Z.τ.m) * (Z.dataD.b : G) ^ (2 ^ Z.τ.m)) ∈
      omegaIn 1 Z.D :=
  (omegaIn 1 Z.D).mul_mem (omegaIn_a_pow Z hk hrel) (omegaIn_b_pow Z hk hrel)


theorem commutator_zpowers_rho_ge (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
        (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G) ≤
      ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆ := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers (Z.dataD.ρ : G)) (omegaIn_ab_pow Z hk hrel)
    rw [rho_commutator_ab_pow Z hk hrel] at h
    have hinv := Subgroup.inv_mem _ h
    simpa [inv_pow] using hinv
  · have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers (Z.dataD.ρ : G)) (omegaIn_a_pow Z hk hrel)
    rw [rho_commutator_a_pow Z hk hrel] at h
    have hinv := Subgroup.inv_mem _ h
    simpa [inv_pow] using hinv


theorem commutator_zpowers_rho_eq (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆ =
      Subgroup.closure ({(Z.dataD.a : G) ^ (2 ^ Z.τ.m),
        (Z.dataD.b : G) ^ (2 ^ Z.τ.m)} : Set G) :=
  le_antisymm (commutator_zpowers_rho_le Z hk hrel) (commutator_zpowers_rho_ge Z hk hrel)

theorem exists_sq_eq_c_and_commutator_of_familyOne (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) :
    ∃ s ∈ F, s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
      ⁅Subgroup.zpowers s, Z.D⁆ =
        ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆ := by
  obtain ⟨s, hsF, hsD, hsq⟩ :=
    exists_sq_eq_c_of_index_two_of_centOmega_of_familyOne Z hk hrel F hDF hF hN hidx hcent
  refine ⟨s, hsF, hsD, hsq, ?_⟩
  rw [commutator_zpowers_s_eq Z hk hrel F hDF hF hN hidx hcent hsF hsD,
    commutator_zpowers_rho_eq Z hk hrel]

end CFSG.CGT.Stroth77

end
