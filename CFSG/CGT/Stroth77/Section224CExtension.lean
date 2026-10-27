module

public import CFSG.CGT.Stroth77.Section224ModTwo
public import CFSG.CGT.Stroth77.Section224A

public section

namespace CFSG.CGT.Stroth77

open Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

@[expose] def deviationTorus (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho) :
    Additive Z.D →+ Torus Z.τ.k :=
  Z.dataD.e.toAddMonoidHom.comp
    ((Subgroup.inclusion (omegaIn_le 1 Z.D)).toAdditive.comp (deviation Z s hs))

theorem deviationTorus_apply (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) :
    deviationTorus Z s hs (Additive.ofMul d) =
      Z.dataD.e (Additive.ofMul ⟨((deviation Z s hs (Additive.ofMul d)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul d)).toMul.2⟩) := by
  rw [deviationTorus]
  rfl

theorem deviation_mem_omega (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) : ((deviation Z s hs (Additive.ofMul d)).toMul : G) ∈ omegaIn 1 Z.D :=
  (deviation Z s hs (Additive.ofMul d)).toMul.2

theorem deviation_sq_mem (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) : ((deviation Z s hs (Additive.ofMul (d * d))).toMul : G) = 1 := by
  have h := deviation_sq_eq_zero Z s hs d
  rw [h]
  rfl

theorem deviationTorus_two_zsmul (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) : (2 : ℤ) • deviationTorus Z s hs (Additive.ofMul d) = 0 := by
  have h : deviationTorus Z s hs (Additive.ofMul (d * d)) = 0 := by
    rw [deviationTorus_apply, deviation_sq_eq_zero Z s hs d]
    simp
  rw [ofMul_mul, map_add] at h
  rw [two_zsmul]
  exact h

theorem deviationTorus_add_self (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) :
    deviationTorus Z s hs (Additive.ofMul d) + deviationTorus Z s hs (Additive.ofMul d) = 0 := by
  rw [← two_zsmul]
  exact deviationTorus_two_zsmul Z s hs d

theorem deviationTorus_sq_eq_zero (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) : deviationTorus Z s hs (Additive.ofMul (d * d)) = 0 := by
  rw [ofMul_mul, map_add]
  exact deviationTorus_add_self Z s hs d

theorem deviation_conj_eq (Z : StrothDatum X) {s l d : G}
    (hs : s ∈ Z.centralizerInMho) (hd : d ∈ Z.D)
    (hlN : l ∈ Subgroup.normalizer (Z.D : Set G))
    (hconj : l * s * l⁻¹ = s * d) {x : G} (hx : x ∈ Z.D) :
    ((deviation Z s hs (Additive.ofMul ⟨l⁻¹ * x * l,
        (Subgroup.mem_normalizer_iff''.mp hlN x).mp hx⟩)).toMul : G)
      = l⁻¹ * ((deviation Z s hs (Additive.ofMul ⟨x, hx⟩)).toMul : G) * l := by
  have hdxraw : d * x = x * d := by
    haveI : IsMulCommutative Z.D := Z.dataD.isMulCommutative
    exact Subtype.ext_iff.mp (IsMulCommutative.is_comm.comm (⟨d, hd⟩ : Z.D) ⟨x, hx⟩)
  have hdx : d * x * d⁻¹ = x := by
    rw [hdxraw]
    group
  have hs_inv : l * s⁻¹ * l⁻¹ = d⁻¹ * s⁻¹ := by
    calc l * s⁻¹ * l⁻¹ = (l * s * l⁻¹)⁻¹ := by group
      _ = (s * d)⁻¹ := by rw [hconj]
      _ = d⁻¹ * s⁻¹ := by group
  rw [deviation_apply, deviation_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
  calc s * (l⁻¹ * x * l) * s⁻¹ * (l⁻¹ * x * l)⁻¹
      = l⁻¹ * ((l * s * l⁻¹) * x * (l * s⁻¹ * l⁻¹) * x⁻¹) * l := by group
    _ = l⁻¹ * ((s * d) * x * (d⁻¹ * s⁻¹) * x⁻¹) * l := by rw [hconj, hs_inv]
    _ = l⁻¹ * (s * x * s⁻¹ * x⁻¹) * l := by
      rw [show s * d * x * (d⁻¹ * s⁻¹) * x⁻¹ = s * (d * x * d⁻¹) * s⁻¹ * x⁻¹ by group,
        hdx]

theorem deviationTorus_conj_eq (Z : StrothDatum X) {s l d : G}
    (hs : s ∈ Z.centralizerInMho) (hd : d ∈ Z.D)
    (hlN : l ∈ Subgroup.normalizer (Z.D : Set G))
    (hconj : l * s * l⁻¹ = s * d)
    {M : IntMat} {hM : Compat Z.τ.k M}
    (hmat : ∀ y : Z.D, Z.dataD.e (Additive.ofMul (conjBy hlN y)) =
      matAct Z.τ.k M hM (Z.dataD.e (Additive.ofMul y)))
    {x : G} (hx : x ∈ Z.D) :
    deviationTorus Z s hs (Additive.ofMul (conjBy hlN ⟨x, hx⟩)) =
      matAct Z.τ.k M hM (deviationTorus Z s hs (Additive.ofMul ⟨x, hx⟩)) := by
  have h := deviation_conj_eq Z hs hd hlN hconj hx
  rw [deviationTorus_apply, deviationTorus_apply, ← hmat ⟨((deviation Z s hs
    (Additive.ofMul ⟨x, hx⟩)).toMul : G), omegaIn_le 1 Z.D
      (deviation Z s hs (Additive.ofMul ⟨x, hx⟩)).toMul.2⟩]
  have hsub : (⟨((deviation Z s hs (Additive.ofMul (conjBy hlN ⟨x, hx⟩))).toMul : G),
      omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul (conjBy hlN ⟨x, hx⟩))).toMul.2⟩ : Z.D)
      = conjBy hlN ⟨((deviation Z s hs (Additive.ofMul ⟨x, hx⟩)).toMul : G),
          omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul ⟨x, hx⟩)).toMul.2⟩ := by
    rw [show (⟨((deviation Z s hs (Additive.ofMul (conjBy hlN ⟨x, hx⟩))).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul (conjBy hlN ⟨x, hx⟩))).toMul.2⟩ : Z.D)
        = ⟨l⁻¹ * ((deviation Z s hs (Additive.ofMul ⟨x, hx⟩)).toMul : G) * l, _⟩ from
          Subtype.ext h]
    rfl
  rw [hsub]

theorem int_modEq_two_of_mul_two_pow_modEq {m : ℕ} {a b : ℤ}
    (h : a * 2 ^ m ≡ b * 2 ^ m [ZMOD 2 ^ (m + 1)]) : a ≡ b [ZMOD 2] := by
  have hdvd : (2 : ℤ) ^ (m + 1) ∣ b * 2 ^ m - a * 2 ^ m := Int.modEq_iff_dvd.mp h
  rw [show b * 2 ^ m - a * 2 ^ m = (b - a) * 2 ^ m by ring] at hdvd
  have hfac : (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ m * 2 := by
    rw [pow_succ]
  rw [hfac] at hdvd
  rw [show (b - a) * 2 ^ m = 2 ^ m * (b - a) by ring] at hdvd
  have h2 : (2 : ℤ) ∣ b - a :=
    (mul_dvd_mul_iff_left (pow_ne_zero m (by norm_num : (2 : ℤ) ≠ 0))).mp hdvd
  exact Int.modEq_iff_dvd.mpr (by simpa using h2)

theorem int_modEq_two_of_mul_two_pow_pred_modEq {m : ℕ} (hm : 1 ≤ m) {a b : ℤ}
    (h : a * 2 ^ (m - 1) ≡ b * 2 ^ (m - 1) [ZMOD 2 ^ m]) : a ≡ b [ZMOD 2] := by
  have hm' : m = (m - 1) + 1 := by omega
  have hdvd : (2 : ℤ) ^ m ∣ b * 2 ^ (m - 1) - a * 2 ^ (m - 1) := Int.modEq_iff_dvd.mp h
  rw [show b * 2 ^ (m - 1) - a * 2 ^ (m - 1) = (b - a) * 2 ^ (m - 1) by ring] at hdvd
  have hfac : (2 : ℤ) ^ m = (2 : ℤ) ^ (m - 1) * 2 := by
    conv_lhs => rw [hm']
    rw [pow_succ]
  rw [hfac] at hdvd
  rw [show (b - a) * 2 ^ (m - 1) = 2 ^ (m - 1) * (b - a) by ring] at hdvd
  have h2 : (2 : ℤ) ∣ b - a :=
    (mul_dvd_mul_iff_left (pow_ne_zero (m - 1) (by norm_num : (2 : ℤ) ≠ 0))).mp hdvd
  exact Int.modEq_iff_dvd.mpr (by simpa using h2)

theorem int_eq_zero_of_modEq_two {a : ℤ} (ha : a = 0 ∨ a = 1) (h : a ≡ 0 [ZMOD 2]) : a = 0 := by
  have h2 : (2 : ℤ) ∣ a := by
    have := Int.modEq_iff_dvd.mp h
    simpa using this
  rcases ha with ha0 | ha1
  · exact ha0
  · subst ha1
    norm_num at h2

theorem int_eq_of_modEq_two {a b : ℤ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (h : a ≡ b [ZMOD 2]) : a = b := by
  have h2 : (2 : ℤ) ∣ b - a := Int.modEq_iff_dvd.mp h
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · rw [ha0, hb0]
  · exfalso
    rw [ha0, hb1] at h2
    norm_num at h2
  · exfalso
    rw [ha1, hb0] at h2
    norm_num at h2
  · rw [ha1, hb1]

theorem int_eq_zero_of_mul_two_pow_modEq {m : ℕ} {a : ℤ}
    (ha : a = 0 ∨ a = 1) (h : a * 2 ^ m ≡ 0 [ZMOD 2 ^ (m + 1)]) : a = 0 := by
  refine int_eq_zero_of_modEq_two ha ?_
  have h' : a * 2 ^ m ≡ (0 : ℤ) * 2 ^ m [ZMOD 2 ^ (m + 1)] := by simpa using h
  simpa using int_modEq_two_of_mul_two_pow_modEq h'

theorem int_eq_zero_of_two_mul_mul_two_pow_pred_modEq {m : ℕ} (hm : 1 ≤ m) {a : ℤ}
    (ha : a = 0 ∨ a = 1) (h : 2 * (a * 2 ^ (m - 1)) ≡ 0 [ZMOD 2 ^ (m + 1)]) : a = 0 := by
  have hpow : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
    ring
  refine int_eq_zero_of_mul_two_pow_modEq (m := m) ha ?_
  rw [hpow]
  calc a * (2 * 2 ^ (m - 1)) = 2 * (a * 2 ^ (m - 1)) := by ring
    _ ≡ 0 [ZMOD 2 ^ (m + 1)] := h

theorem type100_uM_mulVec (v : Fin 3 → ℤ) :
    Type100.uM *ᵥ v = ![v 0, v 2, v 1] := by
  funext i
  fin_cases i <;>
    simp [Type100.uM, uMat, ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem type100_rhoM_mulVec (v : Fin 3 → ℤ) :
    Type100.ρM *ᵥ v = ![v 0 - 2 * v 2, -v 2, v 1 - v 2] := by
  funext i
  fin_cases i <;>
    simp [Type100.ρM, ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem type100_uvM_mulVec (v : Fin 3 → ℤ) :
    Type100.uvM *ᵥ v = ![-3 * v 0 + 2 * v 1 + 2 * v 2, -2 * v 0 + v 1 + 2 * v 2,
      -2 * v 0 + 2 * v 1 + v 2] := by
  funext i
  fin_cases i <;>
    simp [Type100.uvM, Type100.uvA, Type100.tM, Type100.ρM, ofCols, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three] <;> ring


theorem t100_compat_uv (m : ℕ) : Compat (StrothTypeIndex.t100 m).k Type100.uvM := by
  change Compat (Type100.k m) Type100.uvM
  exact Type100.compat_uv m

theorem t100_compat_t (m : ℕ) : Compat (StrothTypeIndex.t100 m).k Type100.tM := by
  change Compat (Type100.k m) Type100.tM
  exact Type100.compat_t m

theorem t100_compat_u (m : ℕ) : Compat (StrothTypeIndex.t100 m).k Type100.uM := by
  change Compat (Type100.k m) Type100.uM
  exact Type100.compat_u m

theorem t100_compat_rho (m : ℕ) : Compat (StrothTypeIndex.t100 m).k Type100.ρM := by
  change Compat (Type100.k m) Type100.ρM
  exact Type100.compat_rho m

theorem t100_action_u_a (m : ℕ) :
    (StrothTypeIndex.t100 m).action.φu (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
      (Torus.b : Torus (StrothTypeIndex.t100 m).k) := by
  change (Type100.action m).φu (Torus.a : Torus (Type100.k m)) =
    (Torus.b : Torus (Type100.k m))
  simpa using Type100.u_a m

theorem t100_action_uv_a (m : ℕ) :
    (StrothTypeIndex.t100 m).action.φuv (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
      (2 : ℤ) • (Torus.c : Torus (StrothTypeIndex.t100 m).k) +
        (1 : ℤ) • (Torus.a : Torus (StrothTypeIndex.t100 m).k) +
        (2 : ℤ) • (Torus.b : Torus (StrothTypeIndex.t100 m).k) := by
  change (Type100.action m).φuv (Torus.a : Torus (Type100.k m)) =
    (2 : ℤ) • (Torus.c : Torus (Type100.k m)) +
      (1 : ℤ) • (Torus.a : Torus (Type100.k m)) +
      (2 : ℤ) • (Torus.b : Torus (Type100.k m))
  exact Type100.uv_a m

theorem t100_action_rho_a (m : ℕ) :
    (StrothTypeIndex.t100 m).action.φρ (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
      (Torus.b : Torus (StrothTypeIndex.t100 m).k) := by
  change (Type100.action m).φρ (Torus.a : Torus (Type100.k m)) =
    (Torus.b : Torus (Type100.k m))
  simpa using Type100.rho_a m

theorem two_torsion_solution (m : ℕ) (hm : 2 ≤ m)
    (w w' : Torus (StrothTypeIndex.t100 m).k)
    (hw2 : (2 : ℤ) • w = 0) (hw2' : (2 : ℤ) • w' = 0)
    (hE2 : w' = matAct (StrothTypeIndex.t100 m).k Type100.uM (t100_compat_u m) w)
    (hE3 : w' = matAct (StrothTypeIndex.t100 m).k Type100.ρM (t100_compat_rho m) w)
    (hE1 : matAct (StrothTypeIndex.t100 m).k Type100.uvM (t100_compat_uv m) w = w)
    (hne : w ≠ 0) :
    w = (2 : ℤ) ^ m • (Torus.a : Torus (StrothTypeIndex.t100 m).k) ∧
    w' = (2 : ℤ) ^ m • (Torus.b : Torus (StrothTypeIndex.t100 m).k) := by
  have hk1 : ∀ i, 1 ≤ (StrothTypeIndex.t100 m).k i := by
    intro i
    fin_cases i <;> simp [StrothTypeIndex.k, Type100.k] <;> omega
  obtain ⟨ε, hε, hwε⟩ := (Torus.two_zsmul_eq_zero_iff hk1 w).mp hw2
  obtain ⟨ε', hε', hw'ε⟩ := (Torus.two_zsmul_eq_zero_iff hk1 w').mp hw2'
  have h2 : Torus.ofInt (StrothTypeIndex.t100 m).k
        (fun i => ε' i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1)) =
      matAct (StrothTypeIndex.t100 m).k Type100.uM (t100_compat_u m)
        (Torus.ofInt (StrothTypeIndex.t100 m).k
          (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1))) := by
    rw [← hw'ε, ← hwε]
    exact hE2
  rw [matAct_ofInt] at h2
  have h3 : Torus.ofInt (StrothTypeIndex.t100 m).k
        (fun i => ε' i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1)) =
      matAct (StrothTypeIndex.t100 m).k Type100.ρM (t100_compat_rho m)
        (Torus.ofInt (StrothTypeIndex.t100 m).k
          (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1))) := by
    rw [← hw'ε, ← hwε]
    exact hE3
  rw [matAct_ofInt] at h3
  have h1 : matAct (StrothTypeIndex.t100 m).k Type100.uvM (t100_compat_uv m)
        (Torus.ofInt (StrothTypeIndex.t100 m).k
          (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1))) =
      Torus.ofInt (StrothTypeIndex.t100 m).k
        (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1)) := by
    rw [← hwε]
    exact hE1
  rw [matAct_ofInt] at h1
  have hE2c2 : ε' 2 * 2 ^ m ≡ ε 1 * 2 ^ m [ZMOD 2 ^ (m + 1)] := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp h2) 2
    simpa [StrothTypeIndex.k, Type100.k, type100_uM_mulVec, Nat.add_sub_cancel] using h
  have hE3c2 : ε' 2 * 2 ^ m ≡ (ε 1 - ε 2) * 2 ^ m [ZMOD 2 ^ (m + 1)] := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp h3) 2
    simpa [StrothTypeIndex.k, Type100.k, type100_rhoM_mulVec, Nat.add_sub_cancel, sub_mul] using h
  have hε'2 : ε' 2 = ε 1 :=
    int_eq_of_modEq_two (hε' 2) (hε 1) (int_modEq_two_of_mul_two_pow_modEq hE2c2)
  have hε2 : ε 2 = 0 := by
    have h3' : ε 1 * 2 ^ m ≡ (ε 1 - ε 2) * 2 ^ m [ZMOD 2 ^ (m + 1)] := by
      have h := hE3c2
      rwa [hε'2] at h
    have hdiv : (2 : ℤ) ∣ ε 2 := by
      have h := Int.modEq_iff_dvd.mp (int_modEq_two_of_mul_two_pow_modEq h3')
      simpa using h
    rcases hε 2 with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at hdiv
      norm_num at hdiv
  have hE1c1 : ε 0 * 2 ^ m ≡ 0 [ZMOD 2 ^ (m + 1)] := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp h1) 1
    have hc' : ε 1 * 2 ^ m ≡
        -2 * (ε 0 * 2 ^ (m - 1)) + ε 1 * 2 ^ m + 2 * (ε 2 * 2 ^ m) [ZMOD 2 ^ (m + 1)] := by
      simpa [StrothTypeIndex.k, Type100.k, type100_uvM_mulVec, Nat.add_sub_cancel] using h.symm
    have hdvd := Int.modEq_iff_dvd.mp hc'
    have hpow : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
      ring
    have hpow' : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by
      rw [pow_succ]
      ring
    have hdiff : (-2 * (ε 0 * 2 ^ (m - 1)) + ε 1 * 2 ^ m + 2 * (ε 2 * 2 ^ m)) -
        ε 1 * 2 ^ m = -(ε 0 * 2 ^ m) + ε 2 * 2 ^ (m + 1) := by
      rw [hpow', hpow]
      ring
    rw [hdiff] at hdvd
    have hdvd'' : (2 : ℤ) ^ (m + 1) ∣ ε 2 * 2 ^ (m + 1) + -(ε 0 * 2 ^ m) := by
      simpa [add_comm] using hdvd
    have h3 : (2 : ℤ) ^ (m + 1) ∣ ε 2 * 2 ^ (m + 1) := ⟨ε 2, by ring⟩
    have hdvd' : (2 : ℤ) ^ (m + 1) ∣ -(ε 0 * 2 ^ m) := (dvd_add_right h3).mp hdvd''
    exact Int.modEq_iff_dvd.mpr (by simpa using hdvd')
  have hε0 : ε 0 = 0 := int_eq_zero_of_mul_two_pow_modEq (hε 0) hE1c1
  have hε1 : ε 1 = 1 := by
    rcases hε 1 with h0 | h1
    · exfalso
      apply hne
      rw [hwε]
      have hvec : (fun i => ε i * 2 ^ ((StrothTypeIndex.t100 m).k i - 1)) = 0 := by
        funext i
        fin_cases i <;> simp [StrothTypeIndex.k, Type100.k, hε0, h0, hε2]
      rw [hvec]
      simp
    · exact h1
  have ha_ofInt : (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
      Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0] := by
    funext i
    fin_cases i <;> simp [Torus.a, gen, Torus.ofInt_apply, Fin.isValue]
  have hwval : w = (2 : ℤ) ^ m • (Torus.a : Torus (StrothTypeIndex.t100 m).k) := by
    rw [hwε, ha_ofInt, ← Torus.ofInt_zsmul, Torus.ofInt_eq_ofInt_iff]
    intro i
    fin_cases i <;> simp [StrothTypeIndex.k, Type100.k, hε0, hε1, hε2]
  have huMa : matAct (StrothTypeIndex.t100 m).k Type100.uM (t100_compat_u m)
      (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
      (Torus.b : Torus (StrothTypeIndex.t100 m).k) := by
    have h := matAct_gen_eq (k := (StrothTypeIndex.t100 m).k) Type100.uM (t100_compat_u m)
      (1 : Fin 3)
    simpa [Type100.uM, uMat, ofCols, Torus.a, Torus.b, gen, Fin.isValue] using h
  constructor
  · exact hwval
  · rw [hE2, hwval, map_zsmul, huMa]

theorem deviation_form_diag (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (hrel : Z.τ.m + 1 = Z.τ.n) {m : ℕ} (hτ : Z.τ = StrothTypeIndex.t100 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ m) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ m) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  classical
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X := ⟨D, hAD, hDS, StrothTypeIndex.t100 m, dataD, hL, hcentS⟩ with hZ'
  have hm2 : 2 ≤ m := hk 0
  have hc_mem : (Z'.dataD.c : G) ∈ omegaIn (Z'.τ.n - 1) Z'.D := by
    refine mem_omegaIn_of_pow_eq_one Z'.dataD.c.2 ?_
    have hn : Z'.τ.n - 1 = m := by
      change (StrothTypeIndex.t100 m).k 1 - 1 = m
      rw [show (StrothTypeIndex.t100 m).k 1 = m + 1 from rfl]
      omega
    rw [hn, ← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, Z'.dataD.orderOf_c]
    exact dvd_rfl
  have hcs : s * (Z'.dataD.c : G) = (Z'.dataD.c : G) * s :=
    (Subgroup.mem_centralizer_iff.mp (hcent hsF) _ hc_mem).symm
  have hφc : ((deviation Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩)).toMul : G) = 1 := by
    rw [deviation_apply]
    calc s * (Z'.dataD.c : G) * s⁻¹ * (Z'.dataD.c : G)⁻¹
        = (Z'.dataD.c : G) * s * s⁻¹ * (Z'.dataD.c : G)⁻¹ := by rw [hcs]
      _ = 1 := by group
  have hΦc0 : deviationTorus Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩) = 0 := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩)).toMul : G),
        omegaIn_le 1 Z'.D (deviation Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩)).toMul.2⟩ : Z'.D) = 1 :=
      Subtype.ext hφc
    rw [h1]
    simp
  have hua_sub : conjBy Z'.dataD.u_mem (⟨Z'.dataD.a, Z'.dataD.a.2⟩ : Z'.D) =
      ⟨Z'.dataD.b, Z'.dataD.b.2⟩ := by
    have h := Z'.dataD.u_conj (⟨Z'.dataD.a, Z'.dataD.a.2⟩ : Z'.D)
    rw [Z'.dataD.e_a] at h
    have hφ : Z'.τ.action.φu (Torus.a : Torus Z'.τ.k) = (Torus.b : Torus Z'.τ.k) := by
      change (StrothTypeIndex.t100 m).action.φu
        (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
        (Torus.b : Torus (StrothTypeIndex.t100 m).k)
      exact t100_action_u_a m
    rw [hφ, ← Z'.dataD.e_b] at h
    exact Additive.ofMul.injective (Z'.dataD.e.injective h)
  have huv_sub : conjBy Z'.dataD.uv_mem (⟨Z'.dataD.a, Z'.dataD.a.2⟩ : Z'.D) =
      ⟨Z'.dataD.c, Z'.dataD.c.2⟩ ^ 2 * ⟨Z'.dataD.a, Z'.dataD.a.2⟩ *
        (⟨Z'.dataD.b, Z'.dataD.b.2⟩ : Z'.D) ^ 2 := by
    have h := Z'.dataD.uv_conj (⟨Z'.dataD.a, Z'.dataD.a.2⟩ : Z'.D)
    rw [Z'.dataD.e_a] at h
    have hφ : Z'.τ.action.φuv (Torus.a : Torus Z'.τ.k) =
        (2 : ℤ) • (Torus.c : Torus Z'.τ.k) + (1 : ℤ) • (Torus.a : Torus Z'.τ.k) +
          (2 : ℤ) • (Torus.b : Torus Z'.τ.k) := by
      change (StrothTypeIndex.t100 m).action.φuv
          (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
        (2 : ℤ) • (Torus.c : Torus (StrothTypeIndex.t100 m).k) +
          (1 : ℤ) • (Torus.a : Torus (StrothTypeIndex.t100 m).k) +
          (2 : ℤ) • (Torus.b : Torus (StrothTypeIndex.t100 m).k)
      exact t100_action_uv_a m
    rw [hφ] at h
    have hrhs : (2 : ℤ) • (Torus.c : Torus Z'.τ.k) + (1 : ℤ) • (Torus.a : Torus Z'.τ.k) +
        (2 : ℤ) • (Torus.b : Torus Z'.τ.k) =
        Z'.dataD.e (Additive.ofMul ((⟨Z'.dataD.c, Z'.dataD.c.2⟩ : Z'.D) ^ 2 *
          ⟨Z'.dataD.a, Z'.dataD.a.2⟩ * (⟨Z'.dataD.b, Z'.dataD.b.2⟩ : Z'.D) ^ 2)) := by
      rw [ofMul_mul, ofMul_mul, ofMul_pow, ofMul_pow, map_add, map_add, map_nsmul, map_nsmul,
        Z'.dataD.e_c, Z'.dataD.e_a, Z'.dataD.e_b]
      norm_num
    rw [hrhs] at h
    exact Additive.ofMul.injective (Z'.dataD.e.injective h)
  have hρa_sub : conjBy Z'.dataD.ρ_mem (⟨Z'.dataD.a, Z'.dataD.a.2⟩ : Z'.D) =
      ⟨Z'.dataD.b, Z'.dataD.b.2⟩ := by
    have h := Z'.dataD.ρ_conj (⟨Z'.dataD.a, Z'.dataD.a.2⟩ : Z'.D)
    rw [Z'.dataD.e_a] at h
    have hφ : Z'.τ.action.φρ (Torus.a : Torus Z'.τ.k) = (Torus.b : Torus Z'.τ.k) := by
      change (StrothTypeIndex.t100 m).action.φρ
        (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
        (Torus.b : Torus (StrothTypeIndex.t100 m).k)
      exact t100_action_rho_a m
    rw [hφ, ← Z'.dataD.e_b] at h
    exact Additive.ofMul.injective (Z'.dataD.e.injective h)
  have huL : Z'.dataD.u ∈ X.L := hL ▸ Z'.dataD.u_mem_L
  have huvL : Z'.dataD.uv ∈ X.L := hL ▸ Z'.dataD.uv_mem_L
  have hρL : Z'.dataD.ρ ∈ X.L := hL ▸ Z'.dataD.ρ_mem_L
  obtain ⟨du, hduD, hdu⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hsF hsD huL
  obtain ⟨duv, hduvD, hduv⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hsF hsD huvL
  obtain ⟨dr, hdrD, hdr⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hsF hsD
      (X.L.inv_mem hρL)
  have huinv : (Z'.dataD.u)⁻¹ = Z'.dataD.u := inv_eq_of_mul_eq_one_right Z'.dataD.u_sq
  have huvinv : (Z'.dataD.uv)⁻¹ = Z'.dataD.uv := inv_eq_of_mul_eq_one_right Z'.dataD.uv_sq
  have hdu' : Z'.dataD.u * s * (Z'.dataD.u)⁻¹ = s * du := by
    simpa [huinv] using hdu
  have hduv' : Z'.dataD.uv * s * (Z'.dataD.uv)⁻¹ = s * duv := by
    simpa [huvinv] using hduv
  have hdr' : Z'.dataD.ρ * s * (Z'.dataD.ρ)⁻¹ = s * dr := by
    simpa using hdr
  have hdev_u : deviationTorus Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩) =
      matAct Z'.τ.k Type100.uM (t100_compat_u m)
        (deviationTorus Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)) := by
    have h := deviationTorus_conj_eq Z' (hF hsF) hduD Z'.dataD.u_mem hdu'
      (M := Type100.uM) (hM := t100_compat_u m) (hmat := Z'.dataD.u_conj)
      (x := Z'.dataD.a) Z'.dataD.a.2
    rwa [hua_sub] at h
  have hdev_r : deviationTorus Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩) =
      matAct Z'.τ.k Type100.ρM (t100_compat_rho m)
        (deviationTorus Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)) := by
    have h := deviationTorus_conj_eq Z' (hF hsF) hdrD Z'.dataD.ρ_mem hdr'
      (M := Type100.ρM) (hM := t100_compat_rho m) (hmat := Z'.dataD.ρ_conj)
      (x := Z'.dataD.a) Z'.dataD.a.2
    rwa [hρa_sub] at h
  have hdev_uv : matAct Z'.τ.k Type100.uvM (t100_compat_uv m)
      (deviationTorus Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)) =
      deviationTorus Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩) := by
    have h := deviationTorus_conj_eq Z' (hF hsF) hduvD Z'.dataD.uv_mem hduv'
      (M := Type100.uvM) (hM := t100_compat_uv m) (hmat := Z'.dataD.uv_conj)
      (x := Z'.dataD.a) Z'.dataD.a.2
    have hstep : deviationTorus Z' s (hF hsF) (Additive.ofMul
        ((⟨Z'.dataD.c, Z'.dataD.c.2⟩ : Z'.D) ^ 2 * ⟨Z'.dataD.a, Z'.dataD.a.2⟩ *
          (⟨Z'.dataD.b, Z'.dataD.b.2⟩ : Z'.D) ^ 2)) =
        deviationTorus Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩) := by
      rw [pow_two, pow_two]
      simp only [ofMul_mul, map_add, deviationTorus_add_self, add_zero, zero_add]
    rw [huv_sub, hstep] at h
    exact h.symm
  have hne : deviationTorus Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩) ≠ 0 := by
    intro hw0
    apply hsD
    have hΦa0 : deviationTorus Z' s (hF hsF)
        (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩) = 0 := hw0
    have hΦb0 : deviationTorus Z' s (hF hsF)
        (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩) = 0 := by
      rw [hdev_u, hΦa0, map_zero]
    have hΦall : ∀ x : Z'.D, deviationTorus Z' s (hF hsF) (Additive.ofMul x) = 0 := by
      intro x
      obtain ⟨W, hW⟩ := Torus.exists_ofInt (Z'.dataD.e (Additive.ofMul x))
      have hdec : Additive.ofMul x =
          Z'.dataD.e.symm (W 0 • (Torus.c : Torus Z'.τ.k) +
            W 1 • (Torus.a : Torus Z'.τ.k) + W 2 • (Torus.b : Torus Z'.τ.k)) := by
        apply Z'.dataD.e.injective
        rw [AddEquiv.apply_symm_apply, ← hW, Torus.ofInt_eq_zsmul_gens]
      have hc' : Z'.dataD.e.symm (Torus.c : Torus Z'.τ.k) =
          Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩ := by
        rw [← Z'.dataD.e_c, AddEquiv.symm_apply_apply]
      have ha' : Z'.dataD.e.symm (Torus.a : Torus Z'.τ.k) =
          Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩ := by
        rw [← Z'.dataD.e_a, AddEquiv.symm_apply_apply]
      have hb' : Z'.dataD.e.symm (Torus.b : Torus Z'.τ.k) =
          Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩ := by
        rw [← Z'.dataD.e_b, AddEquiv.symm_apply_apply]
      rw [hdec]
      simp only [map_add, map_zsmul, hc', ha', hb', hΦc0, hΦa0, hΦb0, smul_zero, add_zero]
    apply Z'.mem_of_mem_centralizer (hF hsF).1.1
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hΦall ⟨d, hd⟩
    rw [deviationTorus_apply] at h
    have h1 : ((deviation Z' s (hF hsF) (Additive.ofMul ⟨d, hd⟩)).toMul : G) = 1 := by
      have h' : Z'.dataD.e (Additive.ofMul ⟨((deviation Z' s (hF hsF)
          (Additive.ofMul ⟨d, hd⟩)).toMul : G), omegaIn_le 1 Z'.D
            (deviation Z' s (hF hsF) (Additive.ofMul ⟨d, hd⟩)).toMul.2⟩) =
          Z'.dataD.e (Additive.ofMul (1 : Z'.D)) := by
        rw [h]
        simp
      have hx := Additive.ofMul.injective (Z'.dataD.e.injective h')
      simpa using congrArg Subtype.val hx
    have h2 : s * d * s⁻¹ * d⁻¹ = 1 := by
      simpa [deviation_apply] using h1
    have h3 : s * d * s⁻¹ = d := by
      have := congrArg (· * d) h2
      simpa [mul_assoc] using this
    have h4 : s * d = d * s := by
      have := congrArg (· * s) h3
      simpa [mul_assoc] using this
    exact h4.symm
  have hw2a : (2 : ℤ) • deviationTorus Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩) = 0 := deviationTorus_two_zsmul Z' s (hF hsF) _
  have hw2b : (2 : ℤ) • deviationTorus Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩) = 0 := deviationTorus_two_zsmul Z' s (hF hsF) _
  obtain ⟨hwval, hw'val⟩ :=
    two_torsion_solution m hm2 _ _ hw2a hw2b hdev_u hdev_r hdev_uv hne
  have hφa : ((deviation Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)).toMul : G) = (Z'.dataD.a : G) ^ (2 ^ m) := by
    have h : deviationTorus Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩) =
        (2 : ℤ) ^ m • (Torus.a : Torus (StrothTypeIndex.t100 m).k) := hwval
    rw [deviationTorus_apply] at h
    have h2 : Z'.dataD.e (Additive.ofMul (Z'.dataD.a ^ (2 ^ m))) =
        (2 ^ m : ℕ) • (Torus.a : Torus (StrothTypeIndex.t100 m).k) := by
      rw [Z'.dataD.e_pow, Z'.dataD.e_a]
    have h' : Z'.dataD.e (Additive.ofMul ⟨((deviation Z' s (hF hsF)
        (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)).toMul : G), omegaIn_le 1 Z'.D
          (deviation Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)).toMul.2⟩) =
        Z'.dataD.e (Additive.ofMul (Z'.dataD.a ^ (2 ^ m))) := by
      rw [h, h2, show (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) by push_cast; ring, natCast_zsmul]
    have hx := Additive.ofMul.injective (Z'.dataD.e.injective h')
    simpa using congrArg Subtype.val hx
  have hφb : ((deviation Z' s (hF hsF)
      (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩)).toMul : G) = (Z'.dataD.b : G) ^ (2 ^ m) := by
    have h : deviationTorus Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩) =
        (2 : ℤ) ^ m • (Torus.b : Torus (StrothTypeIndex.t100 m).k) := hw'val
    rw [deviationTorus_apply] at h
    have h2 : Z'.dataD.e (Additive.ofMul (Z'.dataD.b ^ (2 ^ m))) =
        (2 ^ m : ℕ) • (Torus.b : Torus (StrothTypeIndex.t100 m).k) := by
      rw [Z'.dataD.e_pow, Z'.dataD.e_b]
    have h' : Z'.dataD.e (Additive.ofMul ⟨((deviation Z' s (hF hsF)
        (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩)).toMul : G), omegaIn_le 1 Z'.D
          (deviation Z' s (hF hsF) (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩)).toMul.2⟩) =
        Z'.dataD.e (Additive.ofMul (Z'.dataD.b ^ (2 ^ m))) := by
      rw [h, h2, show (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) by push_cast; ring, natCast_zsmul]
    have hx := Additive.ofMul.injective (Z'.dataD.e.injective h')
    simpa using congrArg Subtype.val hx
  exact ⟨hφc, hφa, hφb, fun d => deviation_sq_mem Z' s (hF hsF) d⟩


noncomputable def thetaT (m : ℕ) :
    Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k :=
  theta m

theorem thetaT_ofInt (m : ℕ) (v : Fin 3 → ℤ) :
    thetaT m (Torus.ofInt (StrothTypeIndex.t100 m).k v) =
      Torus.ofInt (StrothTypeIndex.t100 m).k (thetaM m *ᵥ v) := by
  change theta m (Torus.ofInt (Type100.k m) v) = Torus.ofInt (Type100.k m) (thetaM m *ᵥ v)
  rw [theta_ofInt]

theorem thetaT_c (m : ℕ) :
    thetaT m (Torus.c : Torus (StrothTypeIndex.t100 m).k) = (2 : ℤ) • Torus.c := by
  have h : (Torus.c : Torus (StrothTypeIndex.t100 m).k) =
      Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.c]
  rw [h, thetaT_ofInt]
  have h2 : thetaM m *ᵥ (![1, 0, 0] : Fin 3 → ℤ) = ![2, 0, 0] := by
    funext i
    fin_cases i <;> simp [thetaM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [h2, Torus.ofInt_eq_zsmul_gens]
  rw [← h]
  simp

theorem thetaT_a (m : ℕ) :
    thetaT m (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
      (2 + (2 : ℤ) ^ m) • Torus.a := by
  have h : (Torus.a : Torus (StrothTypeIndex.t100 m).k) =
      Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.a]
  rw [h, thetaT_ofInt]
  have h2 : thetaM m *ᵥ (![0, 1, 0] : Fin 3 → ℤ) = ![0, 2 + (2 : ℤ) ^ m, 0] := by
    funext i
    fin_cases i <;> simp [thetaM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [h2, Torus.ofInt_eq_zsmul_gens]
  rw [← h]
  simp

theorem thetaT_b (m : ℕ) :
    thetaT m (Torus.b : Torus (StrothTypeIndex.t100 m).k) =
      (2 + (2 : ℤ) ^ m) • Torus.b := by
  have h : (Torus.b : Torus (StrothTypeIndex.t100 m).k) =
      Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 1] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.b]
  rw [h, thetaT_ofInt]
  have h2 : thetaM m *ᵥ (![0, 0, 1] : Fin 3 → ℤ) = ![0, 0, 2 + (2 : ℤ) ^ m] := by
    funext i
    fin_cases i <;> simp [thetaM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [h2, Torus.ofInt_eq_zsmul_gens]
  rw [← h]
  simp

theorem ofMul_eq_gens_zsmul (Z : StrothDatum X) (d : Z.D) :
    ∃ i j l : ℤ, Additive.ofMul d =
      i • Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩ +
      j • Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩ +
      l • Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩ := by
  obtain ⟨i, j, l, hd⟩ := Z.dataD.exists_zpow_c_a_b d
  refine ⟨i, j, l, ?_⟩
  rw [hd]
  apply Z.dataD.e.injective
  simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul, Z.dataD.e_c, Z.dataD.e_a,
    Z.dataD.e_b]

theorem thetaD_torus_eq_t100 (Z : StrothDatum X) {m : ℕ} (hτ : Z.τ = StrothTypeIndex.t100 m)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ∀ d : Z.D,
      (letI := Z.dataD
       Z.dataD.e (Additive.ofMul (thetaD Z s (hF hsF) d))) =
      thetaType Z.τ (Z.dataD.e (Additive.ofMul d)) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X := ⟨D, hAD, hDS, StrothTypeIndex.t100 m, dataD, hL, hcentS⟩ with hZ'
  obtain ⟨hφc, hφa, hφb, hφsq⟩ :=
    deviation_form_diag Z' hk hrel (m := m) rfl F hDF hF hN hidx hcent hsF hsD
  have hs : s ∈ Z'.centralizerInMho := hF hsF
  have hΦc : deviationTorus Z' s hs (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩) = 0 := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z' s hs (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩)).toMul : G),
        omegaIn_le 1 Z'.D (deviation Z' s hs (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩)).toMul.2⟩ : Z'.D) = 1 :=
      Subtype.ext hφc
    rw [h1]
    simp
  have hΦa : deviationTorus Z' s hs (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩) =
      (2 : ℤ) ^ m • (Torus.a : Torus Z'.τ.k) := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z' s hs (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)).toMul : G),
        omegaIn_le 1 Z'.D (deviation Z' s hs (Additive.ofMul ⟨Z'.dataD.a, Z'.dataD.a.2⟩)).toMul.2⟩ : Z'.D) =
        Z'.dataD.a ^ (2 ^ m) := Subtype.ext hφa
    rw [h1, Z'.dataD.e_pow, Z'.dataD.e_a]
    rw [show ((2 : ℕ) ^ m) • (Torus.a : Torus Z'.τ.k) = ((2 : ℤ) ^ m) • Torus.a from by
      rw [← natCast_zsmul]
      norm_num]
  have hΦb : deviationTorus Z' s hs (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩) =
      (2 : ℤ) ^ m • (Torus.b : Torus Z'.τ.k) := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z' s hs (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩)).toMul : G),
        omegaIn_le 1 Z'.D (deviation Z' s hs (Additive.ofMul ⟨Z'.dataD.b, Z'.dataD.b.2⟩)).toMul.2⟩ : Z'.D) =
        Z'.dataD.b ^ (2 ^ m) := Subtype.ext hφb
    rw [h1, Z'.dataD.e_pow, Z'.dataD.e_b]
    rw [show ((2 : ℕ) ^ m) • (Torus.b : Torus Z'.τ.k) = ((2 : ℤ) ^ m) • Torus.b from by
      rw [← natCast_zsmul]
      norm_num]
  intro d
  obtain ⟨i, j, l, hd⟩ := ofMul_eq_gens_zsmul Z' d
  have hV : Z'.dataD.e (Additive.ofMul d) =
      i • (Torus.c : Torus Z'.τ.k) + j • (Torus.a : Torus Z'.τ.k) +
        l • (Torus.b : Torus Z'.τ.k) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      Z'.dataD.e_c, Z'.dataD.e_a, Z'.dataD.e_b]
  have hΦd : deviationTorus Z' s hs (Additive.ofMul d) =
      j • ((2 : ℤ) ^ m • (Torus.a : Torus Z'.τ.k)) +
        l • ((2 : ℤ) ^ m • (Torus.b : Torus Z'.τ.k)) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hΦc, hΦa, hΦb]
    simp
  have hLHS : Z'.dataD.e (Additive.ofMul (thetaD Z' s hs d)) =
      (2 : ℤ) • Z'.dataD.e (Additive.ofMul d) + deviationTorus Z' s hs (Additive.ofMul d) := by
    have heq : Additive.ofMul d + Additive.ofMul d +
        Additive.ofMul ⟨((deviation Z' s hs (Additive.ofMul d)).toMul : G),
          omegaIn_le 1 Z'.D (deviation Z' s hs (Additive.ofMul d)).toMul.2⟩ =
        Additive.ofMul (thetaD Z' s hs d) := by
      rw [show thetaD Z' s hs d = d * d *
          ⟨((deviation Z' s hs (Additive.ofMul d)).toMul : G),
            omegaIn_le 1 Z'.D (deviation Z' s hs (Additive.ofMul d)).toMul.2⟩ from rfl,
        ofMul_mul, ofMul_mul]
    rw [← heq, map_add, map_add, two_zsmul, ← deviationTorus_apply]
  rw [hLHS, hV, hΦd]
  have hRHS : thetaType Z'.τ (i • (Torus.c : Torus Z'.τ.k) + j • (Torus.a : Torus Z'.τ.k) +
      l • (Torus.b : Torus Z'.τ.k)) =
      i • ((2 : ℤ) • (Torus.c : Torus Z'.τ.k)) +
        j • ((2 + (2 : ℤ) ^ m) • (Torus.a : Torus Z'.τ.k)) +
        l • ((2 + (2 : ℤ) ^ m) • (Torus.b : Torus Z'.τ.k)) := by
    have hc : thetaType Z'.τ (Torus.c : Torus Z'.τ.k) = (2 : ℤ) • Torus.c := by
      change thetaT m (Torus.c : Torus (StrothTypeIndex.t100 m).k) = 2 • Torus.c
      exact thetaT_c m
    have ha : thetaType Z'.τ (Torus.a : Torus Z'.τ.k) =
        (2 + (2 : ℤ) ^ m) • Torus.a := by
      change thetaT m (Torus.a : Torus (StrothTypeIndex.t100 m).k) = (2 + 2 ^ m) • Torus.a
      exact thetaT_a m
    have hb : thetaType Z'.τ (Torus.b : Torus Z'.τ.k) =
        (2 + (2 : ℤ) ^ m) • Torus.b := by
      change thetaT m (Torus.b : Torus (StrothTypeIndex.t100 m).k) = (2 + 2 ^ m) • Torus.b
      exact thetaT_b m
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hc, ha, hb]
  rw [hRHS]
  module

theorem theta_eq_matAct_sub_of_conj_t100 (Z : StrothDatum X) (m : ℕ)
    (hk : ∀ i, 2 ≤ Z.τ.k i)
    (e : Additive Z.D ≃+ Torus (StrothTypeIndex.t100 m).k) {s l : G}
    (hs : s ∈ Z.centralizerInMho) (hsqD : s * s ∈ Z.D)
    (hlN : l ∈ Subgroup.normalizer (Z.D : Set G))
    (M : IntMat) (hM : Compat (StrothTypeIndex.t100 m).k M)
    (hconj : ∀ d : Z.D, e (Additive.ofMul (conjBy hlN d)) =
      matAct (StrothTypeIndex.t100 m).k M hM (e (Additive.ofMul d)))
    (hform : ∀ d : Z.D, e (Additive.ofMul (thetaD Z s hs d)) =
      thetaT m (e (Additive.ofMul d)))
    {d : Z.D} (h : l⁻¹ * s * l = s * (d : G)) :
    thetaT m (e (Additive.ofMul d)) =
      matAct (StrothTypeIndex.t100 m).k M hM (e (Additive.ofMul ⟨s * s, hsqD⟩)) -
        e (Additive.ofMul ⟨s * s, hsqD⟩) := by
  let q : Z.D := ⟨s * s, hsqD⟩
  have hconjq : conjBy hlN q = q * thetaD Z s hs d := by
    apply Subtype.ext
    dsimp [conjBy, q]
    rw [show l⁻¹ * (s * s) * l = (l⁻¹ * s * l) * (l⁻¹ * s * l) by group]
    rw [h]
    exact sq_mul_eq_sq_mul_thetaD Z hk hs d.2
  have heq : matAct (StrothTypeIndex.t100 m).k M hM (e (Additive.ofMul q)) =
      e (Additive.ofMul q) + thetaT m (e (Additive.ofMul d)) := by
    calc matAct (StrothTypeIndex.t100 m).k M hM (e (Additive.ofMul q))
        = e (Additive.ofMul (conjBy hlN q)) := (hconj q).symm
      _ = e (Additive.ofMul (q * thetaD Z s hs d)) := by rw [hconjq]
      _ = e (Additive.ofMul q) + e (Additive.ofMul (thetaD Z s hs d)) := by
        rw [ofMul_mul, map_add]
      _ = e (Additive.ofMul q) + thetaT m (e (Additive.ofMul d)) := by rw [hform]
  rw [heq]
  abel

theorem thetaD_additive_torus (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) :
    Z.dataD.e (Additive.ofMul (thetaD Z s hs d)) =
      (2 : ℤ) • Z.dataD.e (Additive.ofMul d) + deviationTorus Z s hs (Additive.ofMul d) := by
  have heq : Additive.ofMul d + Additive.ofMul d +
      Additive.ofMul ⟨((deviation Z s hs (Additive.ofMul d)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul d)).toMul.2⟩ =
      Additive.ofMul (thetaD Z s hs d) := by
    rw [show thetaD Z s hs d = d * d *
        ⟨((deviation Z s hs (Additive.ofMul d)).toMul : G),
          omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul d)).toMul.2⟩ from rfl,
      ofMul_mul, ofMul_mul]
  rw [← heq, map_add, map_add, two_zsmul, ← deviationTorus_apply]

theorem thetaD_inv (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho) (d : Z.D) :
    thetaD Z s hs d⁻¹ = (thetaD Z s hs d)⁻¹ := by
  apply Additive.ofMul.injective
  apply Z.dataD.e.injective
  simp only [thetaD_additive_torus, ofMul_inv, map_neg]
  abel

theorem exists_sq_eq_c_of_index_two_of_centOmega_t100_sq (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t100 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) :
    ∃ s ∈ F, s ∉ Z.D ∧ s * s = (Z.dataD.c : G) := by
  classical
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X := ⟨D, hAD, hDS, StrothTypeIndex.t100 m, dataD, hL, hcentS⟩ with hZ'
  obtain ⟨s0, hs0F, hs0D, hs0sqD⟩ := exists_sq_mem_D_of_index_two Z' hk F hF hidx
  have hs : s0 ∈ Z'.centralizerInMho := hF hs0F
  have hform := thetaD_torus_eq_t100 Z' (m := m) rfl hk hrel F hDF hF hN hidx hcent hs0F hs0D
  have huL : Z'.dataD.u ∈ X.L := hL ▸ Z'.dataD.u_mem_L
  have htL : Z'.dataD.t ∈ X.L := hL ▸ Z'.dataD.t_mem_L
  have huvL : Z'.dataD.uv ∈ X.L := hL ▸ Z'.dataD.uv_mem_L
  have hρL : Z'.dataD.ρ ∈ X.L := hL ▸ Z'.dataD.ρ_mem_L
  obtain ⟨du, hduD, hdu⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D huL
  obtain ⟨dt, hdtD, hdt⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D htL
  obtain ⟨duv, hduvD, hduv⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D huvL
  obtain ⟨dρ, hdρD, hdρ⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D hρL
  have hmat_uv : ∀ y : Z'.D, Z'.dataD.e (Additive.ofMul (conjBy Z'.dataD.uv_mem y)) =
      matAct (StrothTypeIndex.t100 m).k Type100.uvM (t100_compat_uv m)
        (Z'.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z'.dataD.uv_conj]
    rfl
  have hmat_t : ∀ y : Z'.D, Z'.dataD.e (Additive.ofMul (conjBy Z'.dataD.t_mem y)) =
      matAct (StrothTypeIndex.t100 m).k Type100.tM (t100_compat_t m)
        (Z'.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z'.dataD.t_conj]
    rfl
  have hmat_u : ∀ y : Z'.D, Z'.dataD.e (Additive.ofMul (conjBy Z'.dataD.u_mem y)) =
      matAct (StrothTypeIndex.t100 m).k Type100.uM (t100_compat_u m)
        (Z'.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z'.dataD.u_conj]
    rfl
  have hmat_ρ : ∀ y : Z'.D, Z'.dataD.e (Additive.ofMul (conjBy Z'.dataD.ρ_mem y)) =
      matAct (StrothTypeIndex.t100 m).k Type100.ρM (t100_compat_rho m)
        (Z'.dataD.e (Additive.ofMul y)) := by
    intro y
    rw [Z'.dataD.ρ_conj]
    rfl
  have hcond_uv : ∃ d : Torus (StrothTypeIndex.t100 m).k,
      thetaType Z'.τ d = matAct (StrothTypeIndex.t100 m).k Type100.uvM (t100_compat_uv m)
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨duv, hduvD⟩), theta_eq_matAct_sub_of_conj_t100 Z' m hk
      Z'.dataD.e hs hs0sqD Z'.dataD.uv_mem Type100.uvM (t100_compat_uv m) hmat_uv
      (fun d => hform d) (d := ⟨duv, hduvD⟩) (by simpa using hduv)⟩
  have hcond_t : ∃ d : Torus (StrothTypeIndex.t100 m).k,
      thetaType Z'.τ d = matAct (StrothTypeIndex.t100 m).k Type100.tM (t100_compat_t m)
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨dt, hdtD⟩), theta_eq_matAct_sub_of_conj_t100 Z' m hk
      Z'.dataD.e hs hs0sqD Z'.dataD.t_mem Type100.tM (t100_compat_t m) hmat_t
      (fun d => hform d) (d := ⟨dt, hdtD⟩) (by simpa using hdt)⟩
  have hcond_u : ∃ d : Torus (StrothTypeIndex.t100 m).k,
      thetaType Z'.τ d = matAct (StrothTypeIndex.t100 m).k Type100.uM (t100_compat_u m)
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨du, hduD⟩), theta_eq_matAct_sub_of_conj_t100 Z' m hk
      Z'.dataD.e hs hs0sqD Z'.dataD.u_mem Type100.uM (t100_compat_u m) hmat_u
      (fun d => hform d) (d := ⟨du, hduD⟩) (by simpa using hdu)⟩
  have hcond_ρ : ∃ d : Torus (StrothTypeIndex.t100 m).k,
      thetaType Z'.τ d = matAct (StrothTypeIndex.t100 m).k Type100.ρM (t100_compat_rho m)
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨dρ, hdρD⟩), theta_eq_matAct_sub_of_conj_t100 Z' m hk
      Z'.dataD.e hs hs0sqD Z'.dataD.ρ_mem Type100.ρM (t100_compat_rho m) hmat_ρ
      (fun d => hform d) (d := ⟨dρ, hdρD⟩) (by simpa using hdρ)⟩
  have hdich := square_class_dichotomy_uniform Z'.τ hk hrel
    (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) hcond_uv hcond_t hcond_u hcond_ρ
  rcases hdich with ⟨v, hv⟩ | ⟨v, hv⟩
  ·
    exfalso
    obtain ⟨y, hy⟩ := Z'.dataD.e.surjective v
    set d : Z'.D := Additive.toMul y with hd
    have hed : Z'.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z'.dataD.e (Additive.ofMul (thetaD Z' s0 hs d)) =
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) := by
      rw [hform d, hed]
      exact hv
    set d' : Z'.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z' s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z' hk hs (by exact Z'.D.inv_mem d.2)).symm
    have he : Z'.dataD.e (Additive.ofMul d') = 0 := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd, add_neg_cancel]
    have hz2 : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = 1 := by
      have h1 : d' = 1 := by
        apply Additive.ofMul.injective
        apply Z'.dataD.e.injective
        rw [he]
        simp
      rw [← hsq, h1]
      rfl
    have hzS : s0 * (d : G)⁻¹ ∈ (X.S : Subgroup G) :=
      X.S.mul_mem (hF hs0F).1.1 (X.S.inv_mem (hDS d.2))
    have hzA : s0 * (d : G)⁻¹ ∈ Subgroup.centralizer (X.A : Set G) := by
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.centralizer_le (A_le_mhoOne_of_family_one Z' hk hrel) hs.2
      · refine Subgroup.mem_centralizer_iff.mpr (fun a ha => ?_)
        have haD : a ∈ Z'.D := hAD ha
        have hcomm : a * (d : G) = (d : G) * a :=
          congrArg Subtype.val (Z'.dataD.isMulCommutative.is_comm.comm ⟨a, haD⟩ ⟨d, d.2⟩)
        exact (show Commute a (d : G) from hcomm).inv_right.eq
    have hzA' : s0 * (d : G)⁻¹ ∈ X.A := X.hH _ hzS hz2 hzA
    have hzD : s0 * (d : G)⁻¹ ∈ Z'.D := hAD hzA'
    exact hs0D (by
      have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
      rw [this]
      exact Z'.D.mul_mem hzD d.2)
  ·
    obtain ⟨y, hy⟩ := Z'.dataD.e.surjective v
    set d : Z'.D := Additive.toMul y with hd
    have hed : Z'.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z'.dataD.e (Additive.ofMul (thetaD Z' s0 hs d)) =
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) - Torus.c := by
      rw [hform d, hed]
      exact hv
    set d' : Z'.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z' s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z' hk hs (by exact Z'.D.inv_mem d.2)).symm
    have he : Z'.dataD.e (Additive.ofMul d') =
        Z'.dataD.e (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩) := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd,
        Z'.dataD.e_c]
      abel
    have hsqc : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = (Z'.dataD.c : G) := by
      have h1 : d' = ⟨Z'.dataD.c, Z'.dataD.c.2⟩ := by
        apply Additive.ofMul.injective
        apply Z'.dataD.e.injective
        rw [he]
      rw [← hsq, h1]
    refine ⟨s0 * (d : G)⁻¹, F.mul_mem hs0F (F.inv_mem (hDF d.2)), ?_, hsqc⟩
    intro hmem
    apply hs0D
    have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
    rw [this]
    exact Z'.D.mul_mem hmem d.2

end CFSG.CGT.Stroth77

end
