module

public import CFSG.CGT.Stroth77.Extension212Lift

public section

namespace CFSG.CGT.Stroth77

variable {K : Fin 3 → ℕ}

theorem odd_of_cast_two {e : ℤ} (h : ((e : ℤ) : ZMod 2) = 1) : Odd e := by
  rcases Int.even_or_odd e with he | he
  · obtain ⟨w, rfl⟩ := he
    push_cast at h
    rw [← two_mul] at h
    exact absurd h (by rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]; decide)
  · exact he

theorem even_of_cast_two {e : ℤ} (h : ((e : ℤ) : ZMod 2) = 0) : Even e := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact even_iff_two_dvd.mpr (by exact_mod_cast h)

theorem iV_cast_two (n : ℕ) : ((Type120.iV n : ℤ) : ZMod 2) = 1 := by
  have h := congrArg (fun z : ℤ => (z : ZMod 2)) (Type120.three_mul_iV n)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_one] at h
  rw [show (3 : ZMod 2) = 1 from rfl, show (2 : ZMod 2) = 0 from rfl, one_mul,
    zero_pow (by omega), zero_add] at h
  exact h

theorem FV_cast_two {n : ℕ} (hn : 1 ≤ n) : ((Type120.FV n : ℤ) : ZMod 2) = 1 := by
  have h := congrArg (fun z : ℤ => (z : ZMod 2)) (Type120.three_mul_FV n)
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one] at h
  rw [show (3 : ZMod 2) = 1 from rfl, show (4 : ZMod 2) = 0 from rfl, one_mul,
    zero_pow (by omega), zero_sub] at h
  rw [h]
  rfl

theorem GV_cast_two {n : ℕ} (hn : 2 ≤ n) : ((Type120.GV n : ℤ) : ZMod 2) = 1 := by
  have h := congrArg (fun z : ℤ => (z : ZMod 2)) (Type120.three_mul_GV n)
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat] at h
  rw [show (3 : ZMod 2) = 1 from rfl, show (4 : ZMod 2) = 0 from rfl, one_mul,
    zero_pow (by omega), zero_sub] at h
  rw [h]
  rfl

theorem FV_cast_two_succ (n : ℕ) : ((Type120.FV (n + 1) : ℤ) : ZMod 2) = 1 :=
  FV_cast_two (by omega)

theorem GV_cast_two_add_two (n : ℕ) : ((Type120.GV (n + 2) : ℤ) : ZMod 2) = 1 :=
  GV_cast_two (by omega)

theorem two_dvd_one_sub_of_odd {e : ℤ} (h : Odd e) : (2 : ℤ) ∣ 1 - e := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by ring⟩

theorem two_dvd_zero_sub_of_even {e : ℤ} (h : Even e) : (2 : ℤ) ∣ 0 - e := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by ring⟩

section Forms

variable {M : IntMat} (hM : Compat K M) (j : Fin 3)

theorem form2_odd (h : Odd (M 0 j)) :
    ∃ x y z : ℤ, matAct K M hM (gen K j) = (2 * x + 1) • gen K 0 + y • gen K 1 + z • gen K 2 := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, M 1 j, M 2 j, by rw [matAct_gen_eq, hx]⟩

theorem form2_even (h : Even (M 0 j)) :
    ∃ x y z : ℤ, matAct K M hM (gen K j) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2 := by
  obtain ⟨x, hx⟩ := even_iff_two_dvd.mp h
  exact ⟨x, M 1 j, M 2 j, by rw [matAct_gen_eq, hx]⟩

theorem form4_ee (h1 : Even (M 1 j)) (h2 : Even (M 2 j)) :
    ∃ x y z : ℤ, matAct K M hM (gen K j) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z) • gen K 2 := by
  obtain ⟨y, hy⟩ := even_iff_two_dvd.mp h1
  obtain ⟨z, hz⟩ := even_iff_two_dvd.mp h2
  exact ⟨M 0 j, y, z, by rw [matAct_gen_eq, hy, hz]⟩

theorem form4_oe (h1 : Odd (M 1 j)) (h2 : Even (M 2 j)) :
    ∃ x y z : ℤ,
      matAct K M hM (gen K j) = x • gen K 0 + (2 * y + 1) • gen K 1 + (2 * z) • gen K 2 := by
  obtain ⟨y, hy⟩ := h1
  obtain ⟨z, hz⟩ := even_iff_two_dvd.mp h2
  exact ⟨M 0 j, y, z, by rw [matAct_gen_eq, hy, hz]⟩

theorem form4_eo (h1 : Even (M 1 j)) (h2 : Odd (M 2 j)) :
    ∃ x y z : ℤ,
      matAct K M hM (gen K j) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z + 1) • gen K 2 := by
  obtain ⟨y, hy⟩ := even_iff_two_dvd.mp h1
  obtain ⟨z, hz⟩ := h2
  exact ⟨M 0 j, y, z, by rw [matAct_gen_eq, hy, hz]⟩

theorem form4_oo (h1 : Odd (M 1 j)) (h2 : Odd (M 2 j)) :
    ∃ x y z : ℤ,
      matAct K M hM (gen K j) = x • gen K 0 + (2 * y + 1) • gen K 1 + (2 * z + 1) • gen K 2 := by
  obtain ⟨y, hy⟩ := h1
  obtain ⟨z, hz⟩ := h2
  exact ⟨M 0 j, y, z, by rw [matAct_gen_eq, hy, hz]⟩

end Forms

theorem matAct_invGen_const {e : ℕ} (hK : ∀ i, K i = e + 1) {M : IntMat} (hM : Compat K M)
    (j : Fin 3) : matAct K M hM (invGen K j) = tw K (M 0 j) (M 1 j) (M 2 j) := by
  rw [invGen, map_zsmul, matAct_gen_eq, tw, invGen, invGen, invGen, hK, hK, hK, hK,
    Nat.add_sub_cancel]
  module

theorem matAct_invGen_idx4_zero {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hK : K = ![k, n, n])
    {M : IntMat} (hM : Compat K M) {μ₁ μ₂ : ℤ} (h1 : M 1 0 = 2 ^ (n - k) * μ₁)
    (h2 : M 2 0 = 2 ^ (n - k) * μ₂) :
    matAct K M hM (invGen K 0) = tw K (M 0 0) μ₁ μ₂ := by
  subst hK
  rw [invGen, map_zsmul, matAct_gen_eq, tw, invGen, invGen, invGen, h1, h2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [show n - 1 = (k - 1) + (n - k) by omega, pow_add]
  module

theorem matAct_invGen_idx4_succ {k n : ℕ} (hkn : k + 1 ≤ n) (hK : K = ![k, n, n])
    {M : IntMat} (hM : Compat K M) (j : Fin 3) (hj : K j = n) :
    matAct K M hM (invGen K j) = tw K 0 (M 1 j) (M 2 j) := by
  subst hK
  have h0 : ((2 : ℤ) ^ (n - 1) * M 0 j) • gen ![k, n, n] 0 = 0 := by
    have hc := two_pow_zsmul_gen ![k, n, n] 0
    simp only [Matrix.cons_val_zero] at hc
    rw [show (2 : ℤ) ^ (n - 1) * M 0 j = (2 ^ (n - 1 - k) * M 0 j) * 2 ^ k by
      rw [mul_comm _ ((2 : ℤ) ^ k), ← mul_assoc, ← pow_add, show k + (n - 1 - k) = n - 1 by omega],
      mul_smul, hc, smul_zero]
  rw [invGen, map_zsmul, matAct_gen_eq, tw, invGen, invGen, invGen, hj]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, smul_add, smul_smul, zero_smul, zero_add, h0]
  module

theorem map_tw_of_invGen (a : Torus K →+ Torus K) {a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℤ}
    (h0 : a (invGen K 0) = tw K a0 b0 c0) (h1 : a (invGen K 1) = tw K a1 b1 c1)
    (h2 : a (invGen K 2) = tw K a2 b2 c2) (x y z : ℤ) :
    a (tw K x y z) = tw K (x * a0 + y * a1 + z * a2) (x * b0 + y * b1 + z * b2)
      (x * c0 + y * c1 + z * c2) := by
  conv_lhs => rw [tw]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0, h1, h2, zsmul_tw, zsmul_tw,
    zsmul_tw, tw_add, tw_add]

theorem matAct_gen_eq_add_tw {M M' : IntMat} (hM : Compat K M) (hM' : Compat K M') (j : Fin 3)
    (Δ₀ Δ₁ Δ₂ : ℤ) (h0 : (2 : ℤ) ^ K 0 ∣ (M 0 j + Δ₀ * 2 ^ (K 0 - 1)) - M' 0 j)
    (h1 : (2 : ℤ) ^ K 1 ∣ (M 1 j + Δ₁ * 2 ^ (K 1 - 1)) - M' 1 j)
    (h2 : (2 : ℤ) ^ K 2 ∣ (M 2 j + Δ₂ * 2 ^ (K 2 - 1)) - M' 2 j) :
    matAct K M' hM' (gen K j) = matAct K M hM (gen K j) + tw K Δ₀ Δ₁ Δ₂ := by
  rw [matAct_gen_eq, matAct_gen_eq, tw, invGen, invGen, invGen, smul_smul, smul_smul, smul_smul]
  have e : M 0 j • gen K 0 + M 1 j • gen K 1 + M 2 j • gen K 2 +
      ((Δ₀ * 2 ^ (K 0 - 1)) • gen K 0 + (Δ₁ * 2 ^ (K 1 - 1)) • gen K 1 +
        (Δ₂ * 2 ^ (K 2 - 1)) • gen K 2) =
      (M 0 j + Δ₀ * 2 ^ (K 0 - 1)) • gen K 0 + (M 1 j + Δ₁ * 2 ^ (K 1 - 1)) • gen K 1 +
        (M 2 j + Δ₂ * 2 ^ (K 2 - 1)) • gen K 2 := by
    simp only [add_zsmul]
    abel
  rw [e]
  exact zsmul_gens_eq_of_dvd h0 h1 h2

theorem matAct_gen_eq_of_dvd {M M' : IntMat} (hM : Compat K M) (hM' : Compat K M') (j : Fin 3)
    (h0 : (2 : ℤ) ^ K 0 ∣ M 0 j - M' 0 j) (h1 : (2 : ℤ) ^ K 1 ∣ M 1 j - M' 1 j)
    (h2 : (2 : ℤ) ^ K 2 ∣ M 2 j - M' 2 j) :
    matAct K M' hM' (gen K j) = matAct K M hM (gen K j) := by
  have h := matAct_gen_eq_add_tw hM hM' j 0 0 0 (by simpa using h0) (by simpa using h1)
    (by simpa using h2)
  rwa [tw_zero, add_zero] at h

theorem exists_two_nsmul_eq_iff (hk : ∀ i, 1 ≤ K i) (p q r : ℤ) :
    (∃ w : Torus K, 2 • w = p • gen K 0 + q • gen K 1 + r • gen K 2) ↔
      Even p ∧ Even q ∧ Even r := by
  have e : p • gen K 0 + q • gen K 1 + r • gen K 2 = Torus.ofInt K ![p, q, r] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    rfl
  rw [e]
  have h := Torus.exists_two_zsmul_eq_iff hk ![p, q, r]
  constructor
  · rintro ⟨w, hw⟩
    have h' := h.1 ⟨w, by rw [← hw, ← natCast_zsmul]; rfl⟩
    exact ⟨h' 0, h' 1, h' 2⟩
  · rintro ⟨hp, hq, hr⟩
    obtain ⟨w, hw⟩ := h.2 (fun i => by fin_cases i <;> assumption)
    exact ⟨w, by rw [← hw, ← natCast_zsmul]; rfl⟩

theorem two_dvd_sub_of_cast {e q : ℤ} (h : ((e : ℤ) : ZMod 2) = (q : ZMod 2)) : (2 : ℤ) ∣ q - e :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub e q 2).mp h

@[expose] def parUV : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 1, 0, 1]
@[expose] def parT : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 1, 1, 0; 0, 0, 1]
@[expose] def parU : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
@[expose] def parR : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

section ProfileConst

variable {e : ℕ} (hK : ∀ i, K i = e + 1)

include hK in
theorem map_tw_of_par_const {M : IntMat} (hM : Compat K M) {P : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hP : M.map (Int.cast : ℤ → ZMod 2) = P) {p00 p10 p20 p01 p11 p21 p02 p12 p22 : ℤ}
    (h00 : P 0 0 = p00) (h10 : P 1 0 = p10) (h20 : P 2 0 = p20) (h01 : P 0 1 = p01)
    (h11 : P 1 1 = p11) (h21 : P 2 1 = p21) (h02 : P 0 2 = p02) (h12 : P 1 2 = p12)
    (h22 : P 2 2 = p22) (x y z : ℤ) :
    matAct K M hM (tw K x y z) = tw K (x * p00 + y * p01 + z * p02)
      (x * p10 + y * p11 + z * p12) (x * p20 + y * p21 + z * p22) := by
  have hk : ∀ i, 1 ≤ K i := fun i => by rw [hK]; omega
  have c : ∀ a b, ((M a b : ℤ) : ZMod 2) = P a b := fun a b => by
    rw [← hP, Matrix.map_apply]
  refine map_tw_of_invGen _ ?_ ?_ ?_ x y z
  · rw [matAct_invGen_const hK]
    exact tw_congr hk (two_dvd_sub_of_cast (by rw [c, h00])) (two_dvd_sub_of_cast (by rw [c, h10]))
      (two_dvd_sub_of_cast (by rw [c, h20]))
  · rw [matAct_invGen_const hK]
    exact tw_congr hk (two_dvd_sub_of_cast (by rw [c, h01])) (two_dvd_sub_of_cast (by rw [c, h11]))
      (two_dvd_sub_of_cast (by rw [c, h21]))
  · rw [matAct_invGen_const hK]
    exact tw_congr hk (two_dvd_sub_of_cast (by rw [c, h02])) (two_dvd_sub_of_cast (by rw [c, h12]))
      (two_dvd_sub_of_cast (by rw [c, h22]))

include hK in
theorem profile2_of_par_const (A : SigmaFourAction K)
    (hV : A.uv.map (Int.cast : ℤ → ZMod 2) = parUV) (hW : A.t.map (Int.cast : ℤ → ZMod 2) = parT)
    (hU : A.u.map (Int.cast : ℤ → ZMod 2) = parU) (hR : A.ρ.map (Int.cast : ℤ → ZMod 2) = parR) :
    Profile2 K A.φuv A.φt A.φu A.φρ := by
  have hk : ∀ i, 1 ≤ K i := fun i => by rw [hK]; omega
  have cV : ∀ a b, ((A.uv a b : ℤ) : ZMod 2) = parUV a b := fun a b => by
    rw [← hV, Matrix.map_apply]
  have cW : ∀ a b, ((A.t a b : ℤ) : ZMod 2) = parT a b := fun a b => by
    rw [← hW, Matrix.map_apply]
  have cU : ∀ a b, ((A.u a b : ℤ) : ZMod 2) = parU a b := fun a b => by
    rw [← hU, Matrix.map_apply]
  have cR : ∀ a b, ((A.ρ a b : ℤ) : ZMod 2) = parR a b := fun a b => by
    rw [← hR, Matrix.map_apply]
  have odd_of {e : ℤ} (h : ((e : ℤ) : ZMod 2) = 1) : Odd e := odd_of_cast_two h
  have even_of {e : ℤ} (h : ((e : ℤ) : ZMod 2) = 0) : Even e := even_of_cast_two h
  refine ⟨fun x y z => ?_, fun x y z => ?_, fun x y z => ?_, fun x y z => ?_,
    form2_odd _ _ (odd_of (by rw [cV]; rfl)), form2_even _ _ (even_of (by rw [cV]; rfl)),
    form2_even _ _ (even_of (by rw [cV]; rfl)), form2_odd _ _ (odd_of (by rw [cW]; rfl)),
    form2_even _ _ (even_of (by rw [cW]; rfl)), form2_even _ _ (even_of (by rw [cW]; rfl)),
    form2_odd _ _ (odd_of (by rw [cU]; rfl)), form2_even _ _ (even_of (by rw [cU]; rfl)),
    form2_even _ _ (even_of (by rw [cU]; rfl)), form2_odd _ _ (odd_of (by rw [cR]; rfl)),
    form2_even _ _ (even_of (by rw [cR]; rfl)), form2_even _ _ (even_of (by rw [cR]; rfl))⟩
  · rw [map_tw_of_par_const hK A.compat_uv hV (p00 := 1) (p10 := 1) (p20 := 1) (p01 := 0)
      (p11 := 1) (p21 := 0) (p02 := 0) (p12 := 0) (p22 := 1) rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    exact tw_congr hk (by omega) (by omega) (by omega)
  · rw [map_tw_of_par_const hK A.compat_t hW (p00 := 1) (p10 := 1) (p20 := 0) (p01 := 0)
      (p11 := 1) (p21 := 0) (p02 := 0) (p12 := 0) (p22 := 1) rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    exact tw_congr hk (by omega) (by omega) (by omega)
  · rw [map_tw_of_par_const hK A.compat_u hU (p00 := 1) (p10 := 0) (p20 := 0) (p01 := 0)
      (p11 := 0) (p21 := 1) (p02 := 0) (p12 := 1) (p22 := 0) rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    exact tw_congr hk (by omega) (by omega) (by omega)
  · rw [map_tw_of_par_const hK A.compat_ρ hR (p00 := 1) (p10 := 0) (p20 := 0) (p01 := 0)
      (p11 := 0) (p21 := 1) (p02 := 0) (p12 := 1) (p22 := 1) rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    exact tw_congr hk (by omega) (by omega) (by omega)

end ProfileConst

theorem two_dvd_lin {p q r a b c : ℤ} (ha : (2 : ℤ) ∣ a - p) (hb : (2 : ℤ) ∣ b - q)
    (hc : (2 : ℤ) ∣ c - r) (x y z : ℤ) :
    (2 : ℤ) ∣ (x * a + y * b + z * c) - (x * p + y * q + z * r) := by
  have := dvd_add (dvd_add (ha.mul_left x) (hb.mul_left y)) (hc.mul_left z)
  convert this using 1
  ring

section ProfileFour

variable {k n : ℕ} (hK : K = ![k, n, n]) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)

include hK hk hkn in
theorem map_tw_idx4 {M : IntMat} (hM : Compat K M) {μ₁ μ₂ : ℤ} (h1 : M 1 0 = 2 ^ (n - k) * μ₁)
    (h2 : M 2 0 = 2 ^ (n - k) * μ₂) (x y z : ℤ) :
    matAct K M hM (tw K x y z) = tw K (x * M 0 0 + y * 0 + z * 0)
      (x * μ₁ + y * M 1 1 + z * M 1 2) (x * μ₂ + y * M 2 1 + z * M 2 2) := by
  have hK1 : K 1 = n := by subst hK; rfl
  have hK2 : K 2 = n := by subst hK; rfl
  exact map_tw_of_invGen _ (matAct_invGen_idx4_zero hk (by omega) hK hM h1 h2)
    (matAct_invGen_idx4_succ hkn hK hM 1 hK1) (matAct_invGen_idx4_succ hkn hK hM 2 hK2) x y z

include hK hk hkn in
theorem profile4_of_par (A : SigmaFourAction K)
    (hV : Odd (A.uv 0 0) ∧ Odd (A.uv 1 1) ∧ Even (A.uv 2 1) ∧ Even (A.uv 1 2) ∧ Odd (A.uv 2 2))
    (hW : Odd (A.t 0 0) ∧ Odd (A.t 1 1) ∧ Even (A.t 2 1) ∧ Even (A.t 1 2) ∧ Odd (A.t 2 2))
    (hU : Odd (A.u 0 0) ∧ Even (A.u 1 1) ∧ Odd (A.u 2 1) ∧ Odd (A.u 1 2) ∧ Even (A.u 2 2))
    (hR : Odd (A.ρ 0 0) ∧ Even (A.ρ 1 1) ∧ Odd (A.ρ 2 1) ∧ Odd (A.ρ 1 2) ∧ Odd (A.ρ 2 2))
    (μV : ∃ μ₁ μ₂ : ℤ, A.uv 1 0 = 2 ^ (n - k) * μ₁ ∧ A.uv 2 0 = 2 ^ (n - k) * μ₂ ∧ Odd μ₁ ∧
      Odd μ₂)
    (μW : ∃ μ₁ μ₂ : ℤ, A.t 1 0 = 2 ^ (n - k) * μ₁ ∧ A.t 2 0 = 2 ^ (n - k) * μ₂ ∧ Odd μ₁ ∧
      Even μ₂)
    (μU : ∃ μ₁ μ₂ : ℤ, A.u 1 0 = 2 ^ (n - k) * μ₁ ∧ A.u 2 0 = 2 ^ (n - k) * μ₂ ∧ Even μ₁ ∧
      Even μ₂)
    (μR : ∃ μ₁ μ₂ : ℤ, A.ρ 1 0 = 2 ^ (n - k) * μ₁ ∧ A.ρ 2 0 = 2 ^ (n - k) * μ₂ ∧ Even μ₁ ∧
      Even μ₂) :
    Profile4 K A.φuv A.φt A.φu A.φρ := by
  have hk1 : ∀ i, 1 ≤ K i := by
    subst hK
    intro i; fin_cases i <;> simp <;> omega
  have hnk : 1 ≤ n - k := by omega
  have ev (μ : ℤ) : Even (2 ^ (n - k) * μ) :=
    (Int.even_pow.mpr ⟨even_two, by omega⟩).mul_right μ
  obtain ⟨V00, V11, V21, V12, V22⟩ := hV
  obtain ⟨W00, W11, W21, W12, W22⟩ := hW
  obtain ⟨U00, U11, U21, U12, U22⟩ := hU
  obtain ⟨R00, R11, R21, R12, R22⟩ := hR
  obtain ⟨v1, v2, hv1, hv2, pv1, pv2⟩ := μV
  obtain ⟨w1, w2, hw1, hw2, pw1, pw2⟩ := μW
  obtain ⟨u1, u2, hu1, hu2, pu1, pu2⟩ := μU
  obtain ⟨r1, r2, hr1, hr2, pr1, pr2⟩ := μR
  have o {e : ℤ} (h : Odd e) : (2 : ℤ) ∣ 1 - e := two_dvd_one_sub_of_odd h
  have z {e : ℤ} (h : Even e) : (2 : ℤ) ∣ 0 - e := two_dvd_zero_sub_of_even h
  have even_zero : Even (0 : ℤ) := ⟨0, by ring⟩
  refine ⟨fun x y z' => ?_, fun x y z' => ?_, fun x y z' => ?_, fun x y z' => ?_,
    form4_ee _ _ (by rw [hv1]; exact ev _) (by rw [hv2]; exact ev _), form4_oe _ _ V11 V21,
    form4_eo _ _ V12 V22, form4_ee _ _ (by rw [hw1]; exact ev _) (by rw [hw2]; exact ev _),
    form4_oe _ _ W11 W21, form4_eo _ _ W12 W22,
    form4_ee _ _ (by rw [hu1]; exact ev _) (by rw [hu2]; exact ev _), form4_eo _ _ U11 U21,
    form4_oe _ _ U12 U22, form4_ee _ _ (by rw [hr1]; exact ev _) (by rw [hr2]; exact ev _),
    form4_eo _ _ R11 R21, form4_oo _ _ R12 R22⟩
  · rw [map_tw_idx4 hK hk hkn A.compat_uv hv1 hv2]
    refine tw_congr hk1 ?_ ?_ ?_
    · convert two_dvd_lin (a := 1) (b := 0) (c := 0) (o V00) (z even_zero) (z even_zero) x y z'
        using 1 <;> ring
    · convert two_dvd_lin (a := 1) (b := 1) (c := 0) (o pv1) (o V11) (z V12) x y z' using 1 <;>
        ring
    · convert two_dvd_lin (a := 1) (b := 0) (c := 1) (o pv2) (z V21) (o V22) x y z' using 1 <;>
        ring
  · rw [map_tw_idx4 hK hk hkn A.compat_t hw1 hw2]
    refine tw_congr hk1 ?_ ?_ ?_
    · convert two_dvd_lin (a := 1) (b := 0) (c := 0) (o W00) (z even_zero) (z even_zero) x y z'
        using 1 <;> ring
    · convert two_dvd_lin (a := 1) (b := 1) (c := 0) (o pw1) (o W11) (z W12) x y z' using 1 <;>
        ring
    · convert two_dvd_lin (a := 0) (b := 0) (c := 1) (z pw2) (z W21) (o W22) x y z' using 1 <;>
        ring
  · rw [map_tw_idx4 hK hk hkn A.compat_u hu1 hu2]
    refine tw_congr hk1 ?_ ?_ ?_
    · convert two_dvd_lin (a := 1) (b := 0) (c := 0) (o U00) (z even_zero) (z even_zero) x y z'
        using 1 <;> ring
    · convert two_dvd_lin (a := 0) (b := 0) (c := 1) (z pu1) (z U11) (o U12) x y z' using 1 <;>
        ring
    · convert two_dvd_lin (a := 0) (b := 1) (c := 0) (z pu2) (o U21) (z U22) x y z' using 1 <;>
        ring
  · rw [map_tw_idx4 hK hk hkn A.compat_ρ hr1 hr2]
    refine tw_congr hk1 ?_ ?_ ?_
    · convert two_dvd_lin (a := 1) (b := 0) (c := 0) (o R00) (z even_zero) (z even_zero) x y z'
        using 1 <;> ring
    · convert two_dvd_lin (a := 0) (b := 0) (c := 1) (z pr1) (z R11) (o R12) x y z' using 1 <;>
        ring
    · convert two_dvd_lin (a := 0) (b := 1) (c := 1) (z pr2) (o R21) (o R22) x y z' using 1 <;>
        ring

include hK hk hkn in
theorem profile2_of_par (A : SigmaFourAction K)
    (hV : Odd (A.uv 0 0) ∧ Odd (A.uv 1 1) ∧ Even (A.uv 2 1) ∧ Even (A.uv 1 2) ∧ Odd (A.uv 2 2))
    (hW : Odd (A.t 0 0) ∧ Odd (A.t 1 1) ∧ Even (A.t 2 1) ∧ Even (A.t 1 2) ∧ Odd (A.t 2 2))
    (hU : Odd (A.u 0 0) ∧ Even (A.u 1 1) ∧ Odd (A.u 2 1) ∧ Odd (A.u 1 2) ∧ Even (A.u 2 2))
    (hR : Odd (A.ρ 0 0) ∧ Even (A.ρ 1 1) ∧ Odd (A.ρ 2 1) ∧ Odd (A.ρ 1 2) ∧ Odd (A.ρ 2 2))
    (rV : Even (A.uv 0 1) ∧ Even (A.uv 0 2)) (rW : Even (A.t 0 1) ∧ Even (A.t 0 2))
    (rU : Even (A.u 0 1) ∧ Even (A.u 0 2)) (rR : Even (A.ρ 0 1) ∧ Even (A.ρ 0 2))
    (μV : ∃ μ₁ μ₂ : ℤ, A.uv 1 0 = 2 ^ (n - k) * μ₁ ∧ A.uv 2 0 = 2 ^ (n - k) * μ₂ ∧ Odd μ₁ ∧
      Odd μ₂)
    (μW : ∃ μ₁ μ₂ : ℤ, A.t 1 0 = 2 ^ (n - k) * μ₁ ∧ A.t 2 0 = 2 ^ (n - k) * μ₂ ∧ Odd μ₁ ∧
      Even μ₂)
    (μU : ∃ μ₁ μ₂ : ℤ, A.u 1 0 = 2 ^ (n - k) * μ₁ ∧ A.u 2 0 = 2 ^ (n - k) * μ₂ ∧ Even μ₁ ∧
      Even μ₂)
    (μR : ∃ μ₁ μ₂ : ℤ, A.ρ 1 0 = 2 ^ (n - k) * μ₁ ∧ A.ρ 2 0 = 2 ^ (n - k) * μ₂ ∧ Even μ₁ ∧
      Even μ₂) :
    Profile2 K A.φuv A.φt A.φu A.φρ := by
  have P4 := profile4_of_par hK hk hkn A hV hW hU hR μV μW μU μR
  exact ⟨P4.nV, P4.nW, P4.nU, P4.nR, form2_odd _ _ hV.1, form2_even _ _ rV.1,
    form2_even _ _ rV.2, form2_odd _ _ hW.1, form2_even _ _ rW.1, form2_even _ _ rW.2,
    form2_odd _ _ hU.1, form2_even _ _ rU.1, form2_even _ _ rU.2, form2_odd _ _ hR.1,
    form2_even _ _ rR.1, form2_even _ _ rR.2⟩

end ProfileFour

end CFSG.CGT.Stroth77
