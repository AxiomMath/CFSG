module

public import CFSG.CGT.Stroth77.Section224Deviation

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

@[expose] def thetaM (m : ℕ) : IntMat :=
  Matrix.diagonal ![2, 2 + (2 : ℤ) ^ m, 2 + (2 : ℤ) ^ m]

theorem thetaM_compat (m : ℕ) : Compat (Type100.k m) (thetaM m) := by
  refine Compat.of_witness (C := thetaM m) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaM, Type100.k, Matrix.diagonal, Fin.isValue]

@[expose] def theta (m : ℕ) : Torus (Type100.k m) →+ Torus (Type100.k m) :=
  matAct (Type100.k m) (thetaM m) (thetaM_compat m)

theorem theta_ofInt (m : ℕ) (D : Fin 3 → ℤ) :
    theta m (Torus.ofInt (Type100.k m) D) =
      Torus.ofInt (Type100.k m) (thetaM m *ᵥ D) := by
  rw [theta, matAct_ofInt]

@[expose] def thetaPreInt (m : ℕ) (W : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![W 0, (1 - (2 : ℤ) ^ (m - 1)) * W 1, (1 - (2 : ℤ) ^ (m - 1)) * W 2]

theorem theta_thetaPreInt (m : ℕ) (hm : 2 ≤ m) (W : Fin 3 → ℤ) :
    theta m (Torus.ofInt (Type100.k m) (thetaPreInt m W)) =
      (2 : ℤ) • Torus.ofInt (Type100.k m) W := by
  rw [theta_ofInt, ← Torus.ofInt_zsmul]
  apply Torus.ofInt_eq_ofInt_iff.mpr
  intro i
  rw [thetaM, Matrix.mulVec_diagonal]
  fin_cases i
  · change 2 * W 0 ≡ 2 * W 0 [ZMOD 2 ^ m]
    exact Int.ModEq.refl _
  · change (2 + (2 : ℤ) ^ m) * ((1 - (2 : ℤ) ^ (m - 1)) * W 1) ≡
      2 * W 1 [ZMOD 2 ^ (m + 1)]
    rw [Int.modEq_iff_dvd]
    have hpowm : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
      ring
    have hpow : (2 : ℤ) ^ m * (2 : ℤ) ^ (m - 1) = (2 : ℤ) ^ (2 * m - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hcoef : (2 + (2 : ℤ) ^ m) * (1 - (2 : ℤ) ^ (m - 1)) =
        2 - (2 : ℤ) ^ (2 * m - 1) := by
      rw [← hpow]
      rw [hpowm]
      ring
    have hpow2 : (2 : ℤ) ^ (2 * m - 1) =
        (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ (m - 2) := by
      rw [show 2 * m - 1 = (m + 1) + (m - 2) by omega, pow_add]
    refine ⟨(2 : ℤ) ^ (m - 2) * W 1, ?_⟩
    calc 2 * W 1 - (2 + (2 : ℤ) ^ m) * ((1 - (2 : ℤ) ^ (m - 1)) * W 1)
        = (2 - (2 + (2 : ℤ) ^ m) * (1 - (2 : ℤ) ^ (m - 1))) * W 1 := by ring
      _ = (2 - (2 - (2 : ℤ) ^ (2 * m - 1))) * W 1 := by rw [hcoef]
      _ = (2 : ℤ) ^ (2 * m - 1) * W 1 := by ring
      _ = ((2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ (m - 2)) * W 1 := by rw [hpow2]
      _ = (2 : ℤ) ^ (m + 1) * ((2 : ℤ) ^ (m - 2) * W 1) := by ring
  · change (2 + (2 : ℤ) ^ m) * ((1 - (2 : ℤ) ^ (m - 1)) * W 2) ≡
      2 * W 2 [ZMOD 2 ^ (m + 1)]
    rw [Int.modEq_iff_dvd]
    have hpowm : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
      ring
    have hpow : (2 : ℤ) ^ m * (2 : ℤ) ^ (m - 1) = (2 : ℤ) ^ (2 * m - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hcoef : (2 + (2 : ℤ) ^ m) * (1 - (2 : ℤ) ^ (m - 1)) =
        2 - (2 : ℤ) ^ (2 * m - 1) := by
      rw [← hpow]
      rw [hpowm]
      ring
    have hpow2 : (2 : ℤ) ^ (2 * m - 1) =
        (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ (m - 2) := by
      rw [show 2 * m - 1 = (m + 1) + (m - 2) by omega, pow_add]
    refine ⟨(2 : ℤ) ^ (m - 2) * W 2, ?_⟩
    calc 2 * W 2 - (2 + (2 : ℤ) ^ m) * ((1 - (2 : ℤ) ^ (m - 1)) * W 2)
        = (2 - (2 + (2 : ℤ) ^ m) * (1 - (2 : ℤ) ^ (m - 1))) * W 2 := by ring
      _ = (2 - (2 - (2 : ℤ) ^ (2 * m - 1))) * W 2 := by rw [hcoef]
      _ = (2 : ℤ) ^ (2 * m - 1) * W 2 := by ring
      _ = ((2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ (m - 2)) * W 2 := by rw [hpow2]
      _ = (2 : ℤ) ^ (m + 1) * ((2 : ℤ) ^ (m - 2) * W 2) := by ring

theorem even_of_intCast_eq_even {n : ℕ} (hn : 1 ≤ n) {a b : ℤ} (hb : Even b)
    (h : (a : ZMod (2 ^ n)) = (b : ZMod (2 ^ n))) : Even a := by
  have hdvd : (2 : ℤ) ^ n ∣ b - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b (2 ^ n)).mp h
  have h2dvd : (2 : ℤ) ∣ b - a :=
    (dvd_pow_self 2 (by omega : n ≠ 0)).trans hdvd
  have h2a : (2 : ℤ) ∣ a := by
    have := dvd_sub hb.two_dvd h2dvd
    simpa using this
  exact even_iff_two_dvd.mpr h2a

theorem thetaM_mulVec_even (m : ℕ) (hm : 1 ≤ m) (D : Fin 3 → ℤ) (i : Fin 3) :
    Even ((thetaM m *ᵥ D) i) := by
  rw [thetaM, Matrix.mulVec_diagonal]
  fin_cases i
  · change Even (2 * D 0)
    exact even_two_mul _
  · change Even ((2 + (2 : ℤ) ^ m) * D 1)
    refine ⟨(1 + (2 : ℤ) ^ (m - 1)) * D 1, ?_⟩
    have hpow : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
      ring
    rw [hpow]
    ring
  · change Even ((2 + (2 : ℤ) ^ m) * D 2)
    refine ⟨(1 + (2 : ℤ) ^ (m - 1)) * D 2, ?_⟩
    have hpow : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
      ring
    rw [hpow]
    ring

theorem even_matVec_sub_of_theta_eq (m : ℕ) (hm : 2 ≤ m) (M : IntMat)
    (hM : Compat (Type100.k m) M) {q : Torus (Type100.k m)}
    (h : ∃ d, theta m d = matAct (Type100.k m) M hM q - q)
    (Q : Fin 3 → ℤ) (hQ : q = Torus.ofInt (Type100.k m) Q) (i : Fin 3) :
    Even ((M *ᵥ Q - Q) i) := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨D, hD⟩ := Torus.exists_ofInt d
  have htheta : theta m d = Torus.ofInt (Type100.k m) (thetaM m *ᵥ D) := by
    rw [← hD, theta_ofInt]
  have hMq : matAct (Type100.k m) M hM q - q =
      Torus.ofInt (Type100.k m) (M *ᵥ Q - Q) := by
    rw [hQ, matAct_ofInt, Torus.ofInt_sub]
  have hEq : Torus.ofInt (Type100.k m) (M *ᵥ Q - Q) =
      Torus.ofInt (Type100.k m) (thetaM m *ᵥ D) := by
    rw [← hMq, ← hd, htheta]
  have hcoord := congrFun hEq i
  have hmeven : Even ((thetaM m *ᵥ D) i) := thetaM_mulVec_even m (by omega) D i
  have hk1 : 1 ≤ Type100.k m i := by
    have hm' := hm
    fin_cases i <;> simp [Type100.k] <;> omega
  exact even_of_intCast_eq_even (n := Type100.k m i) hk1 hmeven hcoord

theorem uM_mulVec (Q : Fin 3 → ℤ) :
    Type100.uM *ᵥ Q = ![Q 0, Q 2, Q 1] := by
  funext i
  fin_cases i <;>
    simp [Type100.uM, uMat, ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem rhoM_mulVec (Q : Fin 3 → ℤ) :
    Type100.ρM *ᵥ Q = ![Q 0 - 2 * Q 2, -Q 2, Q 1 - Q 2] := by
  funext i
  fin_cases i <;>
    simp [Type100.ρM, ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem ofInt_one_zero_zero (m : ℕ) :
    Torus.ofInt (Type100.k m) ![1, 0, 0] = Torus.c := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp [Torus.c]

theorem exists_theta_eq_of_two_zsmul (m : ℕ) (hm : 2 ≤ m)
    {v : Torus (Type100.k m)} (hv : ∃ w, (2 : ℤ) • w = v) :
    ∃ d, theta m d = v := by
  obtain ⟨w, hw⟩ := hv
  obtain ⟨W, hW⟩ := Torus.exists_ofInt w
  refine ⟨Torus.ofInt (Type100.k m) (thetaPreInt m W), ?_⟩
  rw [theta_thetaPreInt m hm W, hW, hw]

theorem square_class_dichotomy (m : ℕ) (hm : 2 ≤ m) (q : Torus (Type100.k m))
    (huv : ∃ d, theta m d = matAct (Type100.k m) Type100.uvM (Type100.compat_uv m) q - q)
    (ht : ∃ d, theta m d = matAct (Type100.k m) Type100.tM (Type100.compat_t m) q - q)
    (hu : ∃ d, theta m d = matAct (Type100.k m) Type100.uM (Type100.compat_u m) q - q)
    (hr : ∃ d, theta m d = matAct (Type100.k m) Type100.ρM (Type100.compat_rho m) q - q) :
    (∃ d, theta m d = q) ∨ (∃ d, theta m d = q - Torus.c) := by
  obtain ⟨Q, hQ⟩ := Torus.exists_ofInt q
  have hQ' : q = Torus.ofInt (Type100.k m) Q := hQ.symm
  have hu1 : Even ((Type100.uM *ᵥ Q - Q) 1) :=
    even_matVec_sub_of_theta_eq m hm Type100.uM (Type100.compat_u m) hu Q hQ' 1
  have hr2 : Even ((Type100.ρM *ᵥ Q - Q) 2) :=
    even_matVec_sub_of_theta_eq m hm Type100.ρM (Type100.compat_rho m) hr Q hQ' 2
  have hu1' : Even (Q 2 - Q 1) := by
    have hEq : (Type100.uM *ᵥ Q - Q) 1 = Q 2 - Q 1 := by
      rw [uM_mulVec]
      simp [Fin.isValue]
    rwa [hEq] at hu1
  have hr2' : Even (Q 1 - 2 * Q 2) := by
    have hEq : (Type100.ρM *ᵥ Q - Q) 2 = Q 1 - 2 * Q 2 := by
      rw [rhoM_mulVec]
      simp [Fin.isValue]
      ring
    rwa [hEq] at hr2
  have hQ1 : Even (Q 1) := by
    have h := hr2'.add (even_two_mul (Q 2))
    simpa [sub_add_cancel] using h
  have hQ2 : Even (Q 2) := by
    have h := hu1'.add hQ1
    simpa [sub_add_cancel] using h
  rcases Int.even_or_odd (Q 0) with hQ0 | hQ0
  · obtain ⟨e0, he0⟩ := even_iff_exists_two_mul.mp hQ0
    obtain ⟨e1, he1⟩ := even_iff_exists_two_mul.mp hQ1
    obtain ⟨e2, he2⟩ := even_iff_exists_two_mul.mp hQ2
    let E : Fin 3 → ℤ := ![e0, e1, e2]
    have hE : (2 : ℤ) • E = Q := by
      funext i
      fin_cases i <;> simp [E, he0, he1, he2]
    have hq2 : (2 : ℤ) • Torus.ofInt (Type100.k m) E = q := by
      rw [← Torus.ofInt_zsmul, hE, ← hQ']
    obtain ⟨d, hd⟩ := exists_theta_eq_of_two_zsmul m hm ⟨Torus.ofInt (Type100.k m) E, hq2⟩
    exact Or.inl ⟨d, hd⟩
  · obtain ⟨e0, he0⟩ := hQ0
    obtain ⟨e1, he1⟩ := even_iff_exists_two_mul.mp hQ1
    obtain ⟨e2, he2⟩ := even_iff_exists_two_mul.mp hQ2
    let E : Fin 3 → ℤ := ![e0, e1, e2]
    have hE : (2 : ℤ) • E = Q - ![1, 0, 0] := by
      funext i
      fin_cases i <;> simp [E, he0, he1, he2] <;> omega
    have hq2 : (2 : ℤ) • Torus.ofInt (Type100.k m) E = q - Torus.c := by
      rw [← Torus.ofInt_zsmul, hE, Torus.ofInt_sub, ofInt_one_zero_zero, ← hQ']
    obtain ⟨d, hd⟩ := exists_theta_eq_of_two_zsmul m hm ⟨Torus.ofInt (Type100.k m) E, hq2⟩
    exact Or.inr ⟨d, hd⟩

theorem exists_sq_mem_D_of_index_two (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (F : Subgroup G) (hF : F ≤ Z.centralizerInMho)
    (hidx : (Z.D.subgroupOf F).index = 2) :
    ∃ s : G, s ∈ F ∧ s ∉ Z.D ∧ s * s ∈ Z.D := by
  obtain ⟨s, hsnot, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hidx
  have hsD : (s : G) ∉ Z.D := by
    intro h
    exact hsnot (Subgroup.mem_subgroupOf.mpr h)
  exact ⟨(s : G), s.2, hsD, sq_mem_D_of_mem_centralizerInMho (Z := Z) hk (hF s.2)⟩

theorem exists_mul_eq_of_mem_normalizer_of_index_two (Z : StrothDatum X)
    (F : Subgroup G) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    {s l : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) (hl : l ∈ X.L) :
    ∃ d ∈ Z.D, l⁻¹ * s * l = s * d := by
  let x : G := l⁻¹ * s * l
  have hlN : l ∈ Subgroup.normalizer (Z.D : Set G) := Z.L_le_normalizer hl
  have hxlF : x ∈ F := by
    have hlinv : l⁻¹ ∈ Subgroup.normalizer (F : Set G) := Subgroup.inv_mem _ (hN hl)
    simpa [x] using (Subgroup.mem_normalizer_iff.mp hlinv s).mp hsF
  have hxlD : x ∉ Z.D := by
    intro hxD
    have hconj : l * x * l⁻¹ ∈ Z.D := (Subgroup.mem_normalizer_iff.mp hlN x).mp hxD
    have hseq : l * x * l⁻¹ = s := by
      dsimp [x]
      group
    exact hsD (hseq ▸ hconj)
  have hsInvF : s⁻¹ ∈ F := F.inv_mem hsF
  have hsInvD : s⁻¹ ∉ Z.D := fun h => hsD (by simpa using Z.D.inv_mem h)
  let H : Subgroup F := Z.D.subgroupOf F
  have hxH : (⟨x, hxlF⟩ : F) ∉ H := fun h => hxlD (Subgroup.mem_subgroupOf.mp h)
  have hsInvH : (⟨s⁻¹, hsInvF⟩ : F) ∉ H := fun h => hsInvD (Subgroup.mem_subgroupOf.mp h)
  have hmulH : (⟨x, hxlF⟩ : F) * (⟨s⁻¹, hsInvF⟩ : F) ∈ H := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun hx => (hxH hx).elim, fun hs => (hsInvH hs).elim⟩
  have hd0D : x * s⁻¹ ∈ Z.D := Subgroup.mem_subgroupOf.mp hmulH
  have hsN : s ∈ Subgroup.normalizer (Z.D : Set G) :=
    ((inf_le_left : Z.centralizerInMho ≤ Z.normalizerIn) (hF hsF)).2
  let d : G := s⁻¹ * (x * s⁻¹) * s
  have hdD : d ∈ Z.D := by
    have hsInvN : s⁻¹ ∈ Subgroup.normalizer (Z.D : Set G) := Subgroup.inv_mem _ hsN
    have := (Subgroup.mem_normalizer_iff.mp hsInvN (x * s⁻¹)).mp hd0D
    simpa [d] using this
  refine ⟨d, hdD, ?_⟩
  dsimp [x, d]
  group

theorem sq_mul_eq_sq_mul_deviation (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    {s d : G} (hs : s ∈ Z.centralizerInMho) (hd : d ∈ Z.D) :
    (s * d) * (s * d) =
      (s * s) * (d * d * ((deviation Z s hs (Additive.ofMul ⟨d, hd⟩)).toMul : G)) := by
  set φ : G := ((deviation Z s hs (Additive.ofMul ⟨d, hd⟩)).toMul : G) with hφ
  have hφω : φ ∈ omegaIn 1 Z.D := by
    rw [hφ]
    exact (deviation Z s hs (Additive.ofMul ⟨d, hd⟩)).toMul.2
  have hφmho : φ ∈ mhoOne Z.D := omegaIn_one_le_mhoOne_of_two_le_k Z hk hφω
  have hφD : φ ∈ Z.D := omegaIn_le 1 Z.D hφω
  have hcommφs : φ * s = s * φ := Subgroup.mem_centralizer_iff.mp hs.2 φ hφmho
  have hsφ : s * φ * s⁻¹ = φ := by
    calc s * φ * s⁻¹ = φ * s * s⁻¹ := by rw [hcommφs]
      _ = φ := by group
  have hsφinv : s⁻¹ * φ * s = φ := by
    calc s⁻¹ * φ * s = s⁻¹ * (φ * s) := by group
      _ = s⁻¹ * (s * φ) := by rw [← hcommφs]
      _ = φ := by group
  have hsd : s * d * s⁻¹ = φ * d := by
    rw [hφ, deviation_apply]
    group
  have h1 : d = φ * (s⁻¹ * d * s) := by
    calc d = s⁻¹ * (s * d * s⁻¹) * s := by group
      _ = s⁻¹ * (φ * d) * s := by rw [hsd]
      _ = (s⁻¹ * φ * s) * (s⁻¹ * d * s) := by group
      _ = φ * (s⁻¹ * d * s) := by rw [hsφinv]
  have hφ2 : φ * φ = 1 := by
    have hφ' : φ ^ 2 = 1 := by
      have h := (mem_omegaIn_iff_of_comm (i := 1) (by
        intro a ha b hb
        exact congrArg Subtype.val
          (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))).mp hφω
      simpa using h.2
    simpa [pow_two] using hφ'
  have hsds : s⁻¹ * d * s = φ * d := by
    calc s⁻¹ * d * s = (φ * φ) * (s⁻¹ * d * s) := by rw [hφ2, one_mul]
      _ = φ * (φ * (s⁻¹ * d * s)) := by group
      _ = φ * d := by rw [← h1]
  have hcommφd : φ * d = d * φ := by
    have hcommD : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
      fun a ha b hb => congrArg Subtype.val
        (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact hcommD φ hφD d hd
  have hcommφdd : φ * (d * d) = (d * d) * φ := by
    calc φ * (d * d) = (φ * d) * d := by rw [mul_assoc]
      _ = (d * φ) * d := by rw [hcommφd]
      _ = d * (φ * d) := by rw [mul_assoc]
      _ = d * (d * φ) := by rw [hcommφd]
      _ = (d * d) * φ := by rw [mul_assoc]
  calc (s * d) * (s * d) = (s * s) * (s⁻¹ * d * s) * d := by group
    _ = (s * s) * (φ * d) * d := by rw [hsds]
    _ = (s * s) * (φ * (d * d)) := by group
    _ = (s * s) * (d * d * φ) := by rw [hcommφdd]

@[expose] def thetaD (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho) (d : Z.D) : Z.D :=
  ⟨(d : G) * (d : G) * ((deviation Z s hs (Additive.ofMul d)).toMul : G), by
    have hd2 : (d : G) * (d : G) ∈ Z.D := Z.D.mul_mem d.2 d.2
    have hφ : ((deviation Z s hs (Additive.ofMul d)).toMul : G) ∈ Z.D :=
      omegaIn_le 1 Z.D (deviation Z s hs (Additive.ofMul d)).toMul.2
    exact Z.D.mul_mem hd2 hφ⟩

@[simp] theorem coe_thetaD (Z : StrothDatum X) (s : G) (hs : s ∈ Z.centralizerInMho)
    (d : Z.D) :
    (thetaD Z s hs d : G) =
      (d : G) * (d : G) * ((deviation Z s hs (Additive.ofMul d)).toMul : G) := rfl

theorem sq_mul_eq_sq_mul_thetaD (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    {s d : G} (hs : s ∈ Z.centralizerInMho) (hd : d ∈ Z.D) :
    (s * d) * (s * d) = (s * s) * (thetaD Z s hs ⟨d, hd⟩ : G) := by
  rw [sq_mul_eq_sq_mul_deviation Z hk hs hd]
  rfl

end CFSG.CGT.Stroth77
