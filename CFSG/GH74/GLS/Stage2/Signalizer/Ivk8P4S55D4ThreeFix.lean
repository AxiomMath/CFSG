module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4Native

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

section Matrix

theorem neg_one_mul_neg_one_SL2' {F : Type} [Field F] : (-1 : SL(2, F)) * -1 = 1 := by
  apply Subtype.ext
  simp

theorem neg_one_ne_one_SL2' {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at this
  exact h2 (by linear_combination -this)

theorem sl2_cube_of_comm_WSL {F : Type} [Field F] (h3 : (3 : F) = 0) {A : SL(2, F)}
    (hc : A * WSL = WSL * A) (h : A ^ 3 = 1 ∨ A ^ 3 = -1) : A = 1 ∨ A = -1 := by
  have hm : (A : Matrix (Fin 2) (Fin 2) F) * ((WSL : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((WSL : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) hc
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  have hW : ((WSL : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  obtain ⟨a, b, c, d, hA⟩ : ∃ a b c d : F, (A : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hW, hA] at hm
  simp only [Matrix.mul_fin_two] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp at e00 e01
  have hdc : d = a := by linear_combination -e01
  have hcb : c = -b := by linear_combination -e00
  subst hdc hcb
  have hcube : (A : Matrix (Fin 2) (Fin 2) F) ^ 3 = !![d ^ 3 - 3 * d * b ^ 2,
      3 * d ^ 2 * b - b ^ 3; -(3 * d ^ 2 * b) + b ^ 3, d ^ 3 - 3 * d * b ^ 2] := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rcases h with h | h
  · left
    have h1 := congrArg (fun Y : SL(2, F) => (Y : Matrix (Fin 2) (Fin 2) F)) h
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hcube] at h1
    have e1 := congrFun (congrFun h1 0) 0
    have e2 := congrFun (congrFun h1 0) 1
    simp at e1 e2
    have hb3 : b ^ 3 = 0 := by linear_combination (-1) * e2 + (d ^ 2 * b) * h3
    have hb : b = 0 := pow_eq_zero_iff (by norm_num) |>.1 hb3
    subst hb
    have hd3 : d ^ 3 = 1 := by simpa using e1
    have hd : d = 1 := by
      have : (d - 1) ^ 3 = 0 := by linear_combination hd3 + (d - d ^ 2) * h3
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    subst hd
    apply Subtype.ext
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    have h1 := congrArg (fun Y : SL(2, F) => (Y : Matrix (Fin 2) (Fin 2) F)) h
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, hcube] at h1
    have e1 := congrFun (congrFun h1 0) 0
    have e2 := congrFun (congrFun h1 0) 1
    simp at e1 e2
    have hb3 : b ^ 3 = 0 := by linear_combination (-1) * e2 + (d ^ 2 * b) * h3
    have hb : b = 0 := pow_eq_zero_iff (by norm_num) |>.1 hb3
    subst hb
    have hd3 : d ^ 3 = -1 := by simpa using e1
    have hd : d = -1 := by
      have : (d + 1) ^ 3 = 0 := by linear_combination hd3 + (d + d ^ 2) * h3
      exact eq_neg_of_add_eq_zero_left (pow_eq_zero_iff (by norm_num) |>.1 this)
    subst hd
    apply Subtype.ext
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end Matrix

section Fixed

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem coe_xPar_single_two (j : Fin d4.rank) (c : K) :
    ((xPar (rootOperatorFamily d4) (Pi.single j 1) c : adjointGroup d4 K) : ModGL d4 K) =
      xUnit d4 K j c := by
  rw [xPar_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_simple]

theorem coe_xPar_neg_single_two (j : Fin d4.rank) (c : K) :
    ((xPar (rootOperatorFamily d4) (-Pi.single j 1) c : adjointGroup d4 K) : ModGL d4 K) =
      yUnit d4 K j c := by
  rw [xPar_neg_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_neg_simple]

theorem entrywise_xOuter (δ : K →+* K) {s : ℤ} (hs : s = 1 ∨ s = -1) (c d e : K) :
    Units.map (entrywiseHom δ) ((xOuter s c d e : adjointGroup d4 K) : ModGL d4 K) =
      ((xOuter s (δ c) (δ d) (δ e) : adjointGroup d4 K) : ModGL d4 K) := by
  rcases hs with rfl | rfl
  · simp only [xOuter, one_smul, Subgroup.coe_mul, map_mul, coe_xPar_single_two,
      units_map_entrywiseHom_xUnit]
  · simp only [xOuter, neg_one_smul, Subgroup.coe_mul, map_mul, coe_xPar_neg_single_two,
      units_map_entrywiseHom_yUnit]

include hσ in
theorem wL_fixed :
    Units.map (entrywiseHom σ) (twistedIncl σ (slLong σ hσ WSL)) =
      twistedIncl σ (slLong σ hσ WSL) := by
  have hW3 : twistedIncl σ (slLong σ hσ WSL) = twistedIncl σ (slLong σ hσ (uSL 1)) *
      twistedIncl σ (slLong σ hσ (vSL (-1))) * twistedIncl σ (slLong σ hσ (uSL 1)) := by
    rw [WSL_eq_uSL_mul_vSL_mul_uSL]
    simp only [map_mul]
  rw [hW3, map_mul, map_mul, twistedIncl_slLong_upper hσ, twistedIncl_slLong_lower hσ,
    coe_xPar_single_two, coe_xPar_neg_single_two, units_map_entrywiseHom_xUnit,
    units_map_entrywiseHom_yUnit]
  simp

include hσ in
theorem wB_fixed [Finite K] :
    Units.map (entrywiseHom σ) (twistedIncl σ (slB σ hσ WSL)) =
      twistedIncl σ (slB σ hσ WSL) := by
  let σE : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hcan : Units.map (entrywiseHom σ) (canonicalRep (coxeterSystem d4) K tdNhat) =
      canonicalRep (coxeterSystem d4) K tdNhat := by
    have := entrywise_canonicalRep (τ := d4) σE tdNhat
    rwa [hσE] at this
  have hS : Units.map (entrywiseHom σ) (twistedIncl σ (slShort σ hσ WSL)) =
      twistedIncl σ (slShort σ hσ WSL) := by
    have hW3 : twistedIncl σ (slShort σ hσ WSL) = twistedIncl σ (slShort σ hσ (uSL 1)) *
        twistedIncl σ (slShort σ hσ (vSL (-1))) * twistedIncl σ (slShort σ hσ (uSL 1)) := by
      rw [WSL_eq_uSL_mul_vSL_mul_uSL]
      simp only [map_mul]
    rw [hW3, map_mul, map_mul, twistedIncl_slShort_upper hσ, twistedIncl_slShort_lower hσ,
      entrywise_xOuter σ (Or.inl rfl), entrywise_xOuter σ (Or.inr rfl)]
    simp
  rw [twistedIncl_slB hσ, map_mul, map_mul, map_inv, hS, hcan]

end Fixed

section Group

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] def NProd : Subgroup (twistedGroup σ) where
  carrier := {x | ∃ (A : SL(2, fixedField σ)) (B : SL(2, K)),
    x = slLong σ hσ A * slB σ hσ B}
  one_mem' := ⟨1, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨A₁, B₁, rfl⟩ ⟨A₂, B₂, rfl⟩
    refine ⟨A₁ * A₂, B₁ * B₂, ?_⟩
    have hc := slLong_comm_slB hσ A₂ B₁
    simp only [map_mul]
    calc slLong σ hσ A₁ * slB σ hσ B₁ * (slLong σ hσ A₂ * slB σ hσ B₂)
        = slLong σ hσ A₁ * (slB σ hσ B₁ * slLong σ hσ A₂) * slB σ hσ B₂ := by group
      _ = slLong σ hσ A₁ * (slLong σ hσ A₂ * slB σ hσ B₁) * slB σ hσ B₂ := by rw [← hc]
      _ = _ := by group
  inv_mem' := by
    rintro _ ⟨A, B, rfl⟩
    refine ⟨A⁻¹, B⁻¹, ?_⟩
    rw [mul_inv_rev, map_inv, map_inv]
    exact (Commute.inv_inv (slLong_comm_slB hσ A B : Commute (slLong σ hσ A) (slB σ hσ B))).eq.symm


theorem TK_pow_card [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 3) {t : twistedGroup σ}
    (ht : t ∈ TK σ) : t ^ (q ^ 3 - 1) = 1 := by
  obtain ⟨b, hb⟩ := ht
  apply twistedIncl_injective σ
  rw [map_pow, hb, map_one]
  have h1 : rootDiagUnit d4 b ^ (q ^ 3 - 1) = rootDiagUnit d4 (b ^ (q ^ 3 - 1)) :=
    (map_pow (rootDiagUnitHom d4 K) b _).symm
  have hb' : b ^ (q ^ 3 - 1) = 1 := by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    have := pow_card_eq_one' (G := Kˣ) (x := b i)
    rwa [Nat.card_units, hK] at this
  rw [h1, hb', rootDiagUnit_one]

include hσ in
theorem exists_fixed_two_subgroup [Finite K] [CharP K 3] {q : ℕ} (h : D4Data K σ q) :
    ∃ E : Subgroup (twistedGroup σ), IsPGroup 2 E ∧
      (∀ e ∈ E, Units.map (entrywiseHom σ) (twistedIncl σ e) = twistedIncl σ e) ∧
      ∀ y : twistedGroup σ, (∀ e ∈ E, y * e = e * y) → y ^ 3 = 1 → y = 1 := by
  have hK := h.neg_one
  have h3K : (3 : K) = 0 := by
    have := CharP.cast_eq_zero K 3
    simpa using this
  have h3F : (3 : fixedField σ) = 0 := by
    have := CharP.cast_eq_zero (fixedField σ) 3
    simpa using this
  have h2F : (2 : fixedField σ) ≠ 0 := by
    intro h2
    exact one_ne_zero (by linear_combination h3F - h2)
  have hcomm : Commute (slLong σ hσ WSL) (slB σ hσ WSL) := slLong_comm_slB hσ WSL WSL
  have hWWF : (WSL : SL(2, fixedField σ)) ^ 4 = 1 := by
    have : (WSL : SL(2, fixedField σ)) ^ 4 = (WSL * WSL) * (WSL * WSL) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, CFSG.LieType.Chevalley.WSL_mul_WSL, neg_one_mul_neg_one_SL2']
  have hWWK : (WSL : SL(2, K)) ^ 4 = 1 := by
    have : (WSL : SL(2, K)) ^ 4 = (WSL * WSL) * (WSL * WSL) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, CFSG.LieType.Chevalley.WSL_mul_WSL, neg_one_mul_neg_one_SL2']
  have hL4 : slLong σ hσ WSL ^ 4 = 1 := by rw [← map_pow, hWWF, map_one]
  have hB4 : slB σ hσ WSL ^ 4 = 1 := by rw [← map_pow, hWWK, map_one]
  have hpow4 : ∀ (g : twistedGroup σ) (a : ℤ), g ^ 4 = 1 → (g ^ a) ^ 4 = 1 := by
    intro g a hg
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  refine ⟨Subgroup.closure {slLong σ hσ WSL, slB σ hσ WSL}, ?_, ?_, ?_⟩
  ·
    have hform : ∀ x ∈ Subgroup.closure ({slLong σ hσ WSL, slB σ hσ WSL} : Set (twistedGroup σ)),
        ∃ a b : ℤ, x = slLong σ hσ WSL ^ a * slB σ hσ WSL ^ b := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx
        · exact ⟨1, 0, by simp⟩
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨0, 1, by simp⟩
      | one => exact ⟨0, 0, by simp⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, b, rfl⟩ := hx
        obtain ⟨c, d, rfl⟩ := hy
        refine ⟨a + c, b + d, ?_⟩
        have hbc := (hcomm.symm.zpow_zpow b c).eq
        calc slLong σ hσ WSL ^ a * slB σ hσ WSL ^ b * (slLong σ hσ WSL ^ c * slB σ hσ WSL ^ d)
            = slLong σ hσ WSL ^ a * (slB σ hσ WSL ^ b * slLong σ hσ WSL ^ c) *
                slB σ hσ WSL ^ d := by simp only [mul_assoc]
          _ = slLong σ hσ WSL ^ a * (slLong σ hσ WSL ^ c * slB σ hσ WSL ^ b) *
                slB σ hσ WSL ^ d := by rw [hbc]
          _ = _ := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
      | inv x _ hx =>
        obtain ⟨a, b, rfl⟩ := hx
        refine ⟨-a, -b, ?_⟩
        rw [mul_inv_rev, zpow_neg, zpow_neg]
        exact (Commute.inv_inv (hcomm.zpow_zpow a b)).eq.symm
    intro x
    obtain ⟨a, b, hx⟩ := hform x x.2
    refine ⟨2, ?_⟩
    apply Subtype.ext
    show (x : twistedGroup σ) ^ 2 ^ 2 = 1
    have hc := hcomm.zpow_zpow a b
    rw [hx, show (2 : ℕ) ^ 2 = 4 from rfl, hc.mul_pow, hpow4 _ a hL4, hpow4 _ b hB4, one_mul]
  ·
    intro e he
    have hle : Subgroup.closure ({slLong σ hσ WSL, slB σ hσ WSL} : Set (twistedGroup σ)) ≤
        MonoidHom.eqLocus ((Units.map (entrywiseHom σ)).comp (twistedIncl σ)) (twistedIncl σ) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact wL_fixed hσ
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact wB_fixed hσ
    exact hle he
  ·
    intro y hy hy3
    have hyL : y * slLong σ hσ WSL = slLong σ hσ WSL * y :=
      hy _ (Subgroup.subset_closure (Set.mem_insert _ _))
    have hyB : y * slB σ hσ WSL = slB σ hσ WSL * y :=
      hy _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hz : y * slLong σ hσ (-1) = slLong σ hσ (-1) * y := by
      rw [← CFSG.LieType.Chevalley.WSL_mul_WSL, map_mul]
      calc y * (slLong σ hσ WSL * slLong σ hσ WSL)
          = (y * slLong σ hσ WSL) * slLong σ hσ WSL := (mul_assoc _ _ _).symm
        _ = (slLong σ hσ WSL * y) * slLong σ hσ WSL := by rw [hyL]
        _ = slLong σ hσ WSL * (y * slLong σ hσ WSL) := mul_assoc _ _ _
        _ = slLong σ hσ WSL * (slLong σ hσ WSL * y) := by rw [hyL]
        _ = (slLong σ hσ WSL * slLong σ hσ WSL) * y := (mul_assoc _ _ _).symm
    obtain ⟨t, ht, A, B, hyAB⟩ := mem_SProd_of_centralizes hσ hK h.hC₀ h.hgF hz
    have hNconj : ∀ s ∈ TK σ, ∀ n ∈ NProd hσ, s * n * s⁻¹ ∈ NProd hσ := by
      rintro s hs _ ⟨A', B', rfl⟩
      obtain ⟨A'', hA''⟩ := TK_conj_slLong hσ hs A'
      obtain ⟨B'', hB''⟩ := TK_conj_slB hσ hs B'
      refine ⟨A'', B'', ?_⟩
      calc s * (slLong σ hσ A' * slB σ hσ B') * s⁻¹
          = (s * slLong σ hσ A' * s⁻¹) * (s * slB σ hσ B' * s⁻¹) := by group
        _ = _ := by rw [hA'', hB'']
    have hn : slLong σ hσ A * slB σ hσ B ∈ NProd hσ := ⟨A, B, rfl⟩
    have hyt : y = t * (slLong σ hσ A * slB σ hσ B) := by rw [hyAB]; group
    have ht3 : t ^ 3 ∈ NProd hσ := by
      set n := slLong σ hσ A * slB σ hσ B with hndef
      have hid : (t * n) ^ 3 = t ^ 3 * ((t⁻¹ ^ 2 * n * (t⁻¹ ^ 2)⁻¹) * (t⁻¹ * n * t⁻¹⁻¹) * n) := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      have hm : (t⁻¹ ^ 2 * n * (t⁻¹ ^ 2)⁻¹) * (t⁻¹ * n * t⁻¹⁻¹) * n ∈ NProd hσ :=
        mul_mem (mul_mem (hNconj _ (pow_mem (inv_mem ht) 2) n hn)
          (hNconj _ (inv_mem ht) n hn)) hn
      rw [← hyt, hy3] at hid
      have : t ^ 3 = ((t⁻¹ ^ 2 * n * (t⁻¹ ^ 2)⁻¹) * (t⁻¹ * n * t⁻¹⁻¹) * n)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        exact hid.symm
      rw [this]
      exact inv_mem hm
    have h3q : ∃ m : ℕ, q ^ 3 = 3 * m := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨n, -, hn'⟩ := FiniteField.card K 3
      have hdvd : 3 ∣ q ^ 3 := by
        rw [← h.card, Nat.card_eq_fintype_card, hn']
        exact dvd_pow_self 3 n.ne_zero
      exact hdvd
    obtain ⟨m, hm⟩ := h3q
    have htN : t ∈ NProd hσ := by
      have hq0 : 0 < q ^ 3 := by
        have := h.two_le
        positivity
      have : t = (t ^ 3) ^ m := by
        rw [← pow_mul, ← hm]
        calc t = t ^ (q ^ 3 - 1) * t := by rw [TK_pow_card h.card ht, one_mul]
          _ = t ^ (q ^ 3) := by rw [← pow_succ]; congr 1; omega
      rw [this]
      exact pow_mem ht3 m
    have hyN : y ∈ NProd hσ := by
      rw [hyt]
      exact mul_mem htN hn
    obtain ⟨A₂, B₂, hy₂⟩ := hyN
    have hAW : A₂ * WSL = WSL * A₂ := by
      have e : slLong σ hσ (A₂ * WSL) * slB σ hσ B₂ = slLong σ hσ (WSL * A₂) * slB σ hσ B₂ := by
        rw [hy₂] at hyL
        have hc := slLong_comm_slB hσ WSL B₂
        calc slLong σ hσ (A₂ * WSL) * slB σ hσ B₂
            = slLong σ hσ A₂ * (slLong σ hσ WSL * slB σ hσ B₂) := by rw [map_mul]; group
          _ = slLong σ hσ A₂ * (slB σ hσ B₂ * slLong σ hσ WSL) := by rw [← hc]
          _ = slLong σ hσ A₂ * slB σ hσ B₂ * slLong σ hσ WSL := by group
          _ = slLong σ hσ WSL * (slLong σ hσ A₂ * slB σ hσ B₂) := hyL
          _ = slLong σ hσ (WSL * A₂) * slB σ hσ B₂ := by rw [map_mul]; group
      exact slLong_injective hσ (mul_right_cancel e)
    have hBW : B₂ * WSL = WSL * B₂ := by
      have e : slLong σ hσ A₂ * slB σ hσ (B₂ * WSL) = slLong σ hσ A₂ * slB σ hσ (WSL * B₂) := by
        rw [hy₂] at hyB
        have hc := slLong_comm_slB hσ A₂ WSL
        calc slLong σ hσ A₂ * slB σ hσ (B₂ * WSL)
            = slLong σ hσ A₂ * slB σ hσ B₂ * slB σ hσ WSL := by rw [map_mul]; group
          _ = slB σ hσ WSL * (slLong σ hσ A₂ * slB σ hσ B₂) := hyB
          _ = (slB σ hσ WSL * slLong σ hσ A₂) * slB σ hσ B₂ := by group
          _ = (slLong σ hσ A₂ * slB σ hσ WSL) * slB σ hσ B₂ := by rw [hc]
          _ = slLong σ hσ A₂ * slB σ hσ (WSL * B₂) := by rw [map_mul]; group
      exact slB_injective hσ (mul_left_cancel e)
    have hcube : slLong σ hσ (A₂ ^ 3) * slB σ hσ (B₂ ^ 3) = 1 := by
      rw [map_pow, map_pow, ← Commute.mul_pow (slLong_comm_slB hσ A₂ B₂ :
        Commute (slLong σ hσ A₂) (slB σ hσ B₂)), ← hy₂]
      exact hy3
    have hz1 : (slLong σ hσ (-1) : twistedGroup σ) ≠ 1 := by
      intro h1
      have := slLong_injective hσ (h1.trans (map_one (slLong σ hσ)).symm)
      exact neg_one_ne_one_SL2' h2F this
    have hcubes : (A₂ ^ 3 = 1 ∧ B₂ ^ 3 = 1) ∨ (A₂ ^ 3 = -1 ∧ B₂ ^ 3 = -1) := by
      have hinter := chartBd_chartAd_inter hσ (B₂ ^ 3) (A₂ ^ 3)⁻¹ (by
        apply toTw_injective hσ
        rw [toTw_chartBd, toTw_chartAd, map_inv]
        exact eq_inv_of_mul_eq_one_right hcube)
      have hinter' : slB σ hσ (B₂ ^ 3) = 1 ∨ slB σ hσ (B₂ ^ 3) = slLong σ hσ (-1) := by
        rcases hinter with h1 | h1
        · left
          simpa [toTw_chartBd] using congrArg (toTw hσ) h1
        · right
          simpa [toTw_chartBd, toTw_zd] using congrArg (toTw hσ) h1
      rcases hinter' with h1 | h1
      · left
        refine ⟨?_, slB_injective hσ (h1.trans (map_one _).symm)⟩
        rw [h1, mul_one] at hcube
        exact slLong_injective hσ (hcube.trans (map_one _).symm)
      · right
        have hB3 : B₂ ^ 3 = -1 := slB_injective hσ (h1.trans (slB_neg_one hσ).symm)
        refine ⟨?_, hB3⟩
        rw [h1, ← map_mul] at hcube
        have h2 : A₂ ^ 3 * (-1) = 1 := slLong_injective hσ (hcube.trans (map_one _).symm)
        calc A₂ ^ 3 = A₂ ^ 3 * (-1) * (-1) := by
              rw [mul_assoc, neg_one_mul_neg_one_SL2', mul_one]
          _ = -1 := by rw [h2, one_mul]
    have hA : A₂ = 1 ∨ A₂ = -1 :=
      sl2_cube_of_comm_WSL h3F hAW (by
        rcases hcubes with h1 | h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1)
    have hB : B₂ = 1 ∨ B₂ = -1 :=
      sl2_cube_of_comm_WSL h3K hBW (by
        rcases hcubes with h1 | h1
        · exact Or.inl h1.2
        · exact Or.inr h1.2)
    have hzz : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
      rw [← map_mul, neg_one_mul_neg_one_SL2', map_one]
    have hzcube : slLong σ hσ (-1) ^ 3 = slLong σ hσ (-1) := by
      rw [pow_succ, pow_two, hzz, one_mul]
    rw [hy₂] at hy3 ⊢
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · simp
    · exfalso
      rw [map_one, one_mul, slB_neg_one hσ, hzcube] at hy3
      exact hz1 hy3
    · exfalso
      rw [map_one, mul_one, hzcube] at hy3
      exact hz1 hy3
    · rw [slB_neg_one hσ, hzz]

end Group

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
