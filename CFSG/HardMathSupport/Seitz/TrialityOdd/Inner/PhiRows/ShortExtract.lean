module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.CentralizerK
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Centralizer

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

section ShortExtract


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

include hσ in
theorem conj_d4X_four {g : twistedGroup σ.toRingHom} {c : Fin d4.rank → Kˣ}
    (hg : twistedIncl σ.toRingHom g = rootDiagUnit d4 c)
    (hfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (c i) = c i)
    (hρ : ∀ i, c (rhoPerm i) = c i) (u : K) :
    g * d4X hσ 4 u * g⁻¹ =
      d4X hσ 4 (((rootChar (τ := TwistTag.D4.tag) c (d43Lift (hexRoot 4)) : Kˣ) : K) * u) := by
  apply Subtype.ext
  have hβ : IsRoot d4 (d43Lift (hexRoot 4)) := isRoot_d43Lift (isRoot_hexRoot 4)
  have := a2cen_torus_conj_xOrbit (σ := σ) (g := (g : adjointGroup d4 K)) hg hfix hρ hβ u
  exact this

include hσ in
theorem conj_d4X_two {g : twistedGroup σ.toRingHom} {c : Fin d4.rank → Kˣ}
    (hg : twistedIncl σ.toRingHom g = rootDiagUnit d4 c)
    (hfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (c i) = c i)
    (hρ : ∀ i, c (rhoPerm i) = c i) (u : K) :
    g * d4X hσ 2 u * g⁻¹ =
      d4X hσ 2 (((rootChar (τ := TwistTag.D4.tag) c (d43Lift (hexRoot 2)) : Kˣ) : K) * u) := by
  apply Subtype.ext
  have hβ : IsRoot d4 (d43Lift (hexRoot 2)) := isRoot_d43Lift (isRoot_hexRoot 2)
  have := a2cen_torus_conj_xOrbit (σ := σ) (g := (g : adjointGroup d4 K)) hg hfix hρ hβ (-u)
  refine this.trans ?_
  show _ = d43XE σ.toRingHom 2 (-(((rootChar (τ := TwistTag.D4.tag) c (d43Lift (hexRoot 2)) : Kˣ) : K) * u))
  rw [mul_neg]
  rfl

omit hσ in
theorem rootChar_pos4 (u v : Kˣ) :
    rootChar (τ := TwistTag.D4.tag) (![u, u, v, u] : Fin 4 → Kˣ) (d43Lift (hexRoot 4)) = u * v := by
  have : d43Lift (hexRoot 4) = d4Root 5 := by rw [d43Lift_hexRoot]; rfl
  rw [this]
  have h5 : (d4Root 5 : Fin Tag.D4.rank → ℤ) = ![1, 0, 1, 0] := by
    funext i; fin_cases i <;> rfl
  unfold rootChar
  rw [h5]
  change ∏ x : Fin 4, (![u, u, v, u] : Fin 4 → Kˣ) x ^ (![1, 0, 1, 0] : Fin 4 → ℤ) x = u * v
  simp [Fin.prod_univ_four]

omit hσ in
theorem rootChar_pos2 (u v : Kˣ) :
    rootChar (τ := TwistTag.D4.tag) (![u, u, v, u] : Fin 4 → Kˣ) (d43Lift (hexRoot 2)) =
      u * u * v := by
  have : d43Lift (hexRoot 2) = d4Root 15 := by rw [d43Lift_hexRoot]; rfl
  rw [this]
  have h5 : (d4Root 15 : Fin Tag.D4.rank → ℤ) = ![0, 1, 1, 1] := by
    funext i; fin_cases i <;> rfl
  unfold rootChar
  rw [h5]
  change ∏ x : Fin 4, (![u, u, v, u] : Fin 4 → Kˣ) x ^ (![0, 1, 1, 1] : Fin 4 → ℤ) x = u * u * v
  simp [Fin.prod_univ_four, mul_assoc]
  exact mul_comm v u

omit hσ in
theorem tuple_short (a : Kˣ) (ha : Units.map σ.toRingHom.toMonoidHom a = a) :
    (fun j : Fin d4.rank => a ^ d4.cartan (nd 0) j *
      (Units.map σ.toRingHom.toMonoidHom a) ^ d4.cartan (nd 1) j *
      (Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a)) ^
        d4.cartan (nd 3) j) =
      (![a ^ (2 : ℤ), a ^ (2 : ℤ), a ^ (-3 : ℤ), a ^ (2 : ℤ)] : Fin 4 → Kˣ) := by
  funext j
  rw [ha, ha]
  fin_cases j <;> (rw [← zpow_add, ← zpow_add]; exact congrArg (a ^ ·) (by decide))

omit hσ in
theorem tuple_long (b : Kˣ) :
    (fun j : Fin d4.rank => b ^ d4.cartan (nd 2) j) =
      (![b ^ (-1 : ℤ), b ^ (-1 : ℤ), b ^ (2 : ℤ), b ^ (-1 : ℤ)] : Fin 4 → Kˣ) := by
  funext j
  fin_cases j <;> exact congrArg (b ^ ·) (by decide)

omit hσ in
theorem rhoConst_rho (u v : Kˣ) :
    ∀ i, (![u, u, v, u] : Fin 4 → Kˣ) (rhoPerm i) = (![u, u, v, u] : Fin 4 → Kˣ) i := by
  intro i
  fin_cases i <;> rfl

omit hσ in
theorem rhoConst_fix (u v : Kˣ) (hu : Units.map σ.toRingHom.toMonoidHom u = u)
    (hv : Units.map σ.toRingHom.toMonoidHom v = v) :
    ∀ i, Units.map σ.toRingHom.toMonoidHom ((![u, u, v, u] : Fin 4 → Kˣ) i) =
      (![u, u, v, u] : Fin 4 → Kˣ) i := by
  intro i
  fin_cases i <;> assumption

include hσ in
theorem conj_slShort_pos4 (a : Kˣ) (ha : Units.map σ.toRingHom.toMonoidHom a = a) (u : K) :
    slShort σ.toRingHom hσ (HSL a) * d4X hσ 4 u * (slShort σ.toRingHom hσ (HSL a))⁻¹ =
      d4X hσ 4 (((a⁻¹ : Kˣ) : K) * u) := by
  have hg := twistedIncl_slShort_HSL hσ a
  rw [tuple_short a ha] at hg
  have hfix := rhoConst_fix (σ := σ) (a ^ (2 : ℤ)) (a ^ (-3 : ℤ))
    (by rw [map_zpow, ha]) (by rw [map_zpow, ha])
  have := conj_d4X_four hσ hg hfix (rhoConst_rho _ _) u
  rw [this, rootChar_pos4, ← zpow_add, show (2 : ℤ) + -3 = -1 by norm_num, zpow_neg_one]

include hσ in
theorem conj_slShort_pos2 (a : Kˣ) (ha : Units.map σ.toRingHom.toMonoidHom a = a) (u : K) :
    slShort σ.toRingHom hσ (HSL a) * d4X hσ 2 u * (slShort σ.toRingHom hσ (HSL a))⁻¹ =
      d4X hσ 2 (((a : Kˣ) : K) * u) := by
  have hg := twistedIncl_slShort_HSL hσ a
  rw [tuple_short a ha] at hg
  have hfix := rhoConst_fix (σ := σ) (a ^ (2 : ℤ)) (a ^ (-3 : ℤ))
    (by rw [map_zpow, ha]) (by rw [map_zpow, ha])
  have := conj_d4X_two hσ hg hfix (rhoConst_rho _ _) u
  rw [this, rootChar_pos2, ← zpow_add, ← zpow_add, show (2 : ℤ) + 2 + -3 = 1 by norm_num,
    zpow_one]

omit hσ in
theorem fixed_unit_map_fix (b : (fixedField σ.toRingHom)ˣ) :
    Units.map σ.toRingHom.toMonoidHom (Units.map (fixedField σ.toRingHom).subtype.toMonoidHom b) =
      Units.map (fixedField σ.toRingHom).subtype.toMonoidHom b := by
  apply Units.ext
  exact (b : fixedField σ.toRingHom).2

include hσ in
theorem conj_slLong_pos4 (b : (fixedField σ.toRingHom)ˣ) (u : K) :
    slLong σ.toRingHom hσ (HSL b) * d4X hσ 4 u * (slLong σ.toRingHom hσ (HSL b))⁻¹ =
      d4X hσ 4 ((((b : fixedField σ.toRingHom) : K)) * u) := by
  set b' := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom b with hb'
  have hg := twistedIncl_slLong_HSL hσ b
  rw [← hb', tuple_long b'] at hg
  have hfix := rhoConst_fix (σ := σ) (b' ^ (-1 : ℤ)) (b' ^ (2 : ℤ))
    (by rw [map_zpow, fixed_unit_map_fix]) (by rw [map_zpow, fixed_unit_map_fix])
  have := conj_d4X_four hσ hg hfix (rhoConst_rho _ _) u
  rw [this, rootChar_pos4, ← zpow_add, show (-1 : ℤ) + 2 = 1 by norm_num, zpow_one]
  rfl

include hσ in
theorem conj_slLong_pos2 (b : (fixedField σ.toRingHom)ˣ) (u : K) :
    slLong σ.toRingHom hσ (HSL b) * d4X hσ 2 u * (slLong σ.toRingHom hσ (HSL b))⁻¹ =
      d4X hσ 2 u := by
  set b' := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom b with hb'
  have hg := twistedIncl_slLong_HSL hσ b
  rw [← hb', tuple_long b'] at hg
  have hfix := rhoConst_fix (σ := σ) (b' ^ (-1 : ℤ)) (b' ^ (2 : ℤ))
    (by rw [map_zpow, fixed_unit_map_fix]) (by rw [map_zpow, fixed_unit_map_fix])
  have := conj_d4X_two hσ hg hfix (rhoConst_rho _ _) u
  rw [this, rootChar_pos2]
  have h1 : b' ^ (-1 : ℤ) * b' ^ (-1 : ℤ) * b' ^ (2 : ℤ) = 1 := by
    rw [← zpow_add, ← zpow_add]; norm_num
  rw [h1]
  simp

include hσ in
theorem slLong_HSL_mem_hHat (b : (fixedField σ.toRingHom)ˣ) :
    slLong σ.toRingHom hσ (HSL b) ∈ hHat σ.toRingHom (ng 0) := by
  show ((slLong σ.toRingHom hσ (HSL b) : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
    hHatE σ.toRingHom (ng 0)
  rw [slLong_val, slLongE_HSL]
  exact ⟨⟨Units.map (fixedField σ.toRingHom).subtype.toMonoidHom b,
    (mem_fixedUnits σ.toRingHom).2 (b : fixedField σ.toRingHom).2⟩, rfl⟩

omit hσ in
theorem d4X_eq_one_iff {i : Fin 6} {c : d43Par σ.toRingHom i} (hσ' : ∀ x, σ.toRingHom (σ.toRingHom (σ.toRingHom x)) = x) :
    d4X hσ' i c = 1 ↔ c = 0 := by
  let φ : d43Par σ.toRingHom i →+ Additive (twistedGroup σ.toRingHom) :=
    AddMonoidHom.mk' (fun c : d43Par σ.toRingHom i => Additive.ofMul (d4X hσ' i c)) fun a b =>
      congrArg Additive.ofMul (d4X_add hσ' i a b)
  have h0 : d4X hσ' i 0 = 1 := map_zero φ
  constructor
  · intro h
    exact d4X_injective hσ' i (h.trans h0.symm)
  · rintro rfl; exact h0

include hσ in
theorem eq_top_of_Q_element
    [Finite K] (h2 : (2 : K) ≠ 0)
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (hT : (⨆ i, hHat σ.toRingHom i) ≤ H)
    (c₁ c₃ c₅ : fixedField σ.toRingHom) (a₂ a₄ : K)
    (hy : d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅ ∈ H)
    (hne : a₂ ≠ 0 ∨ a₄ ≠ 0) : H = ⊤ := by
  have hlongX : ∀ (i : Fin 6) (c : d43Par σ.toRingHom i) (k : ℤ), (i : ℤ) + 1 = k →
      k % 2 = 0 → CFSG.GH74.BNPair.IsRoot 6 k → d4X hσ i c ∈ H := fun i c k hk hk2 hkr =>
    hlong (root_le_longSub hkr hk2 (d4X_mem_hexGroup' hσ i c hk))
  have hX1 : d4X hσ 1 c₁ ∈ H := hlongX 1 c₁ 2 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  have hX3 : d4X hσ 3 c₃ ∈ H := hlongX 3 c₃ 4 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  have hX5 : d4X hσ 5 c₅ ∈ H := hlongX 5 c₅ 6 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  have hc23 : d4X hσ 2 a₂ * d4X hσ 3 c₃ = d4X hσ 3 c₃ * d4X hσ 2 a₂ :=
    ((d4Rel_model hσ).c23 a₂ c₃).eq
  have hs : d4X hσ 2 a₂ * d4X hσ 4 a₄ ∈ H := by
    have e : d4X hσ 2 a₂ * d4X hσ 4 a₄ =
        (d4X hσ 3 c₃)⁻¹ * ((d4X hσ 1 c₁)⁻¹ *
          (d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅) *
            (d4X hσ 5 c₅)⁻¹) := by
      have e1 : (d4X hσ 3 c₃)⁻¹ * ((d4X hσ 1 c₁)⁻¹ *
          (d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅) *
            (d4X hσ 5 c₅)⁻¹) =
          (d4X hσ 3 c₃)⁻¹ * (d4X hσ 2 a₂ * d4X hσ 3 c₃) * d4X hσ 4 a₄ := by group
      rw [e1, hc23]; group
    rw [e]
    exact H.mul_mem (H.inv_mem hX3) (H.mul_mem (H.mul_mem (H.inv_mem hX1) hy) (H.inv_mem hX5))
  by_cases h0 : a₂ = 0
  · have ha4 : a₄ ≠ 0 := hne.resolve_left (by simpa using h0)
    have hX2 : d4X hσ 2 a₂ = 1 := (d4X_eq_one_iff hσ).2 h0
    rw [hX2, one_mul] at hs
    exact eq_top_of_long_torus_short hσ h2 H hlong hT (k := 5) (Or.inr (Or.inl rfl))
      (d4X_mem_hexGroup' hσ 4 a₄ (by norm_num)) hs (fun h => ha4 ((d4X_eq_one_iff hσ).1 h))
  · obtain ⟨a, ha1⟩ := ha
    set aK : Kˣ := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom a with haK_def
    have haK : Units.map σ.toRingHom.toMonoidHom aK = aK := fixed_unit_map_fix a
    have hτs : slShort σ.toRingHom hσ (HSL aK) ∈ H :=
      hT (Subgroup.mem_iSup_of_mem (ng 1) (slShort_HSL_mem_hHat hσ aK))
    have hτl : slLong σ.toRingHom hσ (HSL a) ∈ H :=
      hT (Subgroup.mem_iSup_of_mem (ng 0) (slLong_HSL_mem_hHat hσ a))
    set τ := slShort σ.toRingHom hσ (HSL aK) * slLong σ.toRingHom hσ (HSL a) with hτ
    have hτH : τ ∈ H := H.mul_mem hτs hτl
    have hmul : ((aK⁻¹ : Kˣ) : K) * ((a : fixedField σ.toRingHom) : K) = 1 := by
      have : ((aK : Kˣ) : K) = ((a : fixedField σ.toRingHom) : K) := rfl
      rw [← this]; exact Units.inv_mul aK
    have w4 : ∀ u : K, τ * d4X hσ 4 u * τ⁻¹ = d4X hσ 4 u := by
      intro u
      have e : τ * d4X hσ 4 u * τ⁻¹ = slShort σ.toRingHom hσ (HSL aK) *
          (slLong σ.toRingHom hσ (HSL a) * d4X hσ 4 u * (slLong σ.toRingHom hσ (HSL a))⁻¹) *
            (slShort σ.toRingHom hσ (HSL aK))⁻¹ := by rw [hτ]; group
      rw [e, conj_slLong_pos4 hσ a u, conj_slShort_pos4 hσ aK haK,
        ← mul_assoc, hmul, one_mul]
    have w2 : ∀ u : K, τ * d4X hσ 2 u * τ⁻¹ = d4X hσ 2 (((aK : Kˣ) : K) * u) := by
      intro u
      have e : τ * d4X hσ 2 u * τ⁻¹ = slShort σ.toRingHom hσ (HSL aK) *
          (slLong σ.toRingHom hσ (HSL a) * d4X hσ 2 u * (slLong σ.toRingHom hσ (HSL a))⁻¹) *
            (slShort σ.toRingHom hσ (HSL aK))⁻¹ := by rw [hτ]; group
      rw [e, conj_slLong_pos2 hσ a u, conj_slShort_pos2 hσ aK haK]
    have hconj : τ * (d4X hσ 2 a₂ * d4X hσ 4 a₄) * τ⁻¹ =
        d4X hσ 2 (((aK : Kˣ) : K) * a₂) * d4X hσ 4 a₄ := by
      have e : τ * (d4X hσ 2 a₂ * d4X hσ 4 a₄) * τ⁻¹ =
          (τ * d4X hσ 2 a₂ * τ⁻¹) * (τ * d4X hσ 4 a₄ * τ⁻¹) := by group
      rw [e, w2, w4]
    have hw : d4X hσ 2 (((aK : Kˣ) : K) * a₂) * (d4X hσ 2 a₂)⁻¹ =
        d4X hσ 2 ((((aK : Kˣ) : K) - 1) * a₂) := by
      have h := d4X_add hσ (2 : Fin 6) ((((aK : Kˣ) : K) - 1) * a₂) a₂
      have e : (((aK : Kˣ) : K) - 1) * a₂ + a₂ = ((aK : Kˣ) : K) * a₂ := by ring
      have h' : d4X hσ 2 (((aK : Kˣ) : K) * a₂) =
          d4X hσ 2 ((((aK : Kˣ) : K) - 1) * a₂) * d4X hσ 2 a₂ :=
        (congrArg (fun c : K => d4X hσ 2 c) e.symm).trans h
      rw [h']; group
    have hmemw : d4X hσ 2 (((aK : Kˣ) : K) * a₂) * (d4X hσ 2 a₂)⁻¹ ∈ H := by
      have h1 : τ * (d4X hσ 2 a₂ * d4X hσ 4 a₄) * τ⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hτH hs) (H.inv_mem hτH)
      rw [hconj] at h1
      have h2' := H.mul_mem h1 (H.inv_mem hs)
      have e : d4X hσ 2 (((aK : Kˣ) : K) * a₂) * d4X hσ 4 a₄ *
          (d4X hσ 2 a₂ * d4X hσ 4 a₄)⁻¹ =
          d4X hσ 2 (((aK : Kˣ) : K) * a₂) * (d4X hσ 2 a₂)⁻¹ := by group
      rwa [e] at h2'
    rw [hw] at hmemw
    have hne1 : (((aK : Kˣ) : K) - 1) * a₂ ≠ 0 := by
      refine mul_ne_zero (fun h => ha1 ?_) h0
      have : ((aK : Kˣ) : K) = 1 := sub_eq_zero.1 h
      exact Subtype.ext this
    exact eq_top_of_long_torus_short hσ h2 H hlong hT (k := 3) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (d4X_mem_hexGroup' hσ 2 _ (by norm_num)) hmemw (fun h => hne1 ((d4X_eq_one_iff hσ).1 h))

end ShortExtract

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
