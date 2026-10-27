module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.BruhatPoint
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4LongZ
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ExtractU

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed

section QForm


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

omit hσ in
theorem actsPos_rot {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
    {root : ℤ → Subgroup X} (R : RGD2 6 H r₁ r₂ U root) :
    ActsPos 6 root (r₂ * r₁) (fun q => q - 2) ∧ ActsPos 6 root (r₂ * r₁)⁻¹ (fun q => q + 2) := by
  have a₁ : ActsPos 6 root r₁ (fun q => 6 - q) := by simpa using R.actsPos_r₁
  have a₁' : ActsPos 6 root r₁⁻¹ (fun q => 6 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁
  have a₂ : ActsPos 6 root r₂ (fun q => 4 - q) := by simpa using R.actsPos_r₂
  have a₂' : ActsPos 6 root r₂⁻¹ (fun q => 4 - q) := by
    simpa using R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂
  refine ⟨ActsPos.of_eq (ActsPos.mul a₂ a₁) fun q => by ring, ?_⟩
  rw [mul_inv_rev]
  exact ActsPos.of_eq (ActsPos.mul a₁' a₂') fun q => by ring

omit hσ in
theorem Rt6_aux : Rt 6 5 = 6 ∧ Rt 6 3 = 4 ∧ Rt 6 11 = -6 ∧ Rt 6 9 = -4 ∧ Rt 6 2 = 3 ∧
    Rt 6 4 = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Rt_of_lt (by norm_num) (by norm_num)]; norm_num

include hσ in
theorem hHat_zero_le_sup :
    hHat σ.toRingHom (ng 0) ≤ hexGroup (twistedX σ.toRingHom) 6 ⊔
      hexGroup (twistedX σ.toRingHom) (-6) := by
  refine (hHat_le_rankOne hσ (ng 0)).trans (sup_le ?_ ?_)
  · have h : twistedRootGroup σ.toRingHom (hexPos 6) ≤ hexGroup (twistedX σ.toRingHom) 6 ⊔
        hexGroup (twistedX σ.toRingHom) (-6) := le_sup_left
    rwa [hexPos_six_eq_single] at h
  · have h : twistedRootGroup σ.toRingHom (hexPos (-6)) ≤ hexGroup (twistedX σ.toRingHom) 6 ⊔
        hexGroup (twistedX σ.toRingHom) (-6) := le_sup_right
    rwa [hexPos_neg_six_eq_single] at h

include hσ in
theorem eq_top_of_short_pair
    [Finite K] (h2 : (2 : K) ≠ 0)
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (hT : (⨆ i, hHat σ.toRingHom i) ≤ H) (a₂ a₄ : K)
    (hs : d4X hσ 2 a₂ * d4X hσ 4 a₄ ∈ H) (hne : a₂ ≠ 0 ∨ a₄ ≠ 0) : H = ⊤ := by
  have e1 : d4X hσ 1 (0 : fixedField σ.toRingHom) = 1 := (d4X_eq_one_iff hσ).2 rfl
  have e3 : d4X hσ 3 (0 : fixedField σ.toRingHom) = 1 := (d4X_eq_one_iff hσ).2 rfl
  have e5 : d4X hσ 5 (0 : fixedField σ.toRingHom) = 1 := (d4X_eq_one_iff hσ).2 rfl
  refine eq_top_of_Q_element hσ h2 ha H hlong hT 0 0 0 a₂ a₄ ?_ hne
  rw [e1, e3, e5]
  convert hs using 1

include hσ in
theorem exists_theta_torus
    (b : (fixedField σ.toRingHom)ˣ)
    (hb : (b : fixedField σ.toRingHom) ≠ 1) :
    ∃ h : twistedGroup σ.toRingHom, h ∈ ⨆ i, hHat σ.toRingHom i ∧
      h ∈ hexGroup (twistedX σ.toRingHom) 4 ⊔ hexGroup (twistedX σ.toRingHom) (-4) ∧
      (∀ c : K, h * d4X hσ 2 c * h⁻¹ = d4X hσ 2 c → c = 0) ∧
      (∀ c : K, h * d4X hσ 4 c * h⁻¹ = d4X hσ 4 c → c = 0) := by
  have R := d4RGD2 σ.toRingHom hσ
  obtain ⟨hn, hn'⟩ := actsPos_rot R
  obtain ⟨v5, v3, v11, v9, v2, v4⟩ := Rt6_aux
  set n : twistedGroup σ.toRingHom := nHat σ.toRingHom 0 * nHat σ.toRingHom 1 with hndef
  set s : fixedUnits σ.toRingHom :=
    ⟨Units.map (fixedField σ.toRingHom).subtype.toMonoidHom b, fixed_unit_map_fix b⟩ with hsdef
  have hs1 : (s : Kˣ) ≠ 1 := by
    intro h
    apply hb
    have : Units.map (fixedField σ.toRingHom).subtype.toMonoidHom b = 1 := h
    have h' := congrArg (fun u : Kˣ => (u : K)) this
    exact Subtype.ext h'
  set ĥ := tor hσ s 1 with hĥdef
  have hĥ : ĥ ∈ hHat σ.toRingHom (ng 0) := d4z_tor_fixed_mem_hHat hσ s
  have hĥT : ĥ ∈ ⨆ i, hHat σ.toRingHom i := Subgroup.mem_iSup_of_mem (ng 0) hĥ
  have ff : ∀ (m : ℤ), m ≠ 0 → m.natAbs ≤ 6 → ¬ CFSG.Timmesfeld.RankTwo.d43Long (hexPos m) →
      chi σ.toRingHom (s : Kˣ) 1 (d43Lift (hexPos m)) ≠ 1 →
      ∀ x : twistedGroup σ.toRingHom, n⁻¹ * x * n⁻¹⁻¹ ∈ hexGroup (twistedX σ.toRingHom) m →
        n * ĥ * n⁻¹ * x * (n * ĥ * n⁻¹)⁻¹ = x → x = 1 := by
    intro m hm0 hm6 hl hχ x hxm hx
    have hfix : ĥ * (n⁻¹ * x * n⁻¹⁻¹) * ĥ⁻¹ = n⁻¹ * x * n⁻¹⁻¹ := by
      calc ĥ * (n⁻¹ * x * n⁻¹⁻¹) * ĥ⁻¹
          = n⁻¹ * ((n * ĥ * n⁻¹) * x * (n * ĥ * n⁻¹)⁻¹) * n⁻¹⁻¹ := by group
        _ = n⁻¹ * x * n⁻¹⁻¹ := by rw [hx]
    have h1 : n⁻¹ * x * n⁻¹⁻¹ = 1 :=
      d4z_tor_fix_short hσ s 1 (isRoot_hexPos hm0 hm6) hl hχ hxm hfix
    calc x = n * (n⁻¹ * x * n⁻¹⁻¹) * n⁻¹ := by group
      _ = 1 := by rw [h1]; group
  refine ⟨n * ĥ * n⁻¹, ?_, ?_, ?_, ?_⟩
  · have e : n * ĥ * n⁻¹ = nHat σ.toRingHom 0 * (nHat σ.toRingHom 1 * ĥ * (nHat σ.toRingHom 1)⁻¹) *
        (nHat σ.toRingHom 0)⁻¹ := by rw [hndef]; group
    rw [e]
    exact R.conj_H₂ _ (R.conj_H₁ _ hĥT)
  · have hsup : ĥ ∈ hexGroup (twistedX σ.toRingHom) 6 ⊔ hexGroup (twistedX σ.toRingHom) (-6) :=
      hHat_zero_le_sup hσ hĥ
    have hmap : (hexGroup (twistedX σ.toRingHom) 6 ⊔ hexGroup (twistedX σ.toRingHom) (-6)).map
        (MulAut.conj n).toMonoidHom ≤
        hexGroup (twistedX σ.toRingHom) 4 ⊔ hexGroup (twistedX σ.toRingHom) (-4) := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        have := hn 5 x (by rw [v5]; exact hx)
        dsimp only at this
        rwa [show (5 : ℤ) - 2 = 3 by norm_num, v3] at this
      · rintro _ ⟨x, hx, rfl⟩
        have := hn 11 x (by rw [v11]; exact hx)
        dsimp only at this
        rwa [show (11 : ℤ) - 2 = 9 by norm_num, v9] at this
    exact hmap ⟨ĥ, hsup, rfl⟩
  · intro c hc
    have hx : d4X hσ 2 c ∈ hexGroup (twistedX σ.toRingHom) 3 := d4X_mem_hexGroup' hσ 2 c (by norm_num)
    have hx' : n⁻¹ * d4X hσ 2 c * n⁻¹⁻¹ ∈ hexGroup (twistedX σ.toRingHom) 5 := by
      have := hn' 2 _ (by rw [v2]; exact hx)
      dsimp only at this
      rwa [show (2 : ℤ) + 2 = 4 by norm_num, v4] at this
    have hχ : chi σ.toRingHom (s : Kˣ) 1 (d43Lift (hexPos 5)) ≠ 1 := by
      have e : pr (nd 2) (d43Lift (hexPos 5)) = 1 := by decide +kernel
      simpa [chi, e] using hs1
    have h1 := ff 5 (by norm_num) (by norm_num)
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ _ hx' hc
    exact (d4X_eq_one_iff hσ).1 h1
  · intro c hc
    have hx : d4X hσ 4 c ∈ hexGroup (twistedX σ.toRingHom) 5 := d4X_mem_hexGroup' hσ 4 c (by norm_num)
    have hx' : n⁻¹ * d4X hσ 4 c * n⁻¹⁻¹ ∈ hexGroup (twistedX σ.toRingHom) (-1) := by
      have := hn' 4 _ (by rw [v4]; exact hx)
      dsimp only at this
      have v6 : Rt 6 6 = -1 := by rw [Rt_of_ge (by norm_num) (by norm_num)]; norm_num
      rwa [show (4 : ℤ) + 2 = 6 by norm_num, v6] at this
    have hχ : chi σ.toRingHom (s : Kˣ) 1 (d43Lift (hexPos (-1))) ≠ 1 := by
      have e : pr (nd 2) (d43Lift (hexPos (-1))) = 1 := by decide +kernel
      simpa [chi, e] using hs1
    have h1 := ff (-1) (by norm_num) (by norm_num)
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ _ hx' hc
    exact (d4X_eq_one_iff hσ).1 h1

include hσ in
theorem d4X_neg' (i : Fin 6) (c : d43Par σ.toRingHom i) : d4X hσ i (-c) = (d4X hσ i c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← d4X_add hσ i, neg_add_cancel]
  exact (d4X_eq_one_iff hσ).2 rfl

include hσ in
theorem eq_top_of_Q_point
    [Finite K] (h2 : (2 : K) ≠ 0)
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (hT : (⨆ i, hHat σ.toRingHom i) ≤ H) (a₂ a₄ : K) (hne : a₂ ≠ 0 ∨ a₄ ≠ 0)
    (hX : ∀ x ∈ hexGroup (twistedX σ.toRingHom) (-4),
      (d4X hσ 2 a₂ * d4X hσ 4 a₄) * x * (d4X hσ 2 a₂ * d4X hσ 4 a₄)⁻¹ ∈ H) : H = ⊤ := by
  have R := d4Rel_model hσ
  have RG := d4RGD2 σ.toRingHom hσ
  obtain ⟨b, hb⟩ := ha
  obtain ⟨h, hhT, hhS, hfix2, hfix4⟩ := exists_theta_torus hσ b hb
  set s : twistedGroup σ.toRingHom := d4X hσ 2 a₂ * d4X hσ 4 a₄ with hs
  have hsU : s ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)) :=
    mul_mem (d4X_mem_posUnipotent hσ 2 a₂) (d4X_mem_posUnipotent hσ 4 a₄)
  have hconj : h ∈ H.comap (MulAut.conj s).toMonoidHom := by
    have hle : hexGroup (twistedX σ.toRingHom) 4 ⊔ hexGroup (twistedX σ.toRingHom) (-4) ≤
        H.comap (MulAut.conj s).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro x hx
        have hc := commute_posUnipotent_hexGroup_four hσ hsU hx
        have : s * x * s⁻¹ = x := by rw [hc]; group
        show s * x * s⁻¹ ∈ H
        rw [this]
        exact hlong (root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (4 : ℤ)) (by norm_num) hx)
      · intro x hx
        exact hX x hx
    exact hle hhS
  have hconj' : s * h * s⁻¹ ∈ H := hconj
  have hhH : h ∈ H := hT hhT
  have hyH : s * h * s⁻¹ * h⁻¹ ∈ H := H.mul_mem hconj' (H.inv_mem hhH)
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K, h * d4X hσ 2 a₂ * h⁻¹ = d4X hσ 2 c₂ := by
    have hm := RG.invariant 3 ⟨by norm_num, by norm_num⟩ h hhT _
      (d4X_mem_hexGroup' hσ 2 a₂ (by norm_num))
    obtain ⟨c, hc⟩ := (mem_hexGroup_iff' hσ 2 (by norm_num : ((2 : Fin 6) : ℤ) + 1 = 3)).1 hm
    exact ⟨c, hc.symm⟩
  obtain ⟨c₄, hc₄⟩ : ∃ c₄ : K, h * d4X hσ 4 a₄ * h⁻¹ = d4X hσ 4 c₄ := by
    have hm := RG.invariant 5 ⟨by norm_num, by norm_num⟩ h hhT _
      (d4X_mem_hexGroup' hσ 4 a₄ (by norm_num))
    obtain ⟨c, hc⟩ := (mem_hexGroup_iff' hσ 4 (by norm_num : ((4 : Fin 6) : ℤ) + 1 = 5)).1 hm
    exact ⟨c, hc.symm⟩
  have hd2 : a₂ ≠ 0 → a₂ - c₂ ≠ 0 := by
    intro ha₂ hz
    have : c₂ = a₂ := (sub_eq_zero.1 hz).symm
    apply ha₂
    apply hfix2 a₂
    rw [hc₂, this]
  have hd4 : a₄ ≠ 0 → a₄ - c₄ ≠ 0 := by
    intro ha₄ hz
    have : c₄ = a₄ := (sub_eq_zero.1 hz).symm
    apply ha₄
    apply hfix4 a₄
    rw [hc₄, this]
  set d₂ : K := a₂ - c₂ with hd₂
  set d₄ : K := a₄ - c₄ with hd₄
  have hX2 : d4X hσ 2 d₂ = d4X hσ 2 a₂ * (d4X hσ 2 c₂)⁻¹ := by
    refine eq_mul_inv_of_mul_eq ?_
    exact (d4X_add hσ 2 d₂ c₂).symm.trans (congrArg (d4X hσ 2) (sub_add_cancel a₂ c₂))
  have hX4 : d4X hσ 4 d₄ = d4X hσ 4 a₄ * (d4X hσ 4 c₄)⁻¹ := by
    refine eq_mul_inv_of_mul_eq ?_
    exact (d4X_add hσ 4 d₄ c₄).symm.trans (congrArg (d4X hσ 4) (sub_add_cancel a₄ c₄))
  obtain ⟨e, he⟩ : ∃ e : fixedField σ.toRingHom,
      ⁅d4X hσ 4 d₄, (d4X hσ 2 c₂)⁻¹⁆ = d4X hσ 3 e := by
    have h24 := R.r24 (-c₂) d₄
    dsimp only at h24
    refine ⟨-(-d43Tr hσ (-c₂ * d₄)), ?_⟩
    have n2 : d4X hσ 2 (-c₂) = (d4X hσ 2 c₂)⁻¹ := d4X_neg' hσ 2 c₂
    have step1 : ⁅d4X hσ 4 d₄, (d4X hσ 2 c₂)⁻¹⁆ = (⁅d4X hσ 2 (-c₂), d4X hσ 4 d₄⁆)⁻¹ := by
      rw [← n2]
      exact (commutatorElement_inv _ _).symm
    exact step1.trans ((congrArg (·⁻¹) h24).trans (d4X_neg' hσ 3 (-d43Tr hσ (-c₂ * d₄))).symm)
  have hsh : s * h * s⁻¹ * h⁻¹ = d4X hσ 3 e * (d4X hσ 2 d₂ * d4X hσ 4 d₄) := by
    have e1 : h * s * h⁻¹ = d4X hσ 2 c₂ * d4X hσ 4 c₄ := by
      rw [hs, ← hc₂, ← hc₄]; group
    have e2 : s * h * s⁻¹ * h⁻¹ = s * (d4X hσ 2 c₂ * d4X hσ 4 c₄)⁻¹ := by
      rw [← e1]; group
    have c23 : d4X hσ 2 a₂ * d4X hσ 3 e = d4X hσ 3 e * d4X hσ 2 a₂ := (R.c23 a₂ e).eq
    have hcomm : d4X hσ 4 d₄ * (d4X hσ 2 c₂)⁻¹ =
        d4X hσ 3 e * ((d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄) := by
      rw [← he, commutatorElement_def]; group
    calc s * h * s⁻¹ * h⁻¹ = s * (d4X hσ 2 c₂ * d4X hσ 4 c₄)⁻¹ := e2
      _ = d4X hσ 2 a₂ * (d4X hσ 4 a₄ * (d4X hσ 4 c₄)⁻¹) * (d4X hσ 2 c₂)⁻¹ := by rw [hs]; group
      _ = d4X hσ 2 a₂ * d4X hσ 4 d₄ * (d4X hσ 2 c₂)⁻¹ := by rw [hX4]
      _ = d4X hσ 2 a₂ * (d4X hσ 4 d₄ * (d4X hσ 2 c₂)⁻¹) := by group
      _ = d4X hσ 2 a₂ * (d4X hσ 3 e * ((d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄)) := by rw [hcomm]
      _ = (d4X hσ 2 a₂ * d4X hσ 3 e) * ((d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄) := by group
      _ = d4X hσ 3 e * (d4X hσ 2 a₂ * (d4X hσ 2 c₂)⁻¹ * d4X hσ 4 d₄) := by rw [c23]; group
      _ = d4X hσ 3 e * (d4X hσ 2 d₂ * d4X hσ 4 d₄) := by rw [hX2]
  have hX3 : d4X hσ 3 e ∈ H :=
    hlong (root_le_longSub (⟨by norm_num, by norm_num⟩ : IsRoot 6 (4 : ℤ)) (by norm_num)
      (d4X_mem_hexGroup' hσ 3 e (by norm_num)))
  have hpair : d4X hσ 2 d₂ * d4X hσ 4 d₄ ∈ H := by
    have : d4X hσ 2 d₂ * d4X hσ 4 d₄ = (d4X hσ 3 e)⁻¹ * (s * h * s⁻¹ * h⁻¹) := by
      rw [hsh]; group
    rw [this]
    exact H.mul_mem (H.inv_mem hX3) hyH
  refine eq_top_of_short_pair hσ h2 ⟨b, hb⟩ H hlong hT d₂ d₄ hpair ?_
  rcases hne with h | h
  · exact Or.inl (hd2 h)
  · exact Or.inr (hd4 h)

end QForm

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
