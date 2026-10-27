module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBMain
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBSL2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBBridge
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingOddProved
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllField
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1Long

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.HardMathSupport.Seitz.TrialityOdd CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.CurtisTits CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Lang.E6Descent CFSG.Fischer
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open scoped MatrixGroups

section Closing

theorem triOdd_closing_gamma {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hClose : Inner.LongTorusClosing σ.toRingHom)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (s : (fixedField σ.toRingHom)ˣ) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hslinj : Function.Injective (slShort σ.toRingHom hσ3))
    (t : Kˣ) (ht : t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s)
    (v : twistedGroup σ.toRingHom) (hv : v = slShort σ.toRingHom hσ3 (HSL t))
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hCH : Subgroup.centralizer ({v} : Set (twistedGroup σ.toRingHom)) ≤ H)
    (y : twistedGroup σ.toRingHom) (hyH : y ∈ H)
    (hy : y * v * y⁻¹ ∉ Subgroup.zpowers v) : H = ⊤ := by
  classical
  subst hv
  have htK : (t : K) = ((s : fixedField σ.toRingHom) : K) := by rw [ht]; rfl
  have htσ : σ.toRingHom (t : K) = t := by
    rw [htK]
    exact (s : fixedField σ.toRingHom).2
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hs3, map_one]
  have hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1 := by
    rw [htσ, htσ]
    have := congrArg Units.val ht3
    simpa [pow_succ, mul_assoc] using this
  have hLc := Inner.longSub_le_centralizer_slShort_HSL hσ3 t hnorm
  have hvL : slShort σ.toRingHom hσ3 (HSL t) ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) := by
    have := slShort_HSL_fixed_mem_longSub hσ3 s
    rwa [← ht] at this
  have hv1 : slShort σ.toRingHom hσ3 (HSL t) ≠ 1 := by
    intro h
    have h1 : HSL t = 1 := hslinj (h.trans (map_one _).symm)
    have h2 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => (M 0 0 : K)) h1
    have ht1 : (t : K) = 1 := by simpa [HSL] using h2
    have hs1' : s = 1 := by
      apply Units.ext
      apply Subtype.ext
      rw [← htK]
      simpa using ht1
    exact hs1 hs1'
  have hvc : ∀ l ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)),
      slShort σ.toRingHom hσ3 (HSL t) * l = l * slShort σ.toRingHom hσ3 (HSL t) := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hLc hl)).symm
  have hLH : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H := fun l hl => hCH (hLc hl)
  have hTH : (⨆ i, hHat σ.toRingHom i) ≤ H := by
    refine iSup_le fun i h hh => hCH ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hHat_commute σ.toRingHom hh (Inner.slShort_HSL_mem_hHat hσ3 t)).eq
  have hyN : y ∉ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) := by
    intro hyN
    apply hy
    have hmem : ∀ l, l ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) ↔
        y * l * y⁻¹ ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) := fun l =>
      Subgroup.mem_normalizer_iff.1 hyN l
    refine mem_zpowers_of_central_longSub hσ3 hvL hvc hv1 ((hmem _).1 hvL) ?_
    intro l hl
    have hl' : y⁻¹ * l * y ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) := by
      have := (hmem (y⁻¹ * l * y)).1.mt
      by_contra hn
      have h2 : y * (y⁻¹ * l * y) * y⁻¹ ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) := by
        have e : y * (y⁻¹ * l * y) * y⁻¹ = l := by group
        rw [e]; exact hl
      exact hn ((hmem _).2 h2)
    have h1 := hvc _ hl'
    calc y * slShort σ.toRingHom hσ3 (HSL t) * y⁻¹ * l
        = y * (slShort σ.toRingHom hσ3 (HSL t) * (y⁻¹ * l * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * l * y) * slShort σ.toRingHom hσ3 (HSL t)) * y⁻¹ := by rw [h1]
      _ = l * (y * slShort σ.toRingHom hσ3 (HSL t) * y⁻¹) := by group
  exact hClose H hLH hTH ⟨y, hyH, hyN⟩

theorem triOddClosingXPlus_holds : TriOddClosingXPlus := by
  intro ℓ f hℓ hℓ2 hℓ3 hf hq K _ _ hK σ hσ z hz3 hz1 hzX H hCH ⟨y, hyH, hy⟩
  classical
  have hK2 : ringChar K ≠ 2 := triOdd_ringChar_ne_two hℓ hℓ2 hf hK
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card (σ := σ.toRingHom) hK hσ'
  have hFcard : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    card_fixedField_of_cube σ.toRingHom hq2 hK hσ'
  obtain ⟨s, hs3, hs1⟩ := exists_cube_root_unit_finite (K := fixedField σ.toRingHom)
    (by rw [hFcard]; omega)
  set t : Kˣ := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s with ht
  have htK : (t : K) = ((s : fixedField σ.toRingHom) : K) := by rw [ht]; rfl
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hs3, map_one]
  have ht1 : t ≠ 1 := fun h => hs1 (by
    apply Units.ext
    apply Subtype.ext
    rw [← htK, h]
    rfl)
  set ε₀ := triOddEqRoot σ hK2 hq2 hK hσ with hε₀
  obtain ⟨h, hh⟩ := hzX
  obtain ⟨M, hM⟩ := triOdd_Asub_eq_eqRoot_slShort σ hℓ hℓ2 hℓ3 hf hK hσ hσ3 _ hh
  have hhz3 : (h * z * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3]; group
  have hM3 : M ^ 3 = 1 := by
    apply triOdd_slShort_injective σ hσ3
    apply ε₀.injective
    rw [map_pow, map_pow, hM, hhz3, map_one, map_one]
  have hM1 : M ≠ 1 := by
    intro hM1
    rw [hM1, map_one, map_one] at hM
    apply hz1
    have : h * z * h⁻¹ = 1 := hM.symm
    have h2 : z = h⁻¹ * (h * z * h⁻¹) * h := by group
    rw [h2, this]; group
  obtain ⟨P, hP⟩ := triOdd_sl2_conj_hsl t ht3 ht1 M hM3 hM1
  set g : C0 σ := ε₀ (slShort σ.toRingHom hσ3 P) * h with hg
  have hgz : g * z * g⁻¹ = ε₀ (slShort σ.toRingHom hσ3 (HSL t)) := by
    rw [← hP, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hM, hg]
    group
  let φ : twistedGroup σ.toRingHom →* C0 σ :=
    (MulAut.conj g⁻¹).toMonoidHom.comp ε₀.toMonoidHom
  have hφ : ∀ x, φ x = g⁻¹ * ε₀ x * g := fun x => by
    show g⁻¹ * ε₀ x * g⁻¹⁻¹ = _
    rw [inv_inv]
  have hφv : φ (slShort σ.toRingHom hσ3 (HSL t)) = z := by
    rw [hφ, ← hgz]; group
  have hClose := longTorusClosingOdd_proved ℓ f hℓ hℓ2 hf K hK σ hσ
  have hCH'' : Subgroup.centralizer ({slShort σ.toRingHom hσ3 (HSL t)} :
      Set (twistedGroup σ.toRingHom)) ≤ H.comap φ := by
    intro w hw
    rw [Subgroup.mem_comap]
    apply hCH
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    have h1 := congrArg ε₀ hw
    rw [map_mul, map_mul, ← hgz] at h1
    calc φ w * z = g⁻¹ * (ε₀ w * (g * z * g⁻¹)) * g := by rw [hφ]; group
      _ = g⁻¹ * ((g * z * g⁻¹) * ε₀ w) * g := by rw [h1]
      _ = z * φ w := by rw [hφ]; group
  have hy''H : ε₀.symm (g * y * g⁻¹) ∈ H.comap φ := by
    rw [Subgroup.mem_comap, hφ, MulEquiv.apply_symm_apply]
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e]
    exact hyH
  have hy'' : ε₀.symm (g * y * g⁻¹) * slShort σ.toRingHom hσ3 (HSL t) *
      (ε₀.symm (g * y * g⁻¹))⁻¹ ∉ Subgroup.zpowers (slShort σ.toRingHom hσ3 (HSL t)) := by
    intro hcon
    apply hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcon
    have h1 := congrArg φ hk
    have hφy : φ (ε₀.symm (g * y * g⁻¹)) = y := by
      rw [hφ, MulEquiv.apply_symm_apply]; group
    rw [map_zpow, map_mul, map_mul, map_inv, hφy, hφv] at h1
    exact Subgroup.mem_zpowers_iff.2 ⟨k, h1⟩
  have htop := triOdd_closing_gamma σ hClose hσ3 s hs3 hs1 (triOdd_slShort_injective σ hσ3) t ht
    (slShort σ.toRingHom hσ3 (HSL t)) rfl (H.comap φ) hCH'' _ hy''H hy''
  rw [eq_top_iff]
  intro w _
  have hw : ε₀.symm (g * w * g⁻¹) ∈ H.comap φ := by rw [htop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_comap, hφ, MulEquiv.apply_symm_apply] at hw
  have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
  rw [e] at hw
  exact hw

end Closing

end CFSG.LieType.SeitzGeneration.ExcWideThree
