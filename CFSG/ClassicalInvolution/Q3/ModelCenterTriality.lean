module

public import CFSG.ClassicalInvolution.Q3.OddCentralizerFree
public import CFSG.ClassicalInvolution.Q3.ModelCenterClassical
public import CFSG.LieType.Steinberg.TwistedD4.Bruhat
public import CFSG.LieType.Steinberg.TwistedD4.Perfect

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section TwistedD4

variable {K : Type} [Field K] {σ : K →+* K}

variable (σ) in
@[expose] def d4CharVal (t s : Kˣ) (l : Fin d4.rank) : K :=
  ((t ^ d4.cartan (nd 2) l : Kˣ) : K) * (((s ^ d4.cartan (nd 0) l : Kˣ) : K) *
    (((Units.map σ.toMonoidHom s ^ d4.cartan (nd 1) l : Kˣ) : K) *
      ((Units.map σ.toMonoidHom (Units.map σ.toMonoidHom s) ^ d4.cartan (nd 3) l : Kˣ) : K)))

theorem conj_xElement_d4Torus (t s : Kˣ) (l : Fin d4.rank) (c : K) :
    (torusElement d4 K (nd 2) t * hShortHom σ s) * xElement l c *
        (torusElement d4 K (nd 2) t * hShortHom σ s)⁻¹ = xElement l (d4CharVal σ t s l * c) := by
  rw [hShortHom_apply]
  have e : ∀ a b x : adjointGroup d4 K, a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ :=
    fun a b x => by group
  rw [e, torus3_conj_xElement (t := .D4), torusElement_conj_xElement, d4CharVal]
  congr 1
  ring

theorem xOuter_one_eq_xElement (c d e : K) :
    xOuter 1 c d e = xElement (nd 0) c * xElement (nd 1) d * xElement (nd 3) e := by
  simp only [xOuter, one_smul, xPar_simple, eltElement_simpleRoot]

theorem eq_one_of_d4_char_eqs {a x y w : K} (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (e0 : a⁻¹ * x ^ 2 = 1) (e1 : a⁻¹ * y ^ 2 = 1) (e3 : a⁻¹ * w ^ 2 = 1)
    (e2 : a ^ 2 * (x⁻¹ * (y⁻¹ * w⁻¹)) = 1) : a = 1 ∧ x ^ 2 = 1 := by
  have h0 : x ^ 2 = a := by field_simp at e0; linear_combination e0
  have h1 : y ^ 2 = a := by field_simp at e1; linear_combination e1
  have h3 : w ^ 2 = a := by field_simp at e3; linear_combination e3
  have h2 : a ^ 2 = x * (y * w) := by field_simp at e2; linear_combination e2
  have h4 : a ^ 4 = a ^ 3 := by
    calc a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (x * (y * w)) ^ 2 := by rw [h2]
      _ = x ^ 2 * y ^ 2 * w ^ 2 := by ring
      _ = a ^ 3 := by rw [h0, h1, h3]; ring
  have ha1 : a = 1 := by
    have : a ^ 3 * (a - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ha
    · linear_combination h
  exact ⟨ha1, by rw [h0, ha1]⟩

theorem d4CharVal_nd0 (t s : Kˣ) : d4CharVal σ t s (nd 0) = (t : K)⁻¹ * (s : K) ^ 2 := by
  simp only [d4CharVal, show d4.cartan (nd 2) (nd 0) = -1 by decide, Int.reduceNeg, zpow_neg,
    zpow_ofNat, pow_one, Units.val_inv_eq_inv_val, show d4.cartan (nd 0) (nd 0) = 2 by decide,
    Units.val_pow_eq_pow_val, RingHom.toMonoidHom_eq_coe,
    show d4.cartan (nd 1) (nd 0) = 0 by decide, pow_zero, Units.val_one,
    show d4.cartan (nd 3) (nd 0) = 0 by decide, mul_one]

theorem d4CharVal_nd1 (t s : Kˣ) : d4CharVal σ t s (nd 1) = (t : K)⁻¹ * (σ s) ^ 2 := by
  simp only [d4CharVal, show d4.cartan (nd 2) (nd 1) = -1 by decide, Int.reduceNeg, zpow_neg,
    zpow_ofNat, pow_one, Units.val_inv_eq_inv_val, show d4.cartan (nd 0) (nd 1) = 0 by decide,
    pow_zero, Units.val_one, RingHom.toMonoidHom_eq_coe,
    show d4.cartan (nd 1) (nd 1) = 2 by decide, Units.val_pow_eq_pow_val, Units.coe_map,
    MonoidHom.coe_ofClass, show d4.cartan (nd 3) (nd 1) = 0 by decide, mul_one, one_mul]

theorem d4CharVal_nd3 (t s : Kˣ) : d4CharVal σ t s (nd 3) = (t : K)⁻¹ * (σ (σ s)) ^ 2 := by
  simp only [d4CharVal, show d4.cartan (nd 2) (nd 3) = -1 by decide, Int.reduceNeg, zpow_neg,
    zpow_ofNat, pow_one, Units.val_inv_eq_inv_val, show d4.cartan (nd 0) (nd 3) = 0 by decide,
    pow_zero, Units.val_one, RingHom.toMonoidHom_eq_coe,
    show d4.cartan (nd 1) (nd 3) = 0 by decide, show d4.cartan (nd 3) (nd 3) = 2 by decide,
    Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass, one_mul]

theorem d4CharVal_nd2 (t s : Kˣ) :
    d4CharVal σ t s (nd 2) = (t : K) ^ 2 * ((s : K)⁻¹ * ((σ s)⁻¹ * (σ (σ s))⁻¹)) := by
  simp only [d4CharVal, show d4.cartan (nd 2) (nd 2) = 2 by decide, zpow_ofNat,
    Units.val_pow_eq_pow_val, show d4.cartan (nd 0) (nd 2) = -1 by decide, Int.reduceNeg, zpow_neg,
    pow_one, Units.val_inv_eq_inv_val, RingHom.toMonoidHom_eq_coe,
    show d4.cartan (nd 1) (nd 2) = -1 by decide, Units.coe_map, MonoidHom.coe_ofClass,
    show d4.cartan (nd 3) (nd 2) = -1 by decide]

theorem sq_eq_one_of_central_torus (hσ : ∀ c, σ (σ (σ c)) = c) {z : twistedGroup σ}
    (hzT : z ∈ ⨆ i, hHat σ i) (hz : z ∈ Subgroup.center (twistedGroup σ)) : z ^ 2 = 1 := by
  have hle : (⨆ i, hHat σ i : Subgroup (twistedGroup σ)) ≤ hHat σ (ng 0) ⊔ hHat σ (ng 1) := by
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute
    (fun a ha b hb => (hHat_commute σ ha hb).eq)).1 (hle hzT)
  obtain ⟨t, ht⟩ : ∃ t : fixedUnits σ, hLongHom σ t = (a : adjointGroup d4 K) :=
    Subgroup.mem_subgroupOf.mp ha
  obtain ⟨s, hs⟩ : ∃ s : Kˣ, hShortHom σ s = (b : adjointGroup d4 K) :=
    Subgroup.mem_subgroupOf.mp hb
  have hzA : (a : adjointGroup d4 K) * (b : adjointGroup d4 K) =
      torusElement d4 K (nd 2) (t : Kˣ) * hShortHom σ s := by
    rw [← ht, ← hs]
    rfl
  obtain ⟨u₂, -, hu₂⟩ := exists_xLong hσ (c := (1 : K)) (map_one σ)
  have hu₁ : ((slShort σ hσ (sl2Upper (1 : K)) : twistedGroup σ) : adjointGroup d4 K) =
      xOuter 1 1 1 1 := by
    rw [slShort_upper, map_one, map_one]
  have hc₁ := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (slShort σ hσ (sl2Upper (1 : K))))
  have hc₂ := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz u₂)
  simp only [Subgroup.coe_mul] at hc₁ hc₂
  rw [hzA, hu₁] at hc₁
  rw [hzA, hu₂, xPar_simple, eltElement_simpleRoot] at hc₂
  set T : Kˣ := (t : Kˣ) with hT
  set W : adjointGroup d4 K := torusElement d4 K (nd 2) T * hShortHom σ s with hW
  have hx₁ : xOuter 1 (d4CharVal σ T s (nd 0) * 1) (d4CharVal σ T s (nd 1) * 1)
      (d4CharVal σ T s (nd 3) * 1) = xOuter 1 1 1 1 := by
    have e : ∀ p q r : adjointGroup d4 K,
        W * (p * q * r) * W⁻¹ = (W * p * W⁻¹) * (W * q * W⁻¹) * (W * r * W⁻¹) := fun p q r => by
      group
    have h1 : W * xOuter 1 1 1 1 * W⁻¹ = xOuter 1 1 1 1 := by
      rw [← hc₁]
      group
    rw [← h1, xOuter_one_eq_xElement, xOuter_one_eq_xElement, e, hW, conj_xElement_d4Torus,
      conj_xElement_d4Torus, conj_xElement_d4Torus]
  obtain ⟨e0, e1, e3⟩ := xOuter_inj (Or.inl rfl) hx₁
  have hx₂ : xElement (nd 2) (d4CharVal σ T s (nd 2) * 1) = xElement (nd 2) 1 := by
    have h1 : W * xElement (nd 2) 1 * W⁻¹ = xElement (nd 2) 1 := by
      rw [← hc₂]
      group
    rw [← h1, hW, conj_xElement_d4Torus]
  have e2 := xElement_injective (nd 2) hx₂
  rw [d4CharVal_nd0, mul_one] at e0
  rw [d4CharVal_nd1, mul_one] at e1
  rw [d4CharVal_nd3, mul_one] at e3
  rw [d4CharVal_nd2, mul_one] at e2
  have hy : σ s ≠ 0 := (Units.map σ.toMonoidHom s).ne_zero
  have hw : σ (σ s) ≠ 0 := (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom s)).ne_zero
  obtain ⟨hT1, hs2⟩ := eq_one_of_d4_char_eqs T.ne_zero s.ne_zero hy hw e0 e1 e3 e2
  have hT' : T = 1 := Units.ext hT1
  have ht1 : t = 1 := Subtype.ext hT'
  have hs' : s ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hs2, Units.val_one])
  have ha1 : a = 1 := by
    apply Subtype.ext
    rw [← ht, ht1, map_one]
    rfl
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hs, ← map_pow, hs', map_one]
    rfl
  rw [ha1, one_mul]
  exact hb2

theorem centerExp_twistedGroup (hσ : ∀ c, σ (σ (σ c)) = c) : CenterExp (twistedGroup σ) 1 := by
  intro z hz
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  have hBU := twistedDatum_bruhatExtras σ
  have h1 := (center_eq_normalCore_borel hct hext hBU) ▸ hz
  rw [pow_one]
  exact sq_eq_one_of_central_torus hσ (normalCore_borel_le_iSup hct hBU h1) hz

end TwistedD4

theorem centerExp_model_trialityD4 {p f n : ℕ} [hpf : Fact p.Prime] (hf : 1 ≤ f) :
    CenterExp (modelUniv .trialityD4 n p f hpf.out).K 1 := by
  have hK : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
    rw [GaloisField.card p (3 * f) (by omega), pow_mul']
  have hσq : ∀ c, iterateFrobenius (GaloisField p (3 * f)) p f c = c ^ p ^ f :=
    fun c => iterateFrobenius_def p f c
  exact centerExp_twistedGroup (sigma_three_of_card hK hσq)

end CFSG.ClassicalInvolution.Q3
