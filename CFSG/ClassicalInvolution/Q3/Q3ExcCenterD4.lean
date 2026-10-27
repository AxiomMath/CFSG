module

public import CFSG.ClassicalInvolution.Q3.ModelCenterTriality
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section TwistedD4

variable {K : Type} [Field K] {σ : K →+* K}

theorem exc3_eq_one_of_central_torus (hσ : ∀ c, σ (σ (σ c)) = c) (h2 : (2 : K) ≠ 0)
    {z : twistedGroup σ}
    (hzT : z ∈ ⨆ i, hHat σ i) (hz : z ∈ Subgroup.center (twistedGroup σ)) : z = 1 := by
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
  have hs1 : (s : K) = 1 := by
    have hfac : ((s : K) - 1) * ((s : K) + 1) = 0 := by linear_combination hs2
    rcases mul_eq_zero.1 hfac with h | h
    · linear_combination h
    · exfalso
      have hsn : (s : K) = -1 := by linear_combination h
      have hσs : σ (s : K) = -1 := by rw [hsn, map_neg, map_one]
      have hσσs : σ (σ (s : K)) = -1 := by rw [hσs, map_neg, map_one]
      rw [hT1, hσσs, hσs, hsn] at e2
      apply h2
      have : ((-1 : K))⁻¹ * (((-1 : K))⁻¹ * ((-1 : K))⁻¹) = -1 := by
        rw [inv_neg, inv_one]
        ring
      rw [this] at e2
      linear_combination -e2
  have hs' : s = 1 := Units.ext hs1
  have ha1 : a = 1 := by
    apply Subtype.ext
    rw [← ht, ht1, map_one]
    rfl
  have hb1 : b = 1 := by
    apply Subtype.ext
    rw [← hs, hs', map_one]
    rfl
  rw [ha1, hb1, one_mul]

theorem exc3_center_twistedGroup (hσ : ∀ c, σ (σ (σ c)) = c) (h2 : (2 : K) ≠ 0) :
    Subgroup.center (twistedGroup σ) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  have hBU := twistedDatum_bruhatExtras σ
  have h1 := (center_eq_normalCore_borel hct hext hBU) ▸ hz
  rw [Subgroup.mem_bot]
  exact exc3_eq_one_of_central_torus hσ h2 (normalCore_borel_le_iSup hct hBU h1) hz

end TwistedD4

theorem exc3_center_trialityD4 (n : ℕ) (hp : Nat.Prime 3) :
    Subgroup.center (modelUniv .trialityD4 n 3 1 hp).K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hK : Nat.card (GaloisField 3 (3 * 1)) = (3 ^ 1) ^ 3 := by
    rw [GaloisField.card 3 (3 * 1) (by norm_num), pow_mul']
  have hσq : ∀ c, iterateFrobenius (GaloisField 3 (3 * 1)) 3 1 c = c ^ 3 ^ 1 :=
    fun c => iterateFrobenius_def 3 1 c
  have h2 : (2 : GaloisField 3 (3 * 1)) ≠ 0 :=
    ModelFacts.two_ne_zero_galoisField (3 * 1) (by norm_num)
  exact exc3_center_twistedGroup (sigma_three_of_card hK hσq) h2

end CFSG.ClassicalInvolution.Q3
