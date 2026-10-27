module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJField
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2NativeCyclic
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPhi6

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.ClassicalInvolution.G2D4Models

theorem not_dvd_of_phi6 {q r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hq : 1 ≤ q)
    (h : r ∣ q ^ 2 - q + 1) : ¬ r ∣ q ∧ ¬ r ∣ q ^ 2 - 1 := by
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
  constructor
  · intro hrq
    have h1 : r ∣ q ^ 2 - q := Nat.dvd_sub (dvd_pow hrq (by norm_num)) hrq
    have h2 : r ∣ 1 := by
      have := (Nat.dvd_add_right h1).1 (by
        have e : q ^ 2 - q + 1 = (q ^ 2 - q) + 1 := rfl
        rw [← e]; exact h)
      exact this
    exact hr.one_lt.ne' (Nat.dvd_one.1 h2)
  · intro hr1
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have hq3 : 2 ≤ q := by
      by_contra hlt
      have : q = 1 := by omega
      subst this
      have h1 : r = 1 := by simpa using h
      exact hr.one_lt.ne' h1
    have h1 : r ∣ q - 2 := by
      have e : q ^ 2 - 1 = (q ^ 2 - q + 1) + (q - 2) := by
        have : q ≤ q ^ 2 := hqq
        omega
      rw [e] at hr1
      exact (Nat.dvd_add_right h).1 hr1
    have h3 : r ∣ 3 := by
      obtain ⟨m, hm⟩ := h1
      have hqm : q = 2 + r * m := by omega
      have e : q ^ 2 - q + 1 = 3 + r * (r * m * m + 3 * m) := by
        rw [hqm]
        have : (2 + r * m) ^ 2 + 1 = 3 + r * (r * m * m + 3 * m) + (2 + r * m) := by ring
        omega
      rw [e] at h
      exact (Nat.dvd_add_left (dvd_mul_right r _)).1 h
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem no_plane_in_JTw
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hq3 : 3 ≤ ℓ ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f)) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrq : r ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1)
    (E : Subgroup (twistedGroup σ.toRingHom)) (hEJ : E ≤ JTw σ.toRingHom)
    (hE : ∀ x ∈ E, x ^ r = 1) (hEc : Nat.card E = r ^ 2) : False := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hcardF : Nat.card (fixSubfield σ) = ℓ ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσq
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hcardF]
    exact_mod_cast (by omega : 3 ≤ ℓ ^ f)
  let f0 : ↥(JTw σ.toRingHom) →* ModGL TwistTag.D4.tag K :=
    (twistedIncl σ.toRingHom).comp (JTw σ.toRingHom).subtype
  have hf0 : ∀ x, f0 x ∈ trialityFieldImage σ σ := by
    intro x
    have hx : Units.map (entrywiseHom σ.toRingHom) (twistedIncl σ.toRingHom (x : _)) =
        twistedIncl σ.toRingHom (x : _) := x.2
    have hmem := twistedIncl_mem_root σ hK2 hq2 hK hσq
      (x : twistedGroup σ.toRingHom)
    exact (d4_mem_trialityFieldImage_self_iff σ hσ3 ⟨twistedIncl σ.toRingHom (x : _), hmem⟩).2
      (Subtype.ext (by rw [coe_fieldActor]; exact hx))
  let Θ : ↥(JTw σ.toRingHom) →* ↥(trialityFieldImage σ σ) := f0.codRestrict _ hf0
  have hΘ : Function.Injective Θ := by
    intro x y h
    have h1 : twistedIncl σ.toRingHom (x : _) = twistedIncl σ.toRingHom (y : _) :=
      congrArg (fun z : ↥(trialityFieldImage σ σ) => (z : ModGL TwistTag.D4.tag K)) h
    exact Subtype.ext (twistedIncl_injective σ.toRingHom h1)
  let Ψ : ↥(JTw σ.toRingHom) →* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (trialityFieldImageEquivG2 σ hk3).toMonoidHom.comp Θ
  have hΨ : Function.Injective Ψ := (trialityFieldImageEquivG2 σ hk3).injective.comp hΘ
  let E' : Subgroup ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (E.subgroupOf (JTw σ.toRingHom)).map Ψ
  have hcard' : Nat.card E' = r ^ 2 := by
    rw [← hEc]
    refine (Nat.card_congr ((Subgroup.equivMapOfInjective _ Ψ hΨ).toEquiv)).symm.trans ?_
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  have hE' : ∀ x ∈ E', x ^ r = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    have : y ^ r = 1 := Subtype.ext (hE y.1 hy)
    rw [this, map_one]
  obtain ⟨hrq0, hrq1⟩ := not_dvd_of_phi6 hr hr5 (by omega) hrq
  exact CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.false_of_isElemAbelian_sq_cyclotomic
    (fixSubfield σ) hr hr5 (by rwa [hcardF]) (by rwa [hcardF]) hE' hcard'

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
