module

public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4


noncomputable def twistedGroupEquivFixed {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) (σ : K →+* K) (hσq : ∀ c, σ c = c ^ q) :
    twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 K σ :=
  (Subgroup.equivMapOfInjective (twistedGroup σ) (adjointGroup d4 K).subtype
    Subtype.val_injective).trans
    (MulEquiv.subgroupCongr
      (CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup hK2 hq
        hK hσq))

theorem exists_twistedGroup_mulEquiv_galois {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nonempty (twistedGroup σ ≃* twistedGroup (iterateFrobenius (GaloisField p (3 * f)) p f)) := by
  classical
  have hq2 : 2 ≤ p ^ f := le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp.out
      (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hGF : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
    rw [GaloisField.card p (3 * f) (by omega), pow_mul']
  have : Finite (GaloisField p (3 * f)) := Nat.finite_of_card_ne_zero (by rw [hGF]; positivity)
  have : CharP (GaloisField p (3 * f)) p := inferInstance
  have hGF2 : ringChar (GaloisField p (3 * f)) ≠ 2 := by
    rw [ringChar.eq (GaloisField p (3 * f)) p]; exact hp2
  have hsig : ∀ c : GaloisField p (3 * f),
      iterateFrobenius (GaloisField p (3 * f)) p f c = c ^ (p ^ f) :=
    fun c => iterateFrobenius_def p f c
  let θ : K ≃+* GaloisField p (3 * f) := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite (GaloisField p (3 * f))
    exact FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hGF])
  have hFrsurj : Function.Surjective (iterateFrobenius (GaloisField p (3 * f)) p f) :=
    Finite.surjective_of_injective (iterateFrobenius (GaloisField p (3 * f)) p f).injective
  have hmap := map_baseChangeGL_graphFixedRootGroup_eq TwistTag.D4 hp.out hf K hK σ hσ
    θ.toRingHom (Fr := iterateFrobenius (GaloisField p (3 * f)) p f) hsig hFrsurj
  let e₂ : graphFixedRootGroup TwistTag.D4 K σ ≃*
      graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * f))
        (iterateFrobenius (GaloisField p (3 * f)) p f) :=
    (Subgroup.equivMapOfInjective _ (baseChangeGL θ.toRingHom)
      (baseChangeGL_injective _)).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨(twistedGroupEquivFixed hK2 hq2 hK σ hσ).trans
    (e₂.trans (twistedGroupEquivFixed hGF2 hq2 hGF _ hsig).symm)⟩


theorem exists_conj_eq_of_involutions_td4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {x x' : twistedGroup σ} (hx : x * x = 1) (hx' : x' * x' = 1)
    (hx1 : x ≠ 1) (hx1' : x' ≠ 1) : ∃ g : twistedGroup σ, g * x * g⁻¹ = x' := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := exists_twistedGroup_mulEquiv_galois hp2 hf K hK σ hσ
  have hy : e x * e x = 1 := by rw [← map_mul, hx, map_one]
  have hy' : e x' * e x' = 1 := by rw [← map_mul, hx', map_one]
  have hy1 : e x ≠ 1 := fun h => hx1 (e.injective (by rw [h, map_one]))
  have hy1' : e x' ≠ 1 := fun h => hx1' (e.injective (by rw [h, map_one]))
  obtain ⟨g', hg'⟩ :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf hy hy' hy1 hy1'
  refine ⟨e.symm g', e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hg'

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
