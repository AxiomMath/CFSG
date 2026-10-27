module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4Native
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Rest CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47 (twisted_of_lieModel_D4)

open scoped MatrixGroups

section D4Models

variable {p f : ℕ} [Fact p.Prime]

abbrev sig0 (p f : ℕ) [Fact p.Prime] : GaloisField p (3 * f) →+* GaloisField p (3 * f) :=
  iterateFrobenius (GaloisField p (3 * f)) p f

theorem sig0_apply (c : GaloisField p (3 * f)) : sig0 p f c = c ^ (p ^ f) :=
  iterateFrobenius_def p f c

theorem card_gf3 (hf : 1 ≤ f) : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
  rw [GaloisField.card p (3 * f) (by omega), pow_mul']

theorem d4Data_sig0 (hp2 : p ≠ 2) (hf : 1 ≤ f) : D4Data (GaloisField p (3 * f)) (sig0 p f) (p ^ f) :=
  ⟨((Fact.out : p.Prime).odd_of_ne_two hp2).pow, card_gf3 hf, fun c => sig0_apply c⟩

omit [Fact p.Prime] in
theorem one_le_of_lieModel_D4 {M : Type} [Group M] (hM : LieModel M .trialityD4 0 p f) : 1 ≤ f := by
  obtain ⟨K₁, _, _, hK₁, -⟩ := twisted_of_lieModel_D4 hM
  by_contra h
  have hf0 : f = 0 := by omega
  subst hf0
  have h1 : Nat.card K₁ = 1 := by simpa [TwistTag.order] using hK₁
  have := Finite.one_lt_card (α := K₁)
  omega

theorem exists_equiv_concrete {M : Type} [Group M] (hp2 : p ≠ 2)
    (hM : LieModel M .trialityD4 0 p f) : Nonempty (M ≃* twistedGroup (sig0 p f)) := by
  have hp : p.Prime := Fact.out
  have hmodel := twisted_of_lieModel_D4 hM
  have hf : 1 ≤ f := one_le_of_lieModel_D4 hM
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hmodel
  have hcardK : Nat.card K = Nat.card (GaloisField p (3 * f)) := by
    rw [hcard, card_gf3 hf]
    rfl
  let θ : K ≃+* GaloisField p (3 * f) := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite (GaloisField p (3 * f))
    exact FiniteField.ringEquivOfCardEq (by rwa [← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card])
  have hFrsurj : Function.Surjective (sig0 p f) :=
    Finite.surjective_of_injective (sig0 p f).injective
  have hmap := map_baseChangeGL_graphFixedRootGroup_eq TwistTag.D4 hp hf K hcard σ.toRingHom hσ
    θ.toRingHom (Fr := sig0 p f) (fun c => sig0_apply c) hFrsurj
  let e₂ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * f)) (sig0 p f)) :=
    (Subgroup.equivMapOfInjective _ (baseChangeGL θ.toRingHom)
      (baseChangeGL_injective _)).trans (MulEquiv.subgroupCongr hmap)
  have hrange := (d4Data_sig0 hp2 hf).range
  let e₃ : ↥(graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * f)) (sig0 p f)) ≃*
      twistedGroup (sig0 p f) :=
    (MulEquiv.subgroupCongr hrange.symm).trans
      (MonoidHom.ofInjective (twistedIncl_injective (sig0 p f))).symm
  exact ⟨e.trans (e₂.trans e₃)⟩

theorem ivk_4_7a_D4_aux {M : Type} [Group M] (hp2 : p ≠ 2) (hM : LieModel M .trialityD4 0 p f)
    (z z' : M) (hz : orderOf z = 2) (hz' : orderOf z' = 2) : IsConj z z' := by
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hM
  have hf := one_le_of_lieModel_D4 hM
  have hsq : ∀ w : M, orderOf w = 2 → φ w * φ w = 1 ∧ φ w ≠ 1 := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [← pow_two, ← map_pow, ← hw, pow_orderOf_eq_one, map_one]
    · intro h
      have : w = 1 := φ.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hw
      exact absurd hw (by norm_num)
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf
    (hsq z hz).1 (hsq z' hz').1 (hsq z hz).2 (hsq z' hz').2
  exact isConj_of_equiv φ (isConj_iff.2 ⟨g, hg⟩)

theorem tauL_mul_self {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) :
    τL hσ * τL hσ = 1 := by
  rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]

theorem tauL_ne_one {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : (-1 : Kˣ) ≠ 1) : τL hσ ≠ 1 := fun h => zd_ne_one hσ hK (Subtype.ext h)

theorem orderOf_tauL {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : (-1 : Kˣ) ≠ 1) : orderOf (τL hσ) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact tauL_mul_self hσ) (tauL_ne_one hσ hK)

theorem ivk_4_7ab_D4_aux {M : Type} [Group M] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hM : LieModel M .trialityD4 0 p f) (z : M) (hz : orderOf z = 2) :
    ∃ (K₁ K₂ : Subgroup M) (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁)
      (_ : Finite F₂) (t : M),
      Nat.card F₁ = (p ^ f) ^ 3 ∧ Nat.card F₂ = p ^ f ∧ (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧
        z ∈ K₁ ∧ z ∈ K₂ ∧ K₁ ⊓ K₂ = Subgroup.zpowers z ∧ Ch6Rem z K₁ K₂ F₁ F₂ t := by
  have hf := one_le_of_lieModel_D4 hM
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hM
  have hD : D4Data (GaloisField p (3 * f)) (sig0 p f) (p ^ f) := d4Data_sig0 hp2 hf
  have hσ := hD.sigma3
  have hcardF : Nat.card (fixedField (sig0 p f)) = p ^ f :=
    card_fixedField_eq (Fact.out : p.Prime) hf hD.card hD.frob
  have hsq : φ z * φ z = 1 ∧ φ z ≠ 1 := by
    refine ⟨?_, ?_⟩
    · rw [← pow_two, ← map_pow, ← hz, pow_orderOf_eq_one, map_one]
    · intro h
      have : z = 1 := φ.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf
    hsq.1 (tauL_mul_self hσ) hsq.2 (tauL_ne_one hσ hD.neg_one)
  let ψ : M ≃* twistedGroup (sig0 p f) := φ.trans (MulAut.conj g)
  have hψz : ψ z = τL hσ := hg
  have hzz : ψ.symm (τL hσ) = z := by rw [← hψz, MulEquiv.symm_apply_apply]
  obtain ⟨S, hS⟩ := exists_native_shape_d4 hσ hD
  have h4₁ : 4 ≤ Nat.card (GaloisField p (3 * f)) := by
    rw [hD.card]
    calc 4 ≤ p ^ f := by omega
      _ ≤ (p ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h4₂ : 4 ≤ Nat.card (fixedField (sig0 p f)) := by rw [hcardF]; omega
  obtain ⟨K₁, K₂, t, hcomm, hz₁, hz₂, hinter, hRem⟩ :=
    Shape.exists_ch6Rem (z := τL hσ) S (by rw [hS]; rfl) h4₁ h4₂
  have key := ch6Data_map ψ.symm ⟨hcomm, hz₁, hz₂, hinter, hRem⟩
  rw [hzz] at key
  exact ⟨K₁.map ψ.symm.toMonoidHom, K₂.map ψ.symm.toMonoidHom, GaloisField p (3 * f),
    fixedField (sig0 p f), inferInstance, inferInstance, inferInstance, inferInstance, ψ.symm t,
    hD.card, hcardF, key⟩

end D4Models

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.Blueprint

theorem ivk_4_7a_D4
    (K : Type) [Group K] [Finite K] (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : LieModel K .trialityD4 0 p n) (z z' : K) (hz : orderOf z = 2) (hz' : orderOf z' = 2) :
    IsConj z z' := by
  have : Fact p.Prime := ⟨hp⟩
  exact ivk_4_7a_D4_aux hp2 hK z z' hz hz'

theorem ivk_4_7ab_D4
    : IVK_4_7ab_D4 := by
  intro M _ _ p f hp hp2 h5 hM z hz
  have : Fact p.Prime := ⟨hp⟩
  exact ivk_4_7ab_D4_aux hp2 h5 hM z hz

theorem ivk_4_7ab
    : IVK_4_7ab :=
  ⟨ivk_4_7ab_G2, ivk_4_7ab_D4⟩

end CFSG.GH74.GLS.IVK.Proofs2
