module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieRoot
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Components

theorem trialityD4_not_hasKComponent
    {k : Type} [Field k] [Finite k] {m : ℕ} (hm : 1 ≤ m)
    (hk : Nat.card k = (2 ^ m) ^ 3) {r : ℕ} (hr : r = 1 ∨ r = 2) (σ₀ : k ≃+* k)
    (hσ₀ : ∀ c, σ₀ c = c ^ ((2 ^ m) ^ r)) (hσ₀3 : σ₀ ^ 3 = 1) :
    ¬ HasKComponent ↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) := by
  have hk' : Nat.card k = 2 ^ (3 * m) := by rw [hk, ← pow_mul, mul_comm]
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hk'
  have h4 : 4 ≤ Nat.card k := by
    rw [hk']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hperf := commutator_graphFixedRootGroup_triality_char_two (ringChar.eq k 2) σ₀
    (fun c => by
      have := congrArg (fun φ : k ≃+* k => φ c) hσ₀3
      simpa [pow_succ] using this) h4
  have hsimple := (isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 k σ₀ hperf).1
  obtain ⟨hcard, -, -⟩ := triality_both_orientations_exact_finite_order 2 m Nat.prime_two hm k hk r
    hr σ₀.toRingHom hσ₀
  have hodd : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 8 + (2 ^ m) ^ 4 + 1)) := by
    refine Odd.mul (Odd.mul ?_ ?_) ?_
    · exact CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hm (by norm_num)
    · exact CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hm (by norm_num)
    · have h8 : Even ((2 ^ m) ^ 8) :=
        Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
      have h4' : Even ((2 ^ m) ^ 4) :=
        Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
      exact (h8.add h4').add_one
  refine not_hasKComponent_of_isSimpleGroup (b := 4 * m) (by omega) hodd ?_
  rw [hcard]
  ring

end Components

theorem trialityEven_core
    {Γ : Type} [Group Γ] {f : ℕ} (hf1 : 1 ≤ f)
    (hmodel : ChevalleyExceptionalModel Γ .trialityD4 2 f) (a : MulAut Γ) (ha : a * a = 1)
    (h0 : HasKComponent ↥(fixSubgroup a)) : False := by
  obtain ⟨F, _, _, _, σ, hσ3, hσ, hFcard, -, ⟨e⟩⟩ :=
    TrialityCover.triality_model hf1 hmodel.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 F σ
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom),
      α = MulAut.congr e a := ⟨_, rfl⟩
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, ha, map_one]
  have h1 : HasKComponent ↥(fixSubgroup α) := by
    rw [hαdef]
    exact hasKComponent_fixSubgroup_of_intertwine e a _
      (mulAut_congr_apply_self e a) h0
  by_cases hα1 : α = 1
  ·
    rw [hα1] at h1
    exact trialityD4_not_hasKComponent hf1 hFcard (Or.inl rfl) σ
      (fun c => by rw [pow_one]; exact hσ c) hσ3 (hasKComponent_of_fixSubgroup_one h1)
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rwa [pow_two]) hα1
  by_cases hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom)
  ·
    exact not_hasKComponent_fix_of_inner hZ
      (fun y hy B => rootWeightDatum_involution_centralizer_component_free
        (RootWeightDatum.fixed TwistTag.D4 σ hσ3) y hy B) hαα hα1 hin h1
  ·
    have hα2' : α ^ 2 = 1 := by rw [pow_two]; exact hαα
    obtain ⟨hev, δ, hδ, -, ψ, hψ, -⟩ :=
      even_triality_outer_involutions_canonical_field hf1 F hFcard σ hσ α hα2' hin
    obtain ⟨m, hm⟩ := hev
    have hm1 : 1 ≤ m := by omega
    have hfm : f = 2 * m := by omega
    have hFcard' : Nat.card F = 2 ^ (6 * m) := by
      rw [hFcard, hfm]
      ring
    have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * m) := fun c => by rw [hσ c, hfm]
    have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * m) := fun c => by
      rw [hδ c, show 3 * f / 2 = 3 * m by omega]
    obtain ⟨-, hk0, hres, hord3, -, hFix, -⟩ :=
      even_triality_canonical_field_full_centralizer hm1 F hFcard' σ hσ' δ hδ'
    have hint : ∀ y, fieldActor σ δ (ψ y) = ψ (α y) := fun y => by
      rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    have h2 : HasKComponent ↥(fixSubgroup (fieldActor σ δ)) :=
      hasKComponent_fixSubgroup_of_intertwine ψ α _ hint h1
    have e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
    have e₂ : ↥(fixSubgroup (fieldActor σ δ)) ≃* ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) :=
      (((fixSubgroup (fieldActor σ δ)).equivMapOfInjective
        (graphFixedRootGroup TwistTag.D4 F σ.toRingHom).subtype
        (graphFixedRootGroup TwistTag.D4 F σ.toRingHom).subtype_injective).trans
        (MulEquiv.subgroupCongr hFix)).trans e₁.symm
    have : Finite (fixSubfield δ) := Subtype.finite
    refine trialityD4_not_hasKComponent hm1 (by rw [hk0, pow_mul']) (Or.inr rfl)
      (fixSubfieldRestrict σ δ) (fun c => Subtype.ext ?_) ?_ (h2.of_mulEquiv e₂)
    · have hsq : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by ring
      rw [hres c, hσ' (c : F), SubmonoidClass.coe_pow, hsq]
    · have := pow_orderOf_eq_one (fixSubfieldRestrict σ δ)
      rwa [hord3] at this

theorem tabIdentFor_trialityEven
    : TabIdentFor @Ident.FamTrialityEven := by
  intro G _ _ X K t hs hX
  obtain ⟨-, f, hf1, hmodel⟩ := hX
  exact (trialityEven_core hf1 hmodel (hs.conjAut : MulAut ↥X) hs.conjAut_mul_self
    hs.hasKComponent_fix).elim

end CFSG.QuasithinUnique.Id2519
