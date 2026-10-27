module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.ReeTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.Basic
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.RankThree.PartOne.RF4.Descent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Open
  CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 TauCeti
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section Ree


theorem reeF4_stdDescent_odd {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) :
    ∀ α : MulAut (F4.reeGamma K a), IsOuterOfOrder p α →
      ∃ g : F4.reeGamma K a, ∃ β : K ≃+* K, orderOf β = p ∧
        α = MulAut.conj g * F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, hcyc, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form a (by omega) K hK
  intro α hα
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
  let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΨα : Ψ ⟨x, β⟩ = α := by rw [hΨ x β]; exact hxβ.symm
  have hΘα : Θ α = β := by
    show SemidirectProduct.rightHom (Ψ.symm α) = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by rw [← hΘα, ← map_pow, hαp, map_one]
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hout x
    rw [h, hone, mul_one] at hxβ
    exact hxβ
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α hαp ⟨x, hxβ⟩
  exact ⟨g, β, hβord, hg⟩

theorem conj_injective_cat_reeF4 {b : ℕ} (hv : (LieTypeIndex.reeF4 b).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨.reeF4 b, hv⟩ →* MulAut (Cat ⟨.reeF4 b, hv⟩)) := by
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  exact conj_injective_of_mulEquiv e (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
    (large_Ree_fixed_group_center_trivial b X hX))

theorem not_sq_dvd_ree_two {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ¬ p ^ 2 ∣ 35942400 := by
  intro h
  have hd : p ∣ 35942400 := (dvd_pow_self p two_ne_zero).trans h
  have h' : p ∣ 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := by
    norm_num
    exact hd
  rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
  · have hp13 : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1
    subst hp13
    revert h
    norm_num

theorem not_sq_dvd_card_reeGamma_zero {k : Type} [Field k] [Finite k] [CharP k F4.prime]
    (hk : Nat.card k = 2) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card (F4.reeGamma k 0) := by
  intro h
  have hord := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    (a := 0) (K := k) (by simpa using hk)).1
  rw [hord] at h
  exact not_sq_dvd_ree_two hp hp7 (by norm_num at h ⊢; exact h)

theorem fixPlaneGen_reeF4_odd (hLow : ExcInnerLowPlanes) {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hexc : ¬ (p = 5 ∧ a = 2))
    (hrank : RankLE2 p (F4.reeGamma K a)) : FixPlaneGen (F4.reeGamma K a) p := by
  have : Fact p.Prime := ⟨hp⟩
  refine fixPlaneGen_of_standard_cat (MulAut.conj : F4.reeGamma K a →* MulAut _).range
    {g | ∃ β : K ≃+* K, orderOf β = p ∧ g = F4.reeGammaFieldAut K a β} ?_ ?_
  · intro α hα
    obtain ⟨g, β, hβ, h⟩ := reeF4_stdDescent_odd ha hK hp α hα
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, F4.reeGammaFieldAut K a β, ⟨β, hβ, rfl⟩, h⟩
  · rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ :=
      CFSG.RankThree.PartOne.Sec66T.reeF4_fixed_data_odd hK hp (by omega) hβ
    have hfix : CFSG.RankThree.PartOne.Sec66T.fixSub (F4.reeGammaFieldAut K a β) =
        fixedSubgroup (F4.reeGammaFieldAut K a β) := Subgroup.ext fun _ => Iff.rfl
    let e₁ : ↥(fixedSubgroup (F4.reeGammaFieldAut K a β)) ≃* F4.reeGamma (fixSubfield β) b :=
      (MulEquiv.subgroupCongr hfix.symm).trans eC
    by_cases hb : b = 0
    · subst hb
      refine ⟨_, inferInstance, MulEquiv.refl _, fun B hBa hBc => ?_⟩
      exfalso
      have hp7 : 7 ≤ p := by omega
      apply not_sq_dvd_card_reeGamma_zero (k := fixSubfield β) (by simpa using hbcard) hp hp7
      rw [← Nat.card_congr e₁.toEquiv, ← hBc]
      exact Subgroup.card_subgroup_dvd_card B
    · have hv : (LieTypeIndex.reeF4 b).Valid := by
        refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
        · simpa [LieTypeIndex.inStandardRange_iff] using Nat.one_le_iff_ne_zero.2 hb
        · simp [LieTypeIndex.isDuplicateRepresentative_iff]
      obtain ⟨eCat⟩ := reeGamma_equiv_cat_of_card (Nat.one_le_iff_ne_zero.2 hb) hv hbcard
      refine ⟨Cat ⟨.reeF4 b, hv⟩, inferInstance, e₁.trans eCat.symm, ?_⟩
      intro B hBa hBc
      exact closure_centralizers_of_excInnerLow hLow
        (d := ⟨.reeF4 b, hv⟩) (IsReeTypeIndex.not_classical (Or.inr (Or.inr (Or.inl ⟨b, rfl⟩)))) hp
        (by omega) (by show p ≠ (LieTypeIndex.reeF4 b).characteristic; rw [LieTypeIndex.characteristic_reeF4]; omega)
        not_isD2SeitzException_reeF4 (conj_injective_cat_reeF4 hv)
        (rankLE2_of_equiv_fixed (e₁.trans eCat.symm) hrank) B hBa hBc

end Ree

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
