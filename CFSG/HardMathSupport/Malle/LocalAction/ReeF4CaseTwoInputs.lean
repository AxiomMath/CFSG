module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSieve
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4NormalizerOrder
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4OuterSigma
import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.AGLEmbedding CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

section Normalizer

theorem reeF4SylowNormalizerCard_of_certs :
    Coordinator.ReeF4SylowNormalizerCard := by
  intro K _ _ d hd e P
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := exists_reeGamma_model hd e
  have : Finite (F4.reeGamma F 2) := Subtype.finite
  let P' : Sylow 5 (F4.reeGamma F 2) := P.mapSurjective (f := eΓ.toMonoidHom) eΓ.surjective
  have h1 := card_normalizer_sylow_reeGamma hF P'
  have h2 : Subgroup.normalizer ((P' : Subgroup (F4.reeGamma F 2)) : Set (F4.reeGamma F 2)) =
      (Subgroup.normalizer ((P : Subgroup K) : Set K)).map eΓ.toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq]
    rfl
  rw [h2, Subgroup.card_map_of_injective eΓ.injective] at h1
  exact h1

end Normalizer

section OuterSigma

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem exists_outer_sigma_fixed_order
    {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsReeFFourFiveIndex d) (e : Nonempty (K ≃* CatGroup d))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hrank : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y)) :
    ∃ σ : Y, σ ∉ K ∧ orderOf σ = 5 ∧
      (∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
        Nat.card F ≤ 25) ∧
      ∀ F : Subgroup Y, F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
        Nat.card F ∣ 35942400 := by
  classical
  have hidx := (exists_outer_sigma K d hd e hC hrank).1
  have hKtop : K ≠ ⊤ := by
    intro hKt
    rw [hKt, Subgroup.index_top] at hidx
    omega
  obtain ⟨e⟩ := e
  have hmodel := reeTitsModel_of_catGroup_reeF4 hd
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier (CatGroup d) 2 (2 * 2 + 1) hmodel
  obtain ⟨-, a, hfa, F, _, _, hF, ⟨e'⟩⟩ := hmodel
  have hFc : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have : CharP F F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  obtain ⟨eΓ⟩ := hS.2.2.2.2.2 a F hfa hF ⟨e'⟩
  have ha : a = 2 := by omega
  subst ha
  let eK : K ≃* F4.reeGamma F 2 := e.trans eΓ
  have : Finite (F4.reeGamma F 2) := Subtype.finite
  obtain ⟨σ₀, -, hσ₀, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
      2 5 Nat.prime_two (by norm_num) F (by simpa using hFc)
  have hk := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by norm_num : 1 ≤ 5) (by simpa using hFc) σ₀).2
  rw [hσ₀] at hk
  have hk1 : Nat.card (fixSubfield σ₀) = 2 ^ 1 := by simpa using hk
  obtain ⟨-, hnf⟩ := CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form
    (a := 2) (K := F) (by norm_num) hFc
  have hinj : Function.Injective (F4.reeGammaFieldAutHom F 2) := by
    rw [injective_iff_map_eq_one]
    intro β hβ
    refine hnf β ⟨1, ?_⟩
    rw [← F4.reeGammaFieldAutHom_apply, hβ, map_one]
  set τ : MulAut (F4.reeGamma F 2) := F4.reeGammaFieldAut F 2 σ₀ with hτdef
  have hτ : orderOf τ = 5 := by
    rw [hτdef, ← F4.reeGammaFieldAutHom_apply]
    exact (orderOf_injective _ hinj σ₀).trans hσ₀
  have hni : τ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma F 2) := by
    intro h
    have h1 := hnf σ₀ h
    rw [h1, orderOf_one] at hσ₀
    omega
  have hOut : Nat.card (Outer (F4.reeGamma F 2)) ∣ 5 :=
    (CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hFc).2
  obtain ⟨-, σ, hσK, hσ5, hact⟩ :=
    exists_sigma_of_outer K eK hC hKtop hOut τ hτ hni
  have hfixK : ∀ k : K, (k : Y) ∈ Subgroup.centralizer ({σ} : Set Y) → τ (eK k) = eK k := by
    intro k hk
    have h1 : σ * k * σ⁻¹ = k := by
      have := (Subgroup.mem_centralizer_iff.1 hk) σ rfl
      rw [this]; group
    have h2 := hact k k.2 (by rw [h1]; exact k.2)
    rw [← h2]
    congr 1
    exact Subtype.ext h1
  refine ⟨σ, hσK, hσ5, ?_, ?_⟩
  · intro F₀ hF₀ hF₀K hF₀C
    obtain ⟨F', ⟨φ⟩, hF'⟩ := exists_subgroup_map_of_le K eK F₀ hF₀K
    have hp' : IsPGroup 5 F' := hF₀.of_equiv φ.symm
    have hcard : Nat.card F' = Nat.card F₀ := Nat.card_congr φ.toEquiv
    rw [← hcard]
    refine card_le_twentyfive_of_fixed_reeGamma σ₀ hk1 F' ?_ hp'
    intro γ hγ
    obtain ⟨k, hk, rfl⟩ := hF' γ hγ
    exact hfixK k (hF₀C hk)
  · intro F₀ hF₀K hF₀C
    obtain ⟨F', ⟨φ⟩, hF'⟩ := exists_subgroup_map_of_le K eK F₀ hF₀K
    have hcard : Nat.card F' = Nat.card F₀ := Nat.card_congr φ.toEquiv
    rw [← hcard]
    refine card_dvd_of_fixed_reeGamma σ₀ hk1 F' ?_
    intro γ hγ
    obtain ⟨k, hk, rfl⟩ := hF' γ hγ
    exact hfixK k (hF₀C hk)

theorem reeF4OuterSigmaFixedOrder_of_certs :
    Coordinator.ReeF4OuterSigmaFixedOrder := by
  intro Y _ _ K d hd hKn hiso hC hrank
  have := hKn
  exact exists_outer_sigma_fixed_order K d hd hiso hC hrank

end OuterSigma

section Cyclic

theorem centralizer_exponent_of_sylow_cyclic {Γ : Type*} [Group Γ] [Finite Γ] {p m : ℕ}
    [Fact p.Prime] (hp : ¬ p ^ 2 ∣ Nat.card Γ) (x₀ : Γ) (hx₀ : orderOf x₀ = p)
    (h : ∀ g ∈ Subgroup.centralizer ({x₀} : Set Γ), g ^ m = 1) :
    ∀ x : Γ, orderOf x = p →
      ∀ g ∈ Subgroup.centralizer ({x} : Set Γ), g ^ m = 1 := by
  intro x hx g hg
  have hpd : p ∣ Nat.card Γ := hx ▸ orderOf_dvd_natCard x
  have hfac : (Nat.card Γ).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card Γ).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization Fact.out Nat.card_pos.ne').1 hpd
    by_contra hne
    exact hp ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').2
      (by omega))
  have hcz : ∀ y : Γ, orderOf y = p →
      Nat.card (Subgroup.zpowers y) = p ^ (Nat.card Γ).factorization p := fun y hy => by
    rw [Nat.card_zpowers, hy, hfac, pow_one]
  let S₀ : Sylow p Γ := Sylow.ofCard (Subgroup.zpowers x₀) (hcz x₀ hx₀)
  let S₁ : Sylow p Γ := Sylow.ofCard (Subgroup.zpowers x) (hcz x hx)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Γ S₀ S₁
  have hmem : c * x₀ * c⁻¹ ∈ Subgroup.zpowers x := by
    have h1 : c * x₀ * c⁻¹ ∈ ((c • S₀ : Sylow p Γ) : Subgroup Γ) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨x₀, Subgroup.mem_zpowers x₀, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hc] at h1
    exact h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hcomm : c * x₀ * c⁻¹ * g = g * (c * x₀ * c⁻¹) := by
    rw [← hk]
    have hxg : Commute x g := Subgroup.mem_centralizer_iff.1 hg x rfl
    exact (hxg.zpow_left k).eq
  have hg' : c⁻¹ * g * c ∈ Subgroup.centralizer ({x₀} : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    calc x₀ * (c⁻¹ * g * c) = c⁻¹ * ((c * x₀ * c⁻¹) * g) * c := by group
      _ = c⁻¹ * (g * (c * x₀ * c⁻¹)) * c := by rw [hcomm]
      _ = c⁻¹ * g * c * x₀ := by group
  have h2 := h _ hg'
  have h3 : g ^ m = c * (c⁻¹ * g * c) ^ m * c⁻¹ := by
    have : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
    conv_lhs => rw [this]
    exact conj_pow
  rw [h3, h2]
  group


theorem card_reeGamma_thirtyTwo
    {F : Type} [Field F] [Finite F] [CharP F F4.prime]
    (hF : Nat.card F = 2 ^ (2 * 2 + 1)) :
    Nat.card (F4.reeGamma F 2) = Coordinator.reeF4Order := by
  rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    2 F hF).1]
  norm_num [Coordinator.reeF4Order]

@[expose] def RegularElementData (p m : ℕ) : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K F4.prime], Nat.card K = 2 ^ (2 * 2 + 1) →
    ∃ x : F4.reeGamma K 2, orderOf x = p ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set (F4.reeGamma K 2)), g ^ m = 1

theorem centralizer_exponent_reeF4
    {p m : ℕ} [Fact p.Prime] (hp : ¬ p ^ 2 ∣ Coordinator.reeF4Order)
    (hdata : RegularElementData p m)
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeFFourFiveIndex d) (e : Nonempty (K ≃* CatGroup d)) (w : K) (hw : orderOf w = p) :
    ∀ g ∈ Subgroup.centralizer ({w} : Set K), g ^ m = 1 := by
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := exists_reeGamma_model hd e
  have : Finite (F4.reeGamma F 2) := Subtype.finite
  obtain ⟨x₀, hx₀, hcent⟩ := hdata hF
  have hx := centralizer_exponent_of_sylow_cyclic (m := m)
    (card_reeGamma_thirtyTwo hF ▸ hp) x₀ hx₀ hcent (eΓ w)
    ((MulEquiv.orderOf_eq eΓ w).trans hw)
  intro g hg
  have hg' : eΓ g ∈ Subgroup.centralizer ({eΓ w} : Set (F4.reeGamma F 2)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_iff.1 hg w rfl]
  have := hx _ hg'
  rw [← map_pow] at this
  exact eΓ.injective (by rw [this, map_one])

theorem reeF4CyclicToralCentralizers_of_regular
    (h13 : RegularElementData 13 793) (h61 : RegularElementData 61 793)
    (h331 : RegularElementData 331 993) (h1321 : RegularElementData 1321 1321) :
    Coordinator.ReeF4CyclicToralCentralizers := by
  intro K _ _ d hd e w
  have f13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have f61 : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  have f331 : Fact (Nat.Prime 331) := ⟨by norm_num⟩
  have f1321 : Fact (Nat.Prime 1321) := ⟨by norm_num⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro (hw | hw)
    · exact centralizer_exponent_reeF4 (p := 13) (by norm_num [Coordinator.reeF4Order]) h13 hd e w hw
    · exact centralizer_exponent_reeF4 (p := 61) (by norm_num [Coordinator.reeF4Order]) h61 hd e w hw
  · exact centralizer_exponent_reeF4 (p := 331) (by norm_num [Coordinator.reeF4Order]) h331 hd e w
  · exact centralizer_exponent_reeF4 (p := 1321) (by norm_num [Coordinator.reeF4Order]) h1321 hd e w

theorem reeF4CyclicToralCentralizers_of_regular_certs
    (h13 : RegularElementData 13 793)
    (h61 : RegularElementData 61 793)
    (h331 : RegularElementData 331 993)
    (h1321 : RegularElementData 1321 1321) :
    Coordinator.ReeF4CyclicToralCentralizers := by
  exact reeF4CyclicToralCentralizers_of_regular h13 h61 h331 h1321

end Cyclic

end CFSG.HardMathSupport.Malle.LocalAction
