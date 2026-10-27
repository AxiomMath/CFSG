module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwo
public import CFSG.CharacterTheory.Semidihedral.SemilinearLayerModel
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2 (fieldPerm)

namespace EvenCatalog

theorem map_centralizer_eq {G M : Type*} [Group G] [Group M] {ρ : G →* M}
    (hρ : Function.Injective ρ) (z : G) :
    (Subgroup.centralizer ({z} : Set G)).map ρ =
      ρ.range ⊓ Subgroup.centralizer ({ρ z} : Set M) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine Subgroup.mem_inf.mpr ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    obtain ⟨⟨x, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hy
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
    refine ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply hρ
    rw [map_mul, map_mul, hc']

@[expose] def centralizerMapEquiv {G M : Type*} [Group G] [Group M] {ρ : G →* M}
    (hρ : Function.Injective ρ) (z : G) :
    ↥(Subgroup.centralizer ({z} : Set G)) ≃*
      ↥(ρ.range ⊓ Subgroup.centralizer ({ρ z} : Set M)) :=
  ((Subgroup.centralizer ({z} : Set G)).equivMapOfInjective ρ hρ).trans
    (MulEquiv.subgroupCongr (map_centralizer_eq hρ z))

theorem coordinateE_eq_top_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) : coordinateE K = ⊤ := by
  classical
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, -, -, -, -, -, -, -, hquot, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_linear_two_involution_normal_forms
      (f := 2) (by norm_num) hK
  have hsqinj : Function.Injective (powMonoidHom 2 : Kˣ →* Kˣ) := by
    intro x y hxy
    have h1 : ((x : K) - y) ^ 2 = 0 := by
      have h2 : (x : K) ^ 2 = (y : K) ^ 2 := by
        have := congrArg (fun u : Kˣ => (u : K)) hxy
        simpa using this
      rw [sub_sq, h2]
      linear_combination ((y : K) ^ 2 - x * y) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1))
  have hunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    rfl
  have hsq : Nat.card (powMonoidHom 2 : Kˣ →* Kˣ).range = 3 := by
    rw [← hunits]
    exact Nat.card_congr (MonoidHom.ofInjective hsqinj).toEquiv.symm
  have hG : Nat.card (coordinateG K) = 60 := by
    rw [CFSG.LinearGroups.card_coordinateG, CFSG.LinearGroups.card_coordinateB, hK, hsq]
    norm_num
  have hGE : coordinateG K ≤ coordinateE K := (coordinateG_le_D K).trans (coordinateD_le_E K)
  have hE : Nat.card (coordinateE K) = 120 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((coordinateG K).subgroupOf (coordinateE K))
    rw [hquot, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGE).toEquiv, hG] at h1
    exact h1
  apply Subgroup.eq_top_of_card_eq
  rw [hE, Nat.card_perm, Finite.card_option, hK]
  rfl

end EvenCatalog

open EvenCatalog

theorem even_linear_two_almost_simple_unbalanced_outcome {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (CFSG.generalizedFitting G)]
    (hnonab : ∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a) {f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting G) .PSL 2 2 f) :
    2 ≤ f ∧
    (∀ z : G, orderOf z = 2 →
      (CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set G)) ≠ ⊥ ↔
        f = 2 ∧ z ∉ CFSG.generalizedFitting G)) ∧
    ∀ z : G, orderOf z = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set G)) ≠ ⊥ →
      CFSG.generalizedFitting G < ⊤ ∧
      Nonempty (CFSG.generalizedFitting G ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (G ≃* Equiv.Perm (Fin 5)) ∧
      Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃*
        Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) ∧
      IsCyclic ↥(CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set G))) ∧
      Nat.card ↥(CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set G))) = 3 ∧
      StatedClassicalModel (CFSG.generalizedFitting G) .PSL 2 5 1 ∧
      CFSG.Blueprint.OddLieType (CFSG.generalizedFitting G) ∧
      CFSG.ComponentClassification.OutcomeLocal.UOutcome G := by
  set F := CFSG.generalizedFitting G with hF
  have hf2 : 2 ≤ f := by
    obtain ⟨-, hf1, -, hne, -⟩ := hmodel.1
    by_contra hlt
    exact hne (by rw [show f = 1 by omega, pow_one])
  obtain ⟨K, hfield, hfinite, hcard, -, ρ, hρ, -, hmap, hcontains, -⟩ :=
    CFSG.Semidihedral.SemilinearLayerModel.generalizedFitting_semilinear_model hnonab hmodel
  set ρ' : G →* Equiv.Perm (Omega K) := (coordinateE K).subtype.comp ρ with hρ'
  have hρ'inj : Function.Injective ρ' := (coordinateE K).subtype_injective.comp hρ
  have hGH : coordinateG K ≤ ρ'.range := by
    intro g hg
    obtain ⟨x, hx⟩ := hcontains (Subgroup.mem_subgroupOf.mpr hg :
      (⟨g, (coordinateG_le_D K).trans (coordinateD_le_E K) hg⟩ : coordinateE K) ∈ _)
    exact ⟨x, by rw [hρ', MonoidHom.comp_apply, hx]; rfl⟩
  have hHE : ρ'.range ≤ coordinateE K := by
    rintro _ ⟨x, rfl⟩
    exact (ρ x).2
  have hzF : ∀ z : G, z ∈ F ↔ ρ' z ∈ coordinateG K := by
    intro z
    constructor
    · intro hz
      have h1 : ρ z ∈ F.map ρ := ⟨z, hz, rfl⟩
      rw [hmap, Subgroup.mem_subgroupOf] at h1
      exact h1
    · intro hz
      have h1 : ρ z ∈ (coordinateG K).subgroupOf (coordinateE K) := Subgroup.mem_subgroupOf.mpr hz
      rw [← hmap] at h1
      obtain ⟨x, hx, hxz⟩ := h1
      rwa [hρ hxz] at hx
  obtain ⟨hdich, hexc, -, -⟩ :=
    even_linear_two_full_centralizer_odd_core hf2 hcard
  have hord : ∀ z : G, orderOf (ρ' z) = orderOf z := fun z => orderOf_injective ρ' hρ'inj z
  have hiff : ∀ z : G, orderOf z = 2 →
      (CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set G)) ≠ ⊥ ↔ f = 2 ∧ z ∉ F) := by
    intro z hz
    have h1 := hdich ρ'.range hGH hHE (ρ' z) ⟨z, rfl⟩ (by rw [hord, hz])
    rw [← hzF] at h1
    rw [← h1]
    constructor
    · exact fun hne hbot => hne (oddCore_eq_bot_of_mulEquiv (centralizerMapEquiv hρ'inj z).symm
        hbot)
    · exact fun hne hbot => hne (oddCore_eq_bot_of_mulEquiv (centralizerMapEquiv hρ'inj z) hbot)
  refine ⟨hf2, hiff, fun z hz hne => ?_⟩
  obtain ⟨hf, hzF'⟩ := (hiff z hz).mp hne
  subst hf
  obtain ⟨hHtop, ⟨eC⟩, -, hcard3⟩ :=
    hexc ρ'.range hGH hHE (ρ' z) ⟨z, rfl⟩ (by rw [hord, hz]) rfl (by rwa [← hzF])
  have eCz := (centralizerMapEquiv hρ'inj z).trans eC
  have hcardz : Nat.card ↥(CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set G))) = 3 := by
    rw [card_oddCore_congr (centralizerMapEquiv hρ'inj z), hcard3]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA5 : Nonempty (F ≃* alternatingGroup (Fin 5)) :=
    CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model F
      (Or.inl ⟨by decide, hmodel⟩)
  obtain ⟨eA⟩ := hA5
  have hEtop := coordinateE_eq_top_of_card_four hcard
  have hΩ : Nat.card (Omega K) = 5 := by rw [Finite.card_option, hcard]; norm_num
  have eG : G ≃* Equiv.Perm (Fin 5) :=
    (MonoidHom.ofInjective hρ'inj).trans ((MulEquiv.subgroupCongr (hHtop.trans hEtop)).trans
      (Subgroup.topEquiv.trans (Equiv.permCongrHom (Finite.equivFinOfCardEq hΩ))))
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hZ5 : Nat.card (ZMod 5) = 5 := Nat.card_zmod 5
  obtain ⟨e5⟩ := (CFSG.LinearGroups.five_field_linear_two_alternating_five_model (ZMod 5)
    hZ5).1
  have hmodel5 : StatedClassicalModel F .PSL 2 5 1 :=
    ⟨⟨Nat.prime_five, le_rfl, le_rfl, by decide, by decide⟩, ZMod 5, inferInstance,
      inferInstance, by rw [hZ5, pow_one],
      ⟨eA.trans (e5.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5)))⟩⟩
  have hodd : CFSG.Blueprint.OddLieType F :=
    ⟨.PSL, 2, 5, 1, Nat.prime_five, by norm_num, hmodel5.1, Or.inl ⟨by decide, hmodel5⟩⟩
  have hU : CFSG.ComponentClassification.OutcomeLocal.UOutcome G := by
    refine Or.inl ?_
    rw [← CFSG.generalizedFitting_eq_componentClassification]
    exact hodd
  refine ⟨lt_top_iff_ne_top.mpr fun htop => hzF' (by rw [htop]; trivial), ⟨eA⟩, ⟨eG⟩, ⟨eCz⟩,
    isCyclic_of_prime_card hcardz, hcardz, hmodel5, hodd, hU⟩

end CFSG.ComponentClassification.UnbalancedCatalog
