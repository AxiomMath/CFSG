module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6XiTransfer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerS

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)
open CFSG.Quasithin (perfectCore)


section Span

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem twoTwistedSpan_facts {e : L ≃* adjointGroup .F4 K} {t : G} (hw : F4Work L K t 1)
    (X₀ : Subgroup (adjointGroup .F4 K)) {k : Type} [Field k] [Finite k] (σ' : k ≃+* k)
    (hk : Nat.card k = 4) (hσ' : ∀ c, σ' c = c ^ 2) {M : Subgroup G}
    (hM : M = centralizerPerfectCore (subgroupToG e X₀) ⊔ L)
    (e₆ : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 k σ'.toRingHom) :
    ⁅M, M⁆ = M ∧ L ≤ M ∧ ∃ htN : t ∈ normalizer (M : Set G),
      Odd (Nat.card (centralizer (M : Set G))) ∧ Odd (Nat.card (center M)) ∧
      M ⊓ centralizer ({t} : Set G) = L ∧
      ∃ η : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom),
        (∀ h : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom, (η h : ModGL TwistTag.E6.tag k) =
          diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) ∧
        ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom),
          φ * normalizerQuotMulAut e₆ ⟨t, htN⟩ * φ⁻¹ = η := by
  subst hM
  have hk' : Nat.card k = (2 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hσ1 : ∀ c, σ'.toRingHom c = c ^ 2 ^ 1 := fun c => by
    rw [pow_one]
    exact hσ' c
  have hMp := commutator_twoE6Span e X₀
  have hLM := le_twoE6Span e X₀
  have htN := mem_normalizer_twoE6Span e X₀ hw.mem_centralizer
  have h36 : 2 ^ (36 * 1) ∣ Nat.card (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two le_rfl hk'
      σ'.toRingHom hσ1]
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordTwistedE6' (le_refl 1)).two
    rw [hr, mul_comm 36 1]
    exact Dvd.intro r rfl
  have htCM : t ∉ centralizer (twoE6Span e X₀ : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e hw.mem_centralizer
      hw.orderOf_eq hMp e₆ h36
  have hC := EPilot.odd_card_centralizer_of_inf_eq_zpowers hw.inf_eq hLM hw.orderOf_eq htN htCM
  have hZ := odd_card_center_of_odd_card_centralizer hC
  refine ⟨hMp, hLM, htN, hC, hZ, ?_⟩
  rcases inf_centralizer_eq_or_xi_twistedE6_quot_27 hw.standard hw.card_eq e hw.mem_centralizer
      hw.orderOf_eq hw.inf_eq hMp hZ hk' σ'.toRingHom hσ1 e₆ htN with h | ⟨hx, φ, η, hη, hφ⟩
  · exact h
  · exact (false_of_le_of_conj_xi_twistedE6 hLM hw.center_eq_bot hw.card_eq e hk' hσ1 e₆
      hw.mem_centralizer htN hη hx hφ).elim

end Span

section Step3

@[expose] def TwoTwistedE6CoreNotDvdInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ¬ Nat.card (centralizerPerfectCore (subgroupToG e X₀)) ∣
        Nat.card (center (centralizerPerfectCore (subgroupToG e X₀))) *
          Nat.card (centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))

@[expose] def TwoTwistedE6SpanConjugateInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ∀ (k : Type) [Field k] [Finite k] (σ' : k ≃+* k), Nat.card k = 4 → (∀ c, σ' c = c ^ 2) →
      ∀ M : Subgroup G, M = centralizerPerfectCore (subgroupToG e X₀) ⊔ L →
      ∀ (_e₆ : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 k σ'.toRingHom) (g : G),
        t ∈ normalizer (CFSG.conjugate M g : Set G) →
        CFSG.conjugate M g ⊓ centralizer ({t} : Set G) = L → CFSG.conjugate M g = M

theorem twoTwistedE6SpanConjugateInput_of_notDvd (h : TwoTwistedE6CoreNotDvdInput) :
    TwoTwistedE6SpanConjugateInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' k _ _ σ' hk hσ' M hM e₆ g htM' hML
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hk' : Nat.card k = (2 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hσ1 : ∀ c, σ'.toRingHom c = c ^ 2 ^ 1 := fun c => by
    rw [pow_one]
    exact hσ' c
  obtain ⟨hMp, -, htN, -, hZ, hC₀, η, hη, φ₀, hφ₀⟩ := twoTwistedSpan_facts hw X₀ σ' hk hσ' hM e₆
  obtain ⟨h₁, rfl⟩ : ∃ h₁ : G, g = h₁⁻¹ := ⟨g⁻¹, (inv_inv g).symm⟩
  have hLM' : L ≤ CFSG.conjugate M h₁⁻¹ := fun x hx => by
    rw [← hML] at hx
    exact hx.1
  have hMp' := E6Pilot.commutator_conjugate_eq hMp h₁⁻¹
  have hZM : Odd (Nat.card (center (CFSG.conjugate M h₁⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  set eM := (E6Pilot.coverConjugateQuotientCenterEquiv M h₁⁻¹).symm.trans e₆ with heM
  have hφM : ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom),
      φ * normalizerQuotMulAut eM ⟨t, htM'⟩ * φ⁻¹ = η := by
    rcases inf_centralizer_eq_or_xi_twistedE6_quot_27 hw.standard hw.card_eq e hw.mem_centralizer
        hw.orderOf_eq hw.inf_eq hMp' hZM hk' σ'.toRingHom hσ1 eM htM' with
      ⟨-, η', hη', φ, hφ⟩ | ⟨hx, φ, η', hη', hφ⟩
    · have hηη : η' = η := MulEquiv.ext fun x => Subtype.ext ((hη' x).trans (hη x).symm)
      refine ⟨φ, ?_⟩
      rw [← hηη]
      exact hφ
    · exact (false_of_le_of_conj_xi_twistedE6 hLM' hw.center_eq_bot hw.card_eq e hk' hσ1 eM
        hw.mem_centralizer htM' hη' hx hφ).elim
  rcases mem_normalizer_or_dvd_of_eta_conjugate_two hK e X₀ hM hw.orderOf_eq hZ e₆ η htN
      ⟨hC₀, φ₀, hφ₀⟩ h₁ htM' ⟨hML, hφM⟩ with hN | hdvd
  · rw [conjugate_inv_eq_map]
    exact mem_normalizer_iff_map_conj_eq.1 hN
  · exact (h G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' hdvd).elim

end Step3

end CFSG.SeitzReduction.F4Pilot
