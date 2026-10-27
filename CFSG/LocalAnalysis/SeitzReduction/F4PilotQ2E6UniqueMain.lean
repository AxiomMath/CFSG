module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6UniqueSteps
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)
open CFSG.Quasithin (perfectCore)

section General

variable {G : Type} [Group G] [Finite G]

theorem commutator_twoE6Span {L : Subgroup G} {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) (X₀ : Subgroup (adjointGroup .F4 K)) :
    ⁅twoE6Span e X₀, twoE6Span e X₀⁆ = twoE6Span e X₀ := by
  have hL : ⁅L, L⁆ = L := by
    have : Group.IsPerfect (adjointGroup .F4 K) := CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 K
    have hr : (L.subtype.comp e.symm.toMonoidHom).range = L := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (e.symm y).2
      · intro hx
        exact ⟨e ⟨x, hx⟩, by simp⟩
    rw [← hr]
    exact commutator_monoidHom_range_eq_of_isPerfect _
  have hE := commutator_centralizerPerfectCore (subgroupToG e X₀)
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · refine sup_le ?_ ?_
    · calc centralizerPerfectCore (subgroupToG e X₀) =
            ⁅centralizerPerfectCore (subgroupToG e X₀),
              centralizerPerfectCore (subgroupToG e X₀)⁆ := hE.symm
        _ ≤ ⁅twoE6Span e X₀, twoE6Span e X₀⁆ :=
            commutator_mono (centralizerPerfectCore_le_twoE6Span e X₀)
              (centralizerPerfectCore_le_twoE6Span e X₀)
    · calc L = ⁅L, L⁆ := hL.symm
        _ ≤ ⁅twoE6Span e X₀, twoE6Span e X₀⁆ :=
            commutator_mono (le_twoE6Span e X₀) (le_twoE6Span e X₀)

theorem conjugate_eq_of_card_le_perfectCore {X L M' : Subgroup G} (hLM : L ≤ M')
    (hcard : Nat.card M' = Nat.card (centralizerPerfectCore X ⊔ L : Subgroup G))
    (hP : Nat.card (centralizerPerfectCore X) ≤
      Nat.card (perfectCore (M' ⊓ centralizer (X : Set G)))) :
    M' = centralizerPerfectCore X ⊔ L := by
  set P := perfectCore (M' ⊓ centralizer (X : Set G)) with hPdef
  have hPle : P ≤ M' ⊓ centralizer (X : Set G) := CFSG.Quasithin.perfectCore_le _
  have hPE : P ≤ centralizerPerfectCore X :=
    le_centralizerPerfectCore (CFSG.Quasithin.perfectCore_perfect _) (hPle.trans inf_le_right)
  have hPeq : P = centralizerPerfectCore X := Subgroup.eq_of_le_of_card_ge hPE hP
  have hEM : centralizerPerfectCore X ≤ M' := hPeq ▸ hPle.trans inf_le_left
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hEM hLM) hcard.le).symm

end General

section E6Inputs

@[expose] def TwoE6XiExclusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∀ φ : ∀ J, (e6Datum K).leviAmalgam J →* G, IsTwoE6GraphFamily (twoE6Span e X₀) t K φ →
      ∀ M : Subgroup G, (∃ g : G, M = CFSG.conjugate (twoE6Span e X₀) g) →
      ∀ (htM : t ∈ normalizer (M : Set G))
        (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K)
        (η : MulAut (adjointGroup TwistTag.E6.tag K)),
        (∀ x : adjointGroup TwistTag.E6.tag K, (η x : ModGL TwistTag.E6.tag K) =
          diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹) →
        ∀ (hx : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K)
          (ψ : MulAut (adjointGroup TwistTag.E6.tag K)),
          ψ * normalizerQuotMulAut eM ⟨t, htM⟩ * ψ⁻¹ ≠ MulAut.conj ⟨_, hx⟩ * η

@[expose] def TwoE6ConjugateInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∀ φ : ∀ J, (e6Datum K).leviAmalgam J →* G, IsTwoE6GraphFamily (twoE6Span e X₀) t K φ →
      ∀ g : G, t ∈ normalizer (CFSG.conjugate (twoE6Span e X₀) g : Set G) →
        CFSG.conjugate (twoE6Span e X₀) g ⊓ centralizer ({t} : Set G) = L →
        CFSG.conjugate (twoE6Span e X₀) g = twoE6Span e X₀

@[expose] def TwoE6CoreCardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∀ φ : ∀ J, (e6Datum K).leviAmalgam J →* G, IsTwoE6GraphFamily (twoE6Span e X₀) t K φ →
      ∀ g : G, t ∈ normalizer (CFSG.conjugate (twoE6Span e X₀) g : Set G) →
        CFSG.conjugate (twoE6Span e X₀) g ⊓ centralizer ({t} : Set G) = L →
        Nat.card (centralizerPerfectCore (subgroupToG e X₀)) ≤
          Nat.card (perfectCore (CFSG.conjugate (twoE6Span e X₀) g ⊓
            centralizer (subgroupToG e X₀ : Set G)))

theorem twoE6ConjugateInput_of_coreCard (h : TwoE6CoreCardInput) : TwoE6ConjugateInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' φ hφ g htM hML
  have hLM : L ≤ CFSG.conjugate (twoE6Span e X₀) g := fun x hx => by
    have hx' : x ∈ CFSG.conjugate (twoE6Span e X₀) g ⊓ centralizer ({t} : Set G) := by
      rw [hML]
      exact hx
    exact hx'.1
  have hcard : Nat.card (CFSG.conjugate (twoE6Span e X₀) g) = Nat.card (twoE6Span e X₀) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  exact conjugate_eq_of_card_le_perfectCore hLM hcard
    (h G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' φ hφ g htM hML)

end E6Inputs

section E6Main

theorem twoE6UniqueInput_of_inputs (hξ : TwoE6XiExclusionInput) (hC : TwoE6ConjugateInput) :
    TwoE6UniqueInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' φ hφ g hg
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have htC := hw.mem_centralizer
  obtain ⟨hZ0, e₆, -⟩ := exists_mulEquiv_twoE6Span_of_family hK e X₀ htC hφ
  have hG₀ := commutator_twoE6Span e X₀
  have hZ : Odd (Nat.card (center (twoE6Span e X₀))) := by
    rw [hZ0, Subgroup.card_bot]
    exact odd_one
  have htM := mem_normalizer_conjugate_inv hg
  have hMp := E6Pilot.commutator_conjugate_eq hG₀ g⁻¹
  have hZM : Odd (Nat.card (center (CFSG.conjugate (twoE6Span e X₀) g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  rcases inf_centralizer_eq_or_xi_E6_quot_27 hw.standard hw.card_eq e htC hw.orderOf_eq hw.inf_eq
      hMp hZM hw.card_eq
      ((E6Pilot.coverConjugateQuotientCenterEquiv (twoE6Span e X₀) g⁻¹).symm.trans e₆) htM with
    ⟨hCM, -⟩ | ⟨η, hη, hx, ψ, hψ⟩
  · exact mem_normalizer_of_conjugate_inv_eq
      (hC G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' φ hφ g⁻¹ htM hCM)
  · exact absurd hψ (hξ G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' φ hφ _ ⟨g⁻¹, rfl⟩ htM _ η hη hx ψ)

end E6Main

end CFSG.SeitzReduction.F4Pilot
