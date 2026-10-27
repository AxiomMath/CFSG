module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Interfaces
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.QuasithinUnique.Setup

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

@[expose] def uniqueMaxOver (S P : Subgroup G) : Subgroup G :=
  sSup {X : Subgroup G | S ≤ X ∧ X < P}

@[expose] def oddOrderSubgroup (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ P ∧ Odd (orderOf x)}

@[expose] def HasNoTwoQuotient (X : Subgroup G) : Prop :=
  ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤

@[expose] def IsReducedOffender (S V A : Subgroup G) : Prop :=
  IsMaxElemAbelian S A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) ∧
    V ⊓ Subgroup.centralizer (A : Set G) = A ⊓ V ∧
    Nat.card V ≤ (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))

structure FFActor (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)) : Prop where
  elementary : ∀ v : V, v * v = 1
  o2_trivial : ∀ N : Subgroup (MulAut V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥
  sylow : IsSylowTwoOf T H
  not_normal : ¬ (T.subgroupOf H).Normal
  max : T ≤ M ∧ M < H ∧ ∀ X : Subgroup (MulAut V), T ≤ X → X < H → X ≤ M
  sqt : CFSG.IsStronglyQuasithin H
  offender : E ≤ H ∧ E ≠ ⊥ ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    Nat.card V ≤ Nat.card E * Nat.card (fixV E)

structure ReducedAction (G : Type) [Group G] (S P V : Subgroup G) : Prop where
  obstruction : PushUpObstruction S P
  eq_conjClosure : V = conjClosure (omegaOneCenterOf S) P
  ne_bot : V ≠ ⊥
  reduced : IsTwoReducedIn P V
  le_omegaOneCenter : V ≤ omegaOneCenterOf (pCoreOf 2 P)
  not_le_centralizer : ¬ P ≤ Subgroup.centralizer (V : Set G)
  centralizer_le : P ⊓ Subgroup.centralizer (V : Set G) ≤ uniqueMaxOver S P
  centralizer_sylow : S ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 P
  image_sylow : IsSylowTwoOf (autOn S V) (autOn P V)
  image_not_normal : ¬ ((autOn S V).subgroupOf (autOn P V)).Normal
  image_max : autOn S V ≤ autOn (uniqueMaxOver S P) V ∧ autOn (uniqueMaxOver S P) V < autOn P V ∧
    ∀ X : Subgroup (MulAut V), autOn S V ≤ X → X < autOn P V → X ≤ autOn (uniqueMaxOver S P) V
  image_pCore : pCoreOf 2 (autOn P V) = ⊥
  thompson_not_le : ¬ thompsonJ S ≤ pCoreOf 2 P
  thompson_not_le_centralizer : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G)
  offender : ∃ A : Subgroup G, IsReducedOffender S V A
  eq_oddOrder_sup : P = oddOrderSubgroup P ⊔ S
  noTwoQuotient : HasNoTwoQuotient (oddOrderSubgroup P)
  commutator_thompson : ⁅oddOrderSubgroup P, thompsonJ S⁆ = oddOrderSubgroup P
  detect : ∀ A₀ : Subgroup G, A₀ ≤ S → S ≤ Subgroup.normalizer (A₀ : Set G) →
    (⁅oddOrderSubgroup P, A₀⁆ < oddOrderSubgroup P ↔ A₀ ≤ pCoreOf 2 P) ∧
    (A₀ ≤ pCoreOf 2 P ↔ A₀ ≤ Subgroup.centralizer (V : Set G))

theorem eq_uniqueMaxOver {S P K : Subgroup G} (hSK : S ≤ K) (hKP : K < P)
    (hK : ∀ X : Subgroup G, S ≤ X → X < P → X ≤ K) : K = uniqueMaxOver S P :=
  le_antisymm (le_sSup ⟨hSK, hKP⟩) (sSup_le fun _ hX => hK _ hX.1 hX.2)

theorem uniqueMaxOver_spec {S P : Subgroup G} (h : IsMinimalParabolic S P) :
    S ≤ uniqueMaxOver S P ∧ uniqueMaxOver S P < P ∧
      ∀ X : Subgroup G, S ≤ X → X < P → X ≤ uniqueMaxOver S P := by
  obtain ⟨-, -, K, hSK, hKP, hK⟩ := h
  rw [← eq_uniqueMaxOver hSK hKP hK]
  exact ⟨hSK, hKP, hK⟩

namespace ReducedAction

variable {G : Type} [Group G] {S P V : Subgroup G}

theorem isElemAbelian (hR : ReducedAction G S P V) : IsElemAbelian 2 V :=
  hR.reduced.2.2.1

theorem le_normalizer (hR : ReducedAction G S P V) : P ≤ Subgroup.normalizer (V : Set G) :=
  hR.reduced.2.1

theorem le_P (hR : ReducedAction G S P V) : V ≤ P :=
  hR.reduced.1

theorem sylow_le (hR : ReducedAction G S P V) : S ≤ P :=
  hR.obstruction.sylow.1

theorem toActor_of_offender [Finite G] {A : Subgroup G} (hR : ReducedAction G S P V)
    (hA : IsReducedOffender S V A) (hsqt : CFSG.IsStronglyQuasithin (autOn P V)) :
    @FFActor V (commGroupOfElemAbelian hR.isElemAbelian) inferInstance (autOn P V) (autOn S V)
      (autOn (uniqueMaxOver S P) V) (autOn A V) := by
  have hV := hR.isElemAbelian
  have hAP : A ≤ P := hA.1.1.trans hR.sylow_le
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAP.trans hR.le_normalizer
  have hAe := isElemAbelian2_autOn hV hA.1.2.1 hAn
  let _ : CommGroup V := commGroupOfElemAbelian hV
  refine ⟨fun v => ?_, fun N hNH hNn hN2 => ?_, hR.image_sylow, hR.image_not_normal, hR.image_max,
    hsqt, autOn_le_autOn V hAP, autOn_ne_bot_of_not_le_centralizer hAn hA.2.1, hAe.1, hAe.2, ?_⟩
  · exact Subtype.ext (by simpa [sq] using hV.2 v v.2)
  · exact le_bot_iff.mp (hR.image_pCore ▸
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 N _ hNH hNn hN2)
  · rw [card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hV hAn]
    exact hA.2.2.2

theorem toActor [Finite G] (hR : ReducedAction G S P V)
    (hsqt : CFSG.IsStronglyQuasithin (autOn P V)) :
    ∃ A : Subgroup G, IsReducedOffender S V A ∧
      @FFActor V (commGroupOfElemAbelian hR.isElemAbelian) inferInstance (autOn P V) (autOn S V)
        (autOn (uniqueMaxOver S P) V) (autOn A V) := by
  obtain ⟨A, hA⟩ := hR.offender
  exact ⟨A, hA, hR.toActor_of_offender hA hsqt⟩

end ReducedAction

end CFSG.QuasithinUnique.Setup
