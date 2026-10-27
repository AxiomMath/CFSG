module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleDesc

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement

@[expose] def OddFullCoverAt {T : Type} [Group T] (Y : Subgroup T) (x : T) : Prop :=
  ∃ P R J : Subgroup T, IsTwoComponentIn P (centralizer ({x} : Set T)) ∧
    R ≤ centralizer ({x} : Set T) ∧ (R.subgroupOf (centralizer ({x} : Set T))).Normal ∧
    Odd (Nat.card R) ∧ J ≤ Y ⊓ centralizer ({x} : Set T) ∧ ⁅J, J⁆ = J ∧ P ≤ J ⊔ R ∧
    J ≤ P ⊔ R ∧ J ⊔ oddCoreIn Y = Y

@[expose] def SingleComponentSimpleFullAt (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T → ∀ X Y : Subgroup T,
    ⁅X, X⁆ = X → ⁅Y, Y⁆ = Y →
    IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) → IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y) →
    2 ≤ CFSG.Open.pRank 2 X → 2 ≤ CFSG.Open.pRank 2 Y →
    ⁅X, Y⁆ ≤ oddCoreIn X ⊓ oddCoreIn Y →
    (∀ x ∈ X, orderOf x = 2 → OddFullCoverAt Y x) →
    (∀ y ∈ Y, orderOf y = 2 → OddFullCoverAt X y) →
    False

theorem le_coreActionKernel_of_commutator_le_oddCoreIn {G : Type} [Group G] {X Y : Subgroup G}
    (h : ⁅X, Y⁆ ≤ oddCoreIn Y) : X ≤ coreActionKernel Y := by
  have hOY : oddCoreIn Y ≤ Y := map_subtype_le _
  have hconj : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun x hx y hy => by
    have h1 : ⁅x, y⁆ * y ∈ Y := mul_mem (hOY (h (commutator_mem_commutator hx hy))) hy
    rwa [commutatorElement_def, inv_mul_cancel_right] at h1
  have h' : ⁅Y, X⁆ ≤ oddCoreIn Y := (Subgroup.commutator_comm Y X).le.trans h
  intro x hx
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj x hx y hy, fun hy => ?_⟩
    have h2 := hconj x⁻¹ (inv_mem hx) _ hy
    simpa [mul_assoc] using h2
  · have h4 := h' (commutator_mem_commutator (inv_mem hj) (inv_mem hx))
    rw [commutatorElement_def, inv_inv, inv_inv] at h4
    exact h4

variable {Q : Type} [Group Q] [Finite Q]

theorem twoLayerIn_inf_centralizer_sup_oddCoreIn {Y : Subgroup Q}
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) {x : Q} (hx2 : orderOf x = 2)
    (hxY : x ∈ coreActionKernel Y) :
    twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ⊔ oddCoreIn Y = Y := by
  have hU2 : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hsup := inf_centralizer_sup_oddCoreIn_eq hU2 (zpowers_le.mpr hxY)
  have hCzx : centralizer ((zpowers x : Subgroup Q) : Set Q) = centralizer ({x} : Set Q) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hCzx] at hsup
  obtain ⟨-, hL, hcov, -⟩ := cover_facts hYq inf_le_left hsup
  rw [hL]
  exact hcov

theorem oddFullCoverAt_map (hO : pPrimeCore 2 Q = ⊥) {X Y : Subgroup Q} (hXZ : X ⊓ center Q = ⊥)
    (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y)) (hXY : X ≤ coreActionKernel Y)
    (hP : ∀ x ∈ X, orderOf x = 2 → ∃ P : Subgroup Q,
      IsTwoComponentIn P (centralizer ({x} : Set Q)) ∧
      P ⊔ oddCoreIn (centralizer ({x} : Set Q)) =
        twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ⊔ oddCoreIn (centralizer ({x} : Set Q)))
    {t : Q ⧸ center Q} (ht : t ∈ X.map (QuotientGroup.mk' (center Q))) (ht2 : orderOf t = 2) :
    OddFullCoverAt (Y.map (QuotientGroup.mk' (center Q))) t := by
  obtain ⟨x, hxX, rfl⟩ := ht
  have hx2 := orderOf_eq_two_of_mk hXZ hxX ht2
  obtain ⟨P, hPC, heq⟩ := hP x hxX hx2
  have hOC : oddCoreIn (centralizer ({x} : Set Q)) ≤ centralizer ({x} : Set Q) :=
    map_subtype_le _
  have hLC : twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ≤ Y ⊓ centralizer ({x} : Set Q) :=
    map_subtype_le _
  have hcov := twoLayerIn_inf_centralizer_sup_oddCoreIn hYq hx2 (hXY hxX)
  refine ⟨P.map (QuotientGroup.mk' (center Q)),
    (oddCoreIn (centralizer ({x} : Set Q))).map (QuotientGroup.mk' (center Q)),
    (twoLayerIn (Y ⊓ centralizer ({x} : Set Q))).map (QuotientGroup.mk' (center Q)),
    isTwoComponentIn_map_center hO hPC,
    (map_mono hOC).trans (map_centralizer_le_centralizer_mk x),
    map_subgroupOf_normal fun q hq => mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hq),
    ?_, le_inf (map_mono (hLC.trans inf_le_left))
      ((map_mono (hLC.trans inf_le_right)).trans (map_centralizer_le_centralizer_mk x)),
    by rw [← Subgroup.map_commutator, commutator_twoLayerIn_self],
    (map_mono (le_sup_left.trans heq.le)).trans (Subgroup.map_sup _ _ _).le,
    (map_mono (le_sup_left.trans heq.ge)).trans (Subgroup.map_sup _ _ _).le, ?_⟩
  · exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_oddCoreIn _))
      (Subgroup.card_map_dvd _ _)
  · refine le_antisymm (sup_le (map_mono (hLC.trans inf_le_left)) (map_subtype_le _)) ?_
    calc Y.map (QuotientGroup.mk' (center Q))
        = (twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ⊔ oddCoreIn Y).map
            (QuotientGroup.mk' (center Q)) := by rw [hcov]
      _ = (twoLayerIn (Y ⊓ centralizer ({x} : Set Q))).map (QuotientGroup.mk' (center Q)) ⊔
            (oddCoreIn Y).map (QuotientGroup.mk' (center Q)) := Subgroup.map_sup _ _ _
      _ ≤ _ := sup_le_sup_left (map_oddCoreIn_le_oddCoreIn_map Y) _

theorem singleComponentQuasisimpleAt_of_simpleFullAt {P : (S : Type) → [Group S] → Prop}
    (h : SingleComponentSimpleFullAt P) : SingleComponentQuasisimpleAt P := by
  intro Q _ _ hQ hO hPQ X Y hXp hYp hXq hYq hXr hYr hcomm hP₁ hP₂
  have hXZ := inf_center_eq_bot_left hQ hO hXp hXq hcomm hP₁
  have hYZ := inf_center_eq_bot_right hQ hO hYp hYq hcomm hP₂
  have hXY : X ≤ coreActionKernel Y :=
    le_coreActionKernel_of_commutator_le_oddCoreIn (hcomm.trans inf_le_right)
  have hYX : Y ≤ coreActionKernel X :=
    le_coreActionKernel_of_commutator_le_oddCoreIn ((commutator_comm Y X).le.trans
      (hcomm.trans inf_le_left))
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  refine h (Q ⧸ center Q) this hPQ (X.map (QuotientGroup.mk' (center Q)))
    (Y.map (QuotientGroup.mk' (center Q))) (by rw [← Subgroup.map_commutator, hXp])
    (by rw [← Subgroup.map_commutator, hYp]) (isQuasisimple_map_mk hXZ hXq)
    (isQuasisimple_map_mk hYZ hYq) (hXr.trans (pRank_le_pRank_map_mk hXZ))
    (hYr.trans (pRank_le_pRank_map_mk hYZ)) ?_
    (fun t ht ht2 => oddFullCoverAt_map hO hXZ hYq hXY hP₁ ht ht2)
    (fun t ht ht2 => oddFullCoverAt_map hO hYZ hXq hYX hP₂ ht ht2)
  rw [← Subgroup.map_commutator]
  exact (map_mono hcomm).trans (le_inf
    ((map_mono inf_le_left).trans (map_oddCoreIn_le_oddCoreIn_map X))
    ((map_mono inf_le_right).trans (map_oddCoreIn_le_oddCoreIn_map Y)))

end CFSG.ComponentClassification.Sol76.Sig
