module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleCrit

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {T : Type} [Group T] [Finite T]

theorem sig_generalizedFitting_eq_top [IsSimpleGroup T] : CFSG.generalizedFitting T = ⊤ := by
  have hN : (CFSG.generalizedFitting T).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := T)).2
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : T)
    have h1 := CFSG.centralizer_generalizedFitting_le T
    rw [h] at h1
    have hxc : x ∈ Subgroup.centralizer ((⊥ : Subgroup T) : Set T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hm
      rw [hm, one_mul, mul_one]
    exact hx (Subgroup.mem_bot.mp (h1 hxc))
  · exact h

theorem twoComponentsQuasisimpleAt_of_oddCore
    (h : ∀ t : T, orderOf t = 2 → CFSG.oddCore ↥(centralizer ({t} : Set T)) = ⊥) :
    TwoComponentsQuasisimpleAt T := by
  intro y hy2 K hK
  have hO : oddCoreIn (centralizer ({y} : Set T)) = ⊥ := by
    have h2 : pPrimeCore 2 ↥(centralizer ({y} : Set T)) = ⊥ := by
      rw [← h y hy2]
      simp only [pPrimeCore, CFSG.oddCore, Nat.coprime_two_left]
    rw [oddCoreIn, h2, Subgroup.map_bot]
  have hOK : pPrimeCore 2 ↥K = ⊥ := by
    have h3 := (oddCoreIn_le_of_isTwoComponentIn hK).trans hO.le
    rwa [oddCoreIn, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h3
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot)
    (isQuasisimple_quotient_of_isPComponent hK.1 hK.2)

omit [Finite T] in
theorem isComponent_subgroupOf_of_isTwoComponentIn {K C : Subgroup T}
    (hK : IsTwoComponentIn K C) (hq : CFSG.IsQuasisimple K) :
    CFSG.IsComponent (K.subgroupOf C) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hK.1).symm hq, ?_⟩
  obtain ⟨-, -, hsub, -, -⟩ := hK.2
  exact hsub

omit [Finite T] in
theorem isComponentOf_of_isTwoComponentIn {K C : Subgroup T}
    (hK : IsTwoComponentIn K C) (hq : CFSG.IsQuasisimple K) :
    CFSG.Assembly.IsComponentOf K C :=
  (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hK.1).mpr
    (isComponent_subgroupOf_of_isTwoComponentIn hK hq)

omit [Finite T] in
theorem card_quot_center_subgroupOf {K C : Subgroup T} (hKC : K ≤ C) :
    Nat.card (↥(K.subgroupOf C) ⧸ center ↥(K.subgroupOf C)) = Nat.card (↥K ⧸ center ↥K) := by
  let e : ↥(K.subgroupOf C) ≃* ↥K := subgroupOfEquivOfLe hKC
  have he : (center ↥(K.subgroupOf C)).map e.toMonoidHom = center ↥K :=
    Subgroup.map_center_eq e
  exact Nat.card_congr (QuotientGroup.congr _ _ e he).toEquiv

theorem singleComponentCleanAt_of_primePow {P : (S : Type) → [Group S] → Prop} (p k : ℕ)
    (h : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T →
      (∀ (y : T) (K : Subgroup T), orderOf y = 2 →
        IsTwoComponentIn K (centralizer ({y} : Set T)) → CFSG.IsQuasisimple K →
        2 ≤ CFSG.Open.pRank 2 K → p ^ k ∣ Nat.card (↥K ⧸ center ↥K)) ∧
      ¬ p ^ (2 * k) ∣ Nat.card T) :
    SingleComponentCleanAt P := by
  refine singleComponentCleanAt_of_card fun T _ _ hT hP y₁ y₂ K₁ K₂ hy₁ hy₂ hK₁ hK₂ hq₁ hq₂ hr₁
    hr₂ hdvd => ?_
  obtain ⟨hc, hT'⟩ := h T hT hP
  exact hT' ((two_mul k ▸ pow_add p k k ▸
    Nat.mul_dvd_mul (hc y₁ K₁ hy₁ hK₁ hq₁ hr₁) (hc y₂ K₂ hy₂ hK₂ hq₂ hr₂)).trans hdvd)

theorem singleComponentCleanAt_of_forall_false {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T →
      ∀ (y : T) (K : Subgroup T), orderOf y = 2 →
        IsTwoComponentIn K (centralizer ({y} : Set T)) → CFSG.IsQuasisimple K →
        2 ≤ CFSG.Open.pRank 2 K → False) :
    SingleComponentCleanAt P := by
  intro T _ _ hT hP X Y hXq hYq hXr hYr hXY hXc hYc
  obtain ⟨y, hyY, hy2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hYr)
  exact h T hT hP y X hy2 (hXc y hyY hy2) hXq hXr

end CFSG.ComponentClassification.Sol76.Sig
