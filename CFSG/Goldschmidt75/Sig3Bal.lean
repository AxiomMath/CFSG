module

public import CFSG.Goldschmidt75.Sig32

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

section Core

variable {L : Type*} [Group L] [Finite L]

theorem eq_bot_of_coreSep_balance' (hO : goldschmidtOddCore L = ⊥) {V₁ V₂ X : Subgroup L}
    {t : L} (hsep : ∀ K : Subgroup L, CFSG.IsComponent K →
      V₁ ≤ centralizer (K : Set L) ∨ V₂ ≤ centralizer (K : Set L))
    (ht : orderOf t = 2) (hX : X ≤ oddCoreOf (centralizer ({t} : Set L)))
    (hC₁ : X ≤ ⁅X, V₁⁆ ⊔ oddCoreOf (centralizer (V₁ : Set L)))
    (hC₂ : X ≤ ⁅X, V₂⁆ ⊔ oddCoreOf (centralizer (V₂ : Set L))) : X = ⊥ := by
  by_contra hX1
  obtain ⟨K, hK, -, hXK, -, hXC⟩ := exists_component_of_oddCore hO ht hX1 hX
  apply hXC
  have key : ∀ V : Subgroup L, X ≤ ⁅X, V⁆ ⊔ oddCoreOf (centralizer (V : Set L)) →
      V ≤ centralizer (K : Set L) → X ≤ centralizer (K : Set L) := by
    intro V hC hVK
    refine hC.trans (sup_le (commutator_le_centralizer_of_centralizes hVK hXK) ?_)
    exact oddCoreOf_le_centralizer_of_component hK fun k hk =>
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (Subgroup.mem_centralizer_iff.mp (hVK hv) k hk).symm
  rcases hsep K hK with h | h
  · exact key V₁ hC₁ h
  · exact key V₂ hC₂ h

end Core

variable {G : Type} [Group G]

theorem le_normalizer_thetaOne {N V : Subgroup G} {t : G} (hNt : N ≤ centralizer ({t} : Set G))
    (hNV : N ≤ centralizer (V : Set G)) :
    N ≤ normalizer ((thetaOne V t : Subgroup G) : Set G) :=
  le_normalizer_sup (le_normalizer_commutator (hNt.trans (centralizer_le_normalizer_oddCent t))
      (hNV.trans (centralizer_le_normalizer _)))
    (le_normalizer_inf_of_le (hNV.trans (centralizer_le_normalizer_oddCentSub V))
      (hNt.trans (centralizer_le_normalizer_oddCent t)))

theorem le_normalizer_theta {N V₁ V₂ : Subgroup G} {t : G} (hNt : N ≤ centralizer ({t} : Set G))
    (hN₁ : N ≤ centralizer (V₁ : Set G)) (hN₂ : N ≤ centralizer (V₂ : Set G)) :
    N ≤ normalizer ((theta V₁ V₂ t : Subgroup G) : Set G) :=
  le_normalizer_inf_of_le (le_normalizer_thetaOne hNt hN₁) (le_normalizer_thetaOne hNt hN₂)

variable [Finite G]

theorem le_commutator_sup_inf {V X : Subgroup G} (hV : IsPGroup 2 V)
    (hVN : V ≤ normalizer (X : Set G)) (hX : Odd (Nat.card X)) :
    X ≤ ⁅X, V⁆ ⊔ (X ⊓ centralizer (V : Set G)) :=
  (CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2 Nat.prime_two V X
    hV hVN (Nat.coprime_two_left.mpr hX)).ge

variable {S₁ S₂ V₁ V₂ : Subgroup G}

omit [Finite G] in
theorem FourPair.le_normalizer_theta (hp : FourPair S₁ S₂ V₁ V₂) {t : G} (ht : t ∈ V₁ ⊔ V₂) :
    V₁ ⊔ V₂ ≤ normalizer ((theta V₁ V₂ t : Subgroup G) : Set G) :=
  CFSG.Goldschmidt75.le_normalizer_theta (hp.le_centralizer_of_mem ht) hp.le_centralizer_left
    hp.le_centralizer_right

theorem theta_inf_le (hp : FourPair S₁ S₂ V₁ V₂) (hsep : CoreSep S₁ S₂) {t s : G}
    (ht : t ∈ V₁ ⊔ V₂) (ht1 : t ≠ 1) (hs : s ∈ V₁ ⊔ V₂) (hs1 : s ≠ 1) :
    theta V₁ V₂ t ⊓ centralizer ({s} : Set G) ≤ theta V₁ V₂ s := by
  set L := centralizer ({s} : Set G) with hL
  set X := theta V₁ V₂ t ⊓ L with hX
  have hEL : V₁ ⊔ V₂ ≤ L := hp.le_centralizer_of_mem hs
  have hV₁L : V₁ ≤ L := le_sup_left.trans hEL
  have hV₂L : V₂ ≤ L := le_sup_right.trans hEL
  have htL : t ∈ L := hEL ht
  have hXL : X ≤ L := inf_le_right
  have hXO : X ≤ oddCent t :=
    inf_le_left.trans (theta_le_oddCent (le_sup_left.trans (hp.le_centralizer_of_mem ht)))
  have hXodd : Odd (Nat.card X) :=
    Odd.of_dvd_nat (Balance.odd_card_oddCoreOf _) (card_dvd_of_le hXO)
  have hEN : V₁ ⊔ V₂ ≤ normalizer (X : Set G) :=
    le_normalizer_inf_of_le (hp.le_normalizer_theta ht) (hEL.trans le_normalizer)
  have hfac₁ : X ≤ ⁅X, V₁⁆ ⊔ (X ⊓ centralizer (V₁ : Set G)) :=
    le_commutator_sup_inf hp.isPGroup_left (le_sup_left.trans hEN) hXodd
  have hfac₂ : X ≤ ⁅X, V₂⁆ ⊔ (X ⊓ centralizer (V₂ : Set G)) :=
    le_commutator_sup_inf hp.isPGroup_right (le_sup_right.trans hEN) hXodd
  have hC₁ : X ⊓ centralizer (V₁ : Set G) ≤ oddCentSub V₁ :=
    (inf_le_inf_right _ (inf_le_left.trans inf_le_left)).trans (thetaOne_inf_le hp hsep ht ht1)
  have hC₂ : X ⊓ centralizer (V₂ : Set G) ≤ oddCentSub V₂ :=
    (inf_le_inf_right _ (inf_le_left.trans inf_le_right)).trans
      (thetaOne_inf_le_right hp hsep ht ht1)
  have hXs : X ≤ oddCent s := by
    show X ≤ oddCoreOf L
    rw [← G37.barOf_eq_bot_iff hXL]
    have hord : orderOf t = 2 := hp.orderOf_eq_two ht ht1
    refine eq_bot_of_coreSep_balance' (L := L ⧸ goldschmidtOddCore L) oddCore_quotient_eq_bot
      (V₁ := barOf L V₁) (V₂ := barOf L V₂) ?_ (orderOf_mk_eq_two htL hord)
      (barOf_le_oddCent htL hord hXO) ?_ ?_
    · intro K hK
      rcases hsep s (sup_le_sup hp.le_left hp.le_right hs) (hp.orderOf_eq_two hs hs1) K hK with
        h | h
      · exact Or.inl ((G37.barOf_mono hp.le_left).trans h)
      · exact Or.inr ((G37.barOf_mono hp.le_right).trans h)
    · exact barOf_le_commutator_sup hXL hV₁L hp.isPGroup_left
        (hfac₁.trans (sup_le_sup_left (le_inf hC₁ (inf_le_left.trans hXL)) _))
    · exact barOf_le_commutator_sup hXL hV₂L hp.isPGroup_right
        (hfac₂.trans (sup_le_sup_left (le_inf hC₂ (inf_le_left.trans hXL)) _))
  have hθ₁ : X ≤ thetaOne V₁ s := hfac₁.trans
    (sup_le_sup (commutator_mono hXs le_rfl) (le_inf hC₁ (inf_le_left.trans hXs)))
  have hθ₂ : X ≤ thetaOne V₂ s := hfac₂.trans
    (sup_le_sup (commutator_mono hXs le_rfl) (le_inf hC₂ (inf_le_left.trans hXs)))
  exact le_inf hθ₁ hθ₂

end CFSG.Goldschmidt75
