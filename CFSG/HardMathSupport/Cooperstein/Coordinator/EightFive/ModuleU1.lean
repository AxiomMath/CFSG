module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleSec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section General

variable {V : Type*} [CommGroup V] {H L : Subgroup (MulAut V)}

@[expose] def OneNoncentral (H L : Subgroup (MulAut V)) : Prop :=
  ∀ Y₀ Y₁ Y₂ Y₃ : Subgroup V, IsChiefFac H Y₀ Y₁ → IsChiefFac H Y₂ Y₃ → Y₁ ≤ Y₂ →
    ¬ IsCentralSec L Y₀ Y₁ → ¬ IsCentralSec L Y₂ Y₃ → False

theorem not_isCentralSec_of_lt_commV (hL : commutator ↥L = ⊤) {U'' : Subgroup V}
    (hU : U'' < commV L) : ¬ IsCentralSec L U'' (commV L) := by
  intro h
  have h1 := isCentralSec_iff_commSub_le.1 h
  rw [commSub_commV_of_perfect hL] at h1
  exact lt_irrefl _ (hU.trans_le h1)

theorem not_isCentralSec_of_isChiefFac_commV (hL : commutator ↥L = ⊤) {U'' : Subgroup V}
    (hU : IsChiefFac H U'' (commV L)) : ¬ IsCentralSec L U'' (commV L) :=
  not_isCentralSec_of_lt_commV hL hU.lt

theorem OneNoncentral.below (hL : commutator ↥L = ⊤) (hone : OneNoncentral H L) :
    ∀ Y₀ Y₁ U'' : Subgroup V, IsChiefFac H U'' (commV L) → IsChiefFac H Y₀ Y₁ →
      Y₁ ≤ U'' → ¬ IsCentralSec L Y₀ Y₁ → False :=
  fun Y₀ Y₁ U'' hU hY hY₁ hYL =>
    hone Y₀ Y₁ U'' (commV L) hY hU hY₁ hYL (not_isCentralSec_of_isChiefFac_commV hL hU)

variable [Finite V]

theorem eq_inf_fixV_of_isChiefFac_commV (hN : H ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hL : commutator ↥L = ⊤)
    (hone : ∀ Y₀ Y₁ U'' : Subgroup V, IsChiefFac H U'' (commV L) → IsChiefFac H Y₀ Y₁ →
      Y₁ ≤ U'' → ¬ IsCentralSec L Y₀ Y₁ → False)
    {U'' : Subgroup V} (hU : IsChiefFac H U'' (commV L)) : U'' = commV L ⊓ fixV L := by
  have hU''L : U'' ≤ fixV L := by
    by_contra hc
    obtain ⟨Y₀, Y₁, hY, hY₁, hYL⟩ := exists_isChiefFac_of_perfect hL hU.stab₀ hc
    exact hone Y₀ Y₁ U'' hU hY hY₁ hYL
  rcases hU.eq_or_eq (le_stabSub_inf (le_stabSub_commV hN) (le_stabSub_fixV hN))
      (le_inf hU.le hU''L) inf_le_left with h | h
  · exact h.symm
  · exact absurd (inf_eq_left.1 h)
      (not_le_fixV_commV_of_perfect hL (ne_bot_of_gt hU.lt))

theorem le_fixV_of_lt_commV (hN : H ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hL : commutator ↥L = ⊤)
    (hone : ∀ Y₀ Y₁ U'' : Subgroup V, IsChiefFac H U'' (commV L) → IsChiefFac H Y₀ Y₁ →
      Y₁ ≤ U'' → ¬ IsCentralSec L Y₀ Y₁ → False)
    {Z : Subgroup V} (hZ : H ≤ stabSub Z) (hZU : Z < commV L) : Z ≤ fixV L := by
  obtain ⟨U'', hZU'', hU⟩ := exists_isChiefFac_of_lt hZU hZ (le_stabSub_commV hN)
  rw [eq_inf_fixV_of_isChiefFac_commV hN hL hone hU] at hZU''
  exact hZU''.trans inf_le_right

theorem isChiefFac_inf_fixV_commV (hN : H ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hL : commutator ↥L = ⊤) (hV : commV L ≠ ⊥)
    (hone : ∀ Y₀ Y₁ U'' : Subgroup V, IsChiefFac H U'' (commV L) → IsChiefFac H Y₀ Y₁ →
      Y₁ ≤ U'' → ¬ IsCentralSec L Y₀ Y₁ → False) :
    IsChiefFac H (commV L ⊓ fixV L) (commV L) ∧
      ¬ IsCentralSec L (commV L ⊓ fixV L) (commV L) := by
  obtain ⟨U'', -, hU⟩ := exists_isChiefFac_of_lt (bot_lt_iff_ne_bot.2 hV) (le_stabSub_bot H)
    (le_stabSub_commV hN)
  rw [eq_inf_fixV_of_isChiefFac_commV hN hL hone hU] at hU
  exact ⟨hU, not_isCentralSec_of_isChiefFac_commV hL hU⟩

theorem u1 (hN : H ≤ Subgroup.normalizer (L : Set (MulAut V))) (hL : commutator ↥L = ⊤)
    (hV : commV L ≠ ⊥) (hone : OneNoncentral H L) :
    IsChiefFac H (commV L ⊓ fixV L) (commV L) ∧
      ¬ IsCentralSec L (commV L ⊓ fixV L) (commV L) ∧
      (∀ U'' : Subgroup V, IsChiefFac H U'' (commV L) → U'' = commV L ⊓ fixV L) ∧
      ∀ Z : Subgroup V, H ≤ stabSub Z → Z < commV L → Z ≤ fixV L :=
  ⟨(isChiefFac_inf_fixV_commV hN hL hV (hone.below hL)).1,
    (isChiefFac_inf_fixV_commV hN hL hV (hone.below hL)).2,
    fun _ hU => eq_inf_fixV_of_isChiefFac_commV hN hL (hone.below hL) hU,
    fun _ hZ hZU => le_fixV_of_lt_commV hN hL (hone.below hL) hZ hZU⟩

end General

section AltPre

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)}

theorem u1_altPre (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) (hV : commV (altPre ψ) ≠ ⊥)
    (hone : OneNoncentral H (altPre ψ)) :
    IsChiefFac H (commV (altPre ψ) ⊓ fixV (altPre ψ)) (commV (altPre ψ)) ∧
      ¬ IsCentralSec (altPre ψ) (commV (altPre ψ) ⊓ fixV (altPre ψ)) (commV (altPre ψ)) ∧
      (∀ U'' : Subgroup V, IsChiefFac H U'' (commV (altPre ψ)) →
        U'' = commV (altPre ψ) ⊓ fixV (altPre ψ)) ∧
      ∀ Z : Subgroup V, H ≤ stabSub Z → Z < commV (altPre ψ) → Z ≤ fixV (altPre ψ) :=
  u1 le_normalizer_altPre (commutator_altPre_eq_top h5 hψ hA) hV hone

theorem oneNoncentral_altPre (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender H A)
    (hbound : ∀ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ → ¬ IsCentralSec (altPre ψ) Y₀ Y₁ →
      Nat.card A ≤ (fixV (autSec A Y₁ Y₀)).index) :
    OneNoncentral H (altPre ψ) := fun Y₀ Y₁ _ _ h₁ h₃ h12 hc₁ hc₃ =>
  false_of_index_le_of_one_lt hA h₁.le h12 h₃.le (hA.1.trans h₁.stab₁) (hA.1.trans h₃.stab₁)
    (hbound Y₀ Y₁ h₁ hc₁)
    (one_lt_index_fixV_autSec h5 hψ hAlt h₃.stab₀ h₃.stab₁ hc₃ hA.1 hA.2.1)

end AltPre

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
