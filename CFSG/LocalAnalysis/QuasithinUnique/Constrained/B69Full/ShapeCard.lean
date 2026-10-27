module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.B69ShapeNat

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem card_autSub_mul_card_le_of_sec (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hS : Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L))) ≤
      Nat.card (Sec W (W ⊓ fixV L))) :
    Nat.card (autSub A W) * Nat.card ↥(W ⊓ fixV A) ≤ Nat.card W := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hL hLA hW
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hUW : W ⊓ fixV L ≤ W := inf_le_left
  have hAU : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hker : A ⊓ centSec W (W ⊓ fixV L) = A ⊓ centSub W := by
    apply le_antisymm
    · rintro a ⟨haA, ha⟩
      refine ⟨haA, ?_⟩
      have := sec_triv_imp_triv hL hAn hW hAW haA fun w hw => (ha.2 w hw).2
      intro w hw
      exact this w hw
    · rintro a ⟨haA, ha⟩
      refine ⟨haA, hAst haA, fun w hw => ?_⟩
      rw [ha w hw, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hcard : Nat.card (autSub A W) = Nat.card (autSec A W (W ⊓ fixV L)) := by
    have e1 := card_autSub_mul hAst
    have e2 := card_autSec_mul hAst hAU
    rw [hker] at e2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e1.trans e2.symm)
  have h2 := card_inf_fixV_le_autSec hUW hAst
  have h3 : Nat.card ↥((W ⊓ fixV L) ⊓ fixV A) ≤ Nat.card ↥(W ⊓ fixV L) :=
    Subgroup.card_le_of_le inf_le_left
  have h4 := card_sec_mul hUW
  rw [hcard]
  set a := Nat.card (autSec A W (W ⊓ fixV L))
  set cS := Nat.card (fixV (autSec A W (W ⊓ fixV L)))
  set c := Nat.card ↥(W ⊓ fixV A)
  set cU := Nat.card ↥((W ⊓ fixV L) ⊓ fixV A)
  set u := Nat.card ↥(W ⊓ fixV L)
  set s := Nat.card (Sec W (W ⊓ fixV L))
  have h5 : a * c ≤ s * u := by
    calc a * c ≤ a * (cS * cU) := Nat.mul_le_mul_left _ h2
      _ ≤ a * (cS * u) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ = (a * cS) * u := by ring
      _ ≤ s * u := Nat.mul_le_mul_right _ hS
  rw [h4] at h5
  exact h5

theorem card_mul_card_fixV_le_of_sup_eq_top {A : Subgroup (MulAut V)} {W : Subgroup V}
    (hAst : A ≤ stabSub W) (hsup : W ⊔ fixV A = ⊤) (hfaith : A ⊓ centSub W = ⊥)
    (hle : Nat.card (autSub A W) * Nat.card ↥(W ⊓ fixV A) ≤ Nat.card W) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card V := by
  have hAW : Nat.card (autSub A W) = Nat.card A := by
    have e := card_autSub_mul hAst
    rw [hfaith, Subgroup.card_bot, mul_one] at e
    exact e
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W (fixV A)
    (fun x _ y _ => mul_comm x y)).1
  rw [hsup, Subgroup.card_top] at hprod
  rw [hAW] at hle
  have hc : 0 < Nat.card ↥(W ⊓ fixV A) := Nat.card_pos
  have key : Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A) ≤
      Nat.card V * Nat.card ↥(W ⊓ fixV A) := by
    calc Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A)
        = (Nat.card A * Nat.card ↥(W ⊓ fixV A)) * Nat.card (fixV A) := by ring
      _ ≤ Nat.card W * Nat.card (fixV A) := Nat.mul_le_mul_right _ hle
      _ = Nat.card V * Nat.card ↥(W ⊓ fixV A) := hprod.symm
  exact Nat.le_of_mul_le_mul_right key hc

theorem not_rAV_lt_one_of_shape (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hshape : CompShape T M A L W) : ¬ rAV A < 1 := by
  rcases hshape with ⟨⟨e, he, hnat⟩, hsyl, -⟩ | ⟨k, -, π, -, -, -, ⟨i, j, -, hAij⟩, -⟩
  · have hS := sec_card_le_of_natural hV hA hL hLA hW he hnat hsyl
    have hle := card_autSub_mul_card_le_of_sec hV hA hL hLA hW hS
    obtain ⟨hsup, hfaith⟩ := eq_sup_fixV_of_natural hV hA hL hLA hW he hnat hsyl
    have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant (a_stab_irr hV hA hL hLA hW)
    intro hlt
    have h1 := (rAV_lt_one_iff hV hA.1.isA2).1 hlt
    have h2 := card_mul_card_fixV_le_of_sup_eq_top hAst hsup hfaith hle
    omega
  · have hc : Nat.card A ≤ 2 := by
      rw [hAij]
      exact card_le_two_of_swap _ i j
    have hne : A ≠ ⊥ := hA.1.2.1
    have h1 : Nat.card A ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
    have h0 : 0 < Nat.card A := Nat.card_pos
    exact not_rAV_lt_one_of_card_two hV hA.1.isA2 (by omega)

end B69

end CFSG.Quasithin
