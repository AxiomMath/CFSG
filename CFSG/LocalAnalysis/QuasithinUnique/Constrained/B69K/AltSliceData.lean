module

public import CFSG.Quasithin.Background.FFC13E

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69K

open CFSG.Quasithin.B69

variable {V : Type} [CommGroup V] [Finite V]

theorem alt_data_general {m : ℕ} (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X)
    (hLA : ⁅L, A⁆ = L) {W U : Subgroup V} (hU : U = ⊥) (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hLU : L ≤ stabSub U) (hAU : A ≤ stabSub U) (hsup : W ⊔ fixV A = ⊤)
    {J : Subgroup (MulAut (Sec W U))} (hJ : J = autSec (L ⊔ A) W U)
    (π : Equiv.Perm (Fin m) →* ↥J) (hπi : Function.Injective π)
    (hπ : (FFModel.symDn m).RealizesVia J ⊤ ⊥ π)
    (hLeq : autSec L W U = (alternatingGroup (Fin m)).map (J.subtype.comp π))
    {t : Equiv.Perm (Fin m)} (ht : t.IsSwap)
    (hAeq : autSec A W U = (Subgroup.zpowers t).map (J.subtype.comp π)) :
    ∃ π' : Equiv.Perm (Fin m) →* ↥(L ⊔ A), Function.Injective π' ∧ Function.Surjective π' ∧
      (FFModel.symDn m).RealizesVia (L ⊔ A) W ⊥ π' ∧
      L = (alternatingGroup (Fin m)).map ((L ⊔ A).subtype.comp π') ∧
      ∃ i j : Fin m, i ≠ j ∧
        A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π') := by
  subst hU
  subst hJ
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW).1
  have hAW : A ≤ stabSub W :=
    B1.le_stabSub_of_invariant (a_stab_irr hV hA hL.2.2 hLA hW)
  have hZW : L ⊔ A ≤ stabSub W := sup_le hLW hAW
  have hZU : L ⊔ A ≤ stabSub ⊥ := sup_le hLU hAU
  have hfaith : (L ⊔ A) ⊓ centSec W ⊥ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, hgc⟩
    rw [Subgroup.mem_bot]
    refine eq_one_of_trivial_on_W hV hO2 hA hL hLA hW hsup hg fun w hw => ?_
    have := hgc.2 w hw
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  set E := B5.secEquiv (L ⊔ A) hZW hZU hfaith with hE
  let π' : Equiv.Perm (Fin m) →* ↥(L ⊔ A) := E.symm.toMonoidHom.comp π
  have hψ : ∀ σ, B5.secHom (L ⊔ A) hZW hZU (π' σ) =
      (((autSec (L ⊔ A) W ⊥).subtype.comp π) σ : MulAut (Sec W ⊥)) := fun σ =>
    (B5.secHom_symm hZW hZU hfaith (π σ)).symm
  obtain ⟨i, j, hij, rfl⟩ := ht
  refine ⟨π', fun a b h => hπi (E.symm.injective h), E.symm.surjective.comp hπ.1,
    B5.realizesVia_of_autSec bot_le hZW hZU hfaith hπ,
    eq_map_of_autSec_eq_map le_sup_left hZW hZU hfaith π' _ hψ _ hLeq, i, j, hij, ?_⟩
  exact eq_map_of_autSec_eq_map le_sup_right hZW hZU hfaith π' _ hψ _ hAeq

end B69K

end CFSG.Quasithin
