module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyGHCent

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

namespace SAFyGH

abbrev W5 : Type := RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))

theorem card_W5 : Nat.card W5 = 28800 := by
  rw [Nat.card_congr (RegularWreathProduct.equivProd (Equiv.Perm (Fin 5))
    (Multiplicative (ZMod 2))), Nat.card_prod, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]
  rw [Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem card_W8 : Nat.card W8 = 128 := by
  rw [Nat.card_congr (RegularWreathProduct.equivProd D8 (Multiplicative (ZMod 2))),
    Nat.card_prod, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]
  rw [DihedralGroup.card]
  norm_num

variable {X : Type} [Group X] [Finite X]

theorem le_card_of_layer (E : Subgroup X) (ψ : E ≃* A5 × A5) (P : Sylow 2 X)
    (ι : ↥(P : Subgroup X) ≃* W8) : 28800 ≤ Nat.card X := by
  have h128 : 128 ∣ Nat.card X := by
    have := Subgroup.card_subgroup_dvd_card (P : Subgroup X)
    rwa [Nat.card_congr ι.toEquiv, card_W8] at this
  have h3600 : 3600 ∣ Nat.card X := by
    have := Subgroup.card_subgroup_dvd_card E
    rwa [Nat.card_congr ψ.toEquiv, card_A5A5] at this
  have h225 : 225 ∣ Nat.card X := (Dvd.intro_left 16 rfl : 225 ∣ 3600).trans h3600
  have h : 128 * 225 ∣ Nat.card X := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h128 h225
  exact Nat.le_of_dvd Nat.card_pos h

theorem equiv_wreath_of_layer (hO : CFSG.pPrimeCore 2 X = ⊥) (E : Subgroup X) [E.Normal]
    (ψ : E ≃* A5 × A5) (P : Sylow 2 X) (ι : ↥(P : Subgroup X) ≃* W8)
    (hAut : MulAut (A5 × A5) ≃* W5) : Nonempty (X ≃* W5) := by
  have hC := centralizer_layer_eq_bot hO E ψ P ι
  let Θ : X →* W5 := (hAut.toMonoidHom).comp ((MulAut.congr ψ).toMonoidHom.comp
    (MulAut.conjNormal (H := E)))
  have hΘ : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : MulAut.conjNormal (H := E) x = 1 := by
      have : (MulAut.congr ψ) (MulAut.conjNormal (H := E) x) = 1 :=
        hAut.injective (by simpa [Θ] using hx)
      exact (MulAut.congr ψ).injective (this.trans (map_one _).symm)
    have hxc : x ∈ centralizer (E : Set X) := by
      rw [mem_centralizer_iff]
      intro e he
      have := congrArg (fun α : MulAut E => ((α ⟨e, he⟩ : E) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc e * x = (x * e * x⁻¹) * x := by rw [this]
        _ = x * e := by group
    rw [hC] at hxc
    exact mem_bot.1 hxc
  have hbij : Function.Bijective Θ :=
    hΘ.bijective_of_nat_card_le (by rw [card_W5]; exact le_card_of_layer E ψ P ι)
  exact ⟨MulEquiv.ofBijective Θ hbij⟩

end SAFyGH

end CFSG.EvenSporadicStandard.TwoHS
