module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2Two

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.CGT.PushingUpLit.CGT6.EmbModule

theorem h1NaturalSL2_holds : H1NaturalSL2 := by
  intro n hn V _ _ hV G hind hnat
  obtain ⟨S⟩ := NatSec.exists_of_isNatSectionBy hnat
  have hn1 : 1 < n := hn
  have hG : Finite ↥G := Finite.of_equiv _ S.θ.toEquiv.symm
  let ρ : Representation (ZMod 2) ↥G (Fin 2 → GaloisField 2 n) :=
    (natRep (GaloisField 2 n)).comp S.θ.toMonoidHom
  have hρ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n),
      ρ g w = (S.θ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w := fun g w => rfl
  have hH : Nat.card (H1 ρ) = 2 ^ n := by
    have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 2 n (by omega)]
    refine card_H1_eq_of_card ρ (θ := S.θ) (β := AddEquiv.refl _) (μ := mu2)
      (fun γ w => rfl) ?_
    rw [card_Z1A_mu2 hF hn1, hF]
  obtain ⟨Φ, hΦ0⟩ := natRep_dual_equiv (GaloisField 2 n)
  have hΦ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n), Φ (ρ g w) = ρ.dual g (Φ w) := by
    intro g w
    have h1 : ρ.dual g (Φ w) = (natRep (GaloisField 2 n)).dual (S.θ g) (Φ w) := by
      apply LinearMap.ext
      intro w'
      simp [Representation.dual_apply, ρ, map_inv]
    rw [h1]
    exact hΦ0 (S.θ g) w
  have hU : ∀ u : ↥(commV G), u ^ 2 = 1 := fun u => Subtype.ext (hV u)
  have hN : ∀ x : Multiplicative (Fin 2 → GaloisField 2 n), x ^ 2 = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    funext i
    have h2 : (2 : GaloisField 2 n) = 0 := CharTwo.two_eq_zero
    simp [toAdd_pow, h2]
  obtain ⟨s, hs⟩ := exists_hom_section hU hN S.β S.surj
  exact ⟨S.claim1 hn hV hind ρ hρ hH.le, S.claim2 ρ hρ s hs Φ hΦ hn hV hH.le⟩

end CFSG.CGT.PushingUpLit.CGT6
