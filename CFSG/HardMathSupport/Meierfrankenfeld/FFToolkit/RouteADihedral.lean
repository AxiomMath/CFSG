module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteA

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Cooperstein.Coordinator

theorem noIrrFFOffender_of_route_A_dihedral {Y : Type} [Group Y] [Finite Y]
    (hcent : Subgroup.center Y = ⊥) (hcard2 : Nat.card (MulAut Y) ≤ 2 * Nat.card Y)
    {r ρ p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hrρ : r + 1 < ρ)
    (hρ : 2 * ρ < orderOf (2 : ZMod p) + 2)
    (hr : ∀ B : Subgroup Y, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hgen : ∀ t : Y, t * t = 1 → t ≠ 1 → ∃ c : Y, orderOf (t * (c * t * c⁻¹)) = p)
    (houter : ∀ ψ : MulAut Y, ψ ∉ (MulAut.conj : Y →* MulAut Y).range → ψ * ψ = 1 →
      ∃ (p' : ℕ) (_ : Fact p'.Prime) (x : Y), p' ≠ 2 ∧ 3 ≤ orderOf (2 : ZMod p') ∧
        orderOf x = p' ∧ ψ x = x⁻¹) :
    NoIrrFFOffender Y := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  exact weight_lt_of_route_A hW hq hirr e hcent hcard2 hEN hE hel hrρ hr
    (rank_of_dihedral hW hirr e hp2 hρ hgen) houter

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
