module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteB
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Cooperstein.Coordinator

theorem noIrrFFOffender_of_heisCfg {Y : Type} [Group Y] {k c p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (hOut : ∀ B : Subgroup (MulAut Y), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ k * Nat.card ↥(B ⊓ (MulAut.conj : Y →* MulAut Y).range))
    (hZ : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty (L ⧸ Subgroup.center L ≃* Y) → Odd (Nat.card (Subgroup.center L)) →
        ¬ p ∣ Nat.card (Subgroup.center L) ∧ Nat.card (Subgroup.center L) ≤ c)
    {x y : Fin n → Y} {z : Y} (h : HeisCfg p n x y z) (hy : ∀ i, y i ^ p = 1)
    (hlt : k * (c * Nat.card Y) < 2 ^ (p ^ n * orderOf (2 : ZMod p))) :
    NoIrrFFOffender Y := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨hZp, hZc⟩ := hZ ↥L hq ⟨e⟩ (odd_card_center_of_isIrrOn hW hirr)
  refine exclusion_of_heisCfg_of_outer hW hq hirr hEN hE hel e hOut hp2 hZp h hy
    (lt_of_le_of_lt ?_ hlt)
  exact Nat.mul_le_mul_left k (Nat.mul_le_mul_right _ hZc)

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
