module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankFourTheoremC

theorem three_le_pRank_of_lift {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal] {x : Y} {S₀ P : Type} [Group S₀] [Group P]
    [Group.IsPerfect S₀] (π : S₀ →* P) (e : ↥L ⧸ center ↥L ≃* P) (φ : S₀ →* ↥L)
    (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s) (Ã : S₀ →* S₀)
    (hÃ : ∀ s, π (Ã s) = l212in_descend e (odC L x) (π s))
    (f : (Fin 3 → Multiplicative (ZMod p)) →* S₀) (hfi : Function.Injective (π.comp f))
    (hfix : ∀ a, Ã (f a) = f a) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set Y)) := by
  have hlift : ∀ s, odC L x (φ s) = φ (Ã s) := fun s =>
    l212in_alpha_phi e π φ hφπ (odC L x) Ã hÃ s
  have hinj : Function.Injective (φ.comp f) := by
    intro a b hab
    apply hfi
    change π (f a) = π (f b)
    rw [← hφπ, ← hφπ]
    exact congrArg (fun l : ↥L => e (QuotientGroup.mk l)) hab
  exact od_three_le_pRank_of_torus (L := L) (x := x) (φ.comp f) hinj (fun a => by
    change odC L x (φ (f a)) = φ (f a)
    rw [hlift, hfix])

theorem fixed_of_pow_eq_one {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    {σ : K ≃+* K} (hσ : σ ^ p = 1) {u : Kˣ} (hu : u ^ p = 1) : σ (u : K) = u :=
  CFSG.StandardType.TableBUF.ringEquiv_apply_eq_of_pow_eq_one hp hσ
    (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
