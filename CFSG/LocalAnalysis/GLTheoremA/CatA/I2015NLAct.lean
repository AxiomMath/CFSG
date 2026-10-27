module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
  CFSG.LocalAnalysis.GLTheoremA.FR CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.LocalAnalysis.GLTheoremA.S10

theorem fixed_of_action {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {H : Type} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) (hZ : Odd (Nat.card Z)) (ρ : (K ≃+* K) →* MulAut H)
    (good : (K ≃+* K) → Prop) (hgood : ∀ σ, good σ → ∀ n : ℕ, good (σ ^ n)) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hH : twoPart (Nat.card H) ^ v = 2 ^ (m * u))
    (hC : ∀ σ, good σ → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (fixNum (ρ σ)) ^ v = 2 ^ (e * u))
    {p : ℕ} (hp : p.Prime) (hred : ∀ σ : K ≃+* K, ∃ n : ℕ, ¬ p ∣ n ∧ good (σ ^ n))
    (f : MulAut (H ⧸ Z)) (σ : K ≃+* K)
    (hσf : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ σ x)) (hord : orderOf f = p) :
    ∃ σ₀ : K ≃+* K, orderOf σ₀ = p ∧ good σ₀ ∧ p ∣ m ∧
      Nat.card {x : K // σ₀ x = x} = 2 ^ (m / p) ∧
      ∀ x : H, ρ σ₀ x = x → f (QuotientGroup.mk x) = QuotientGroup.mk x := by
  obtain ⟨n, hn, hσ₀, hgn, hσn⟩ := sigma_order hm hK Z hZc hZ ρ good hgood hu hv hH hC hp hred f σ
    hσf hord
  refine ⟨σ ^ n, hσ₀, hgn, ?_⟩
  obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field hm hK (σ ^ n)
  rw [hσ₀] at hdvd hcard
  refine ⟨hdvd, hcard, fun x hx => ?_⟩
  have hfeq := fixSub_pow_eq hp hord hn
  have h1 : (f ^ n) (QuotientGroup.mk x) = QuotientGroup.mk x := by
    rw [hσn x, hx]
  have h2 : (QuotientGroup.mk x : H ⧸ Z) ∈ FP.fixSub (f ^ n) := FP.mem_fixSub.2 h1
  rw [hfeq] at h2
  exact FP.mem_fixSub.1 h2

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
