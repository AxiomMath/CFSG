module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXWInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DXW

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem t263SelWP_of_innerRank {Q : ℕ → TauCeti.CFSGIndex → Prop}
    (hin : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω),
      S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (↥S ⧸ Subgroup.center ↥S) (Q p) → ∀ b : Ω, b ^ p = 1 →
      InnDiagOn p (Subgroup.zpowers b) S → InducesInnerMod p S b)
    (hrank : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X], catalogIs X (Q p) →
      ∀ E U : Subgroup X, IsElemAbelian p E → IsPGroup 2 ↥U → U ≠ ⊥ →
        E ≤ Subgroup.normalizer (U : Set X) → Nat.card ↥E ≤ p) :
    DX.T263SelWP Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T'
    hT'ne hT'2 hT'S hBT' hker x hxB₀ hxC hxcomm
  classical
  exfalso
  have hBel : CFSG.Open.IsElemAbelian p B := hB.1
  have hB₀el : CFSG.Open.IsElemAbelian p B₀ := isElemAbelian_mono hBel hB₀.1
  have hin₀ : ∀ b ∈ B₀, InducesInnerMod p S b := fun b hb =>
    hin p hp hp2 Ω S hSn hSq hSp hQ b (hBel.2 b (hB₀.1 hb))
      (S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hb))
  have hEq : B₀ ⊓ Subgroup.centralizer (S : Set Ω) = B ⊓ Subgroup.centralizer (S : Set Ω) :=
    le_antisymm (inf_le_inf_right _ hB₀.1) (le_inf hB₀.2.2.2.2 inf_le_right)
  have hcard₀ : p * Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀ := by
    rw [hEq]; exact hcase
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  have hnab : ∃ x y : ↥S ⧸ Subgroup.center ↥S, x * y ≠ y * x :=
    CFSG.StandardType.exists_mul_ne_mul_centerQuot_of_perfect hSq.1 inferInstance
  have hZ : Subgroup.center (↥S ⧸ Subgroup.center ↥S) = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_isSimpleGroup_of_nonabelian hnab
  exact t263_false_of_inner_rank hp hp2 hSn hSq hSp hB₀el hin₀ hcard₀ hT'S hT'2 hT'ne
    (hB₀.1.trans hBT') (MulEquiv.refl _) hZ (hrank p hp hp2 (↥S ⧸ Subgroup.center ↥S) hQ)

end CFSG.LocalAnalysis.GLTheoremA.T263.DXW
