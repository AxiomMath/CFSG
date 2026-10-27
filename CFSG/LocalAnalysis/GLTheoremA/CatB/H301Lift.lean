module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift8
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

variable {G : Type} [Group G] [Finite G]

theorem sporCfg_of_row (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    {p : ℕ} {row : Row} (hrowS : I301ARow row) (hc : row.center = 1)
    {x : G} {L : Subgroup G} (hx1 : x ≠ 1) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x))))
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    (hrk : GLATwoLocalRank p G ≤ row.rank) : Nonempty (SporCfg G p x L row) := by
  obtain ⟨c⟩ := nonempty_sporCfgCore hrowS hc hx1 hx hL hrow hodd hrk1 hrk
  exact ⟨{
    Bs := c.Bs
    R := c.R
    D := c.D
    hBs := c.hBs
    hBsCard := c.hBsCard
    hRL := c.hRL
    hR := c.hR
    hBsN := c.hBsN
    hRN := c.hRN
    hD := c.hD
    hData := c.hData
    hMax := c.hMax
    hR0 := c.hR0
    hK6 := c.hK6_layer hOut hc hx hL hrow hrk1
    hNL := c.hNL }⟩

@[expose] def I301ACoverAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (x : G) (L : Subgroup G) (row : Row), row.center = 3 → x ≠ 1 → orderOf x = p →
    GLAPComponent p (cx x) L → CFSG.Open.IsKGroup ↥(cx x) → RowL row p L →
    Odd (Nat.card (GLAPPrimeCoreOf p (cx x))) →
    (∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p) →
    GLATwoLocalRank p G ≤ row.rank → Nonempty (SporCfg G p x L row)

theorem i301AAt_of_rows (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    {p : ℕ} (hrows : ∀ row : Row, I301ARow row) (hcov : I301ACoverAt G p) :
    I301AAt G p := by
  intro x L row hx1 hx hL hKG hrow hodd hrk1 hrk
  have hc : row.center = 1 ∨ row.center = 3 := by cases row <;> simp [Row.center]
  rcases hc with hc | hc
  · exact sporCfg_of_row hOut (hrows row) hc hx1 hx hL hrow hodd hrk1 hrk
  · exact hcov x L row hc hx1 hx hL hKG hrow hodd hrk1 hrk

end CFSG.LocalAnalysis.GLTheoremA.H301
