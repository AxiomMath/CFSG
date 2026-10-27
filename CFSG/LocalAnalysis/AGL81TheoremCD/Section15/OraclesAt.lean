module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1217Sigma
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def O812sixAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ q ∈ sigmaM G M, 5 ≤ q →
    ∀ F : Subgroup G, F ≤ M → IsPGroup 3 F → F ≠ ⊥ → Group.IsSolvable (MulAut ↥F) →
      2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.centralizer (F : Set G)) →
      ¬ CFSG.HallHigman.IsPSolvable q ↥(M ⊓ Subgroup.centralizer (F : Set G)) →
      Subgroup.normalizer (F : Set G) ≤ M

@[expose] def O1517bAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ p ∈ sigmaM G M,
    ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M → rankThreeGamma 2 3 R ≤ M →
      ∀ A : Subgroup G, A ≤ M → Nat.card A = 3 →
        p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G)) →
        ∀ P : Subgroup G,
          CFSG.ABGLocalTools.IsSylowOf 3 P (M ⊓ Subgroup.normalizer (A : Set G)) →
          (((IsElemAbelian 3 P ∧ Nat.card P = 27) ∨ IsCyclic ↥(Subgroup.center ↥P)) ∧
            3 ≤ CFSG.Open.pRank 3 P) →
          Subgroup.normalizer (A : Set G) ≤ M

@[expose] def O1521At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  3 ∉ sigmaM G M →
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 → rankThreeGamma 1 3 E ≤ M →
      ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → E ≤ H → H ≠ M →
        ∃ A T R H' : Subgroup G, L34Config M A T R H'

@[expose] def O1521bAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  3 ∉ sigmaM G M →
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 → rankThreeGamma 1 3 E ≤ M →
      ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → E ≤ H → H ≠ M →
        ∀ q ∈ sigmaM G M, ¬ q ∣ Nat.card ↥(H ⊓ M)

@[expose] def O1219SigmaAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ q p : ℕ, q ∈ sigmaM G M → p.Prime → p ≠ 2 → p ∉ sigmaM G M →
    ∀ D : Subgroup G, D ≤ M → ¬ IsCyclic ↥D → (∀ x ∈ D, x ^ p = 1) →
      ⁅⁅D, D⁆, D⁆ = ⊥ →
      CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (D : Set G)) = CFSG.Open.pRank q M →
      ∃ E : Subgroup G, E ≤ D ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        rankThreeGamma 1 p E ≤ M

@[expose] def O1211At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q → q ∉ sigmaM G M →
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian q E → Nat.card E = q ^ 2 →
      rankThreeGamma 1 q E ≤ M →
      ∀ H : Subgroup G, IsTwoLocal H → E ≤ H → H ≤ M

theorem O812sixAt.of_ctx2 (h : O812six) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O812sixAt G M := by
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong

theorem O1517bAt.of_ctx2 (h : O1517b) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O1517bAt G M := by
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong

theorem O1521At.of_ctx2 (h : O1521) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O1521At G M := by
  intro h3
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong h3

theorem O1521bAt.of_ctx2 (h : O1521b) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O1521bAt G M := by
  intro h3
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong h3

theorem O1219SigmaAt.of_ctx2 (h : O1219Sigma) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O1219SigmaAt G M := by
  intro q p hq hp hp2 hpσ D hDM hDnc hDexp hDcl hrank
  obtain ⟨p0, hp0⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p0, hp0, ctx.witness p0 hp0⟩ ctx.strong
    q p hq hp hp2 hpσ D hDM hDnc hDexp hDcl hrank

theorem O1211At.of_ctx2 (h : O1211) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O1211At G M := by
  intro q hq hq5 hqσ E hEM hE hEc hΓ H hH2 hEH
  obtain ⟨p0, hp0⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p0, hp0, ctx.witness p0 hp0⟩ ctx.strong
    q hq hq5 hqσ E hEM hE hEc hΓ H hH2 hEH

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
