module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesAt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineOne
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1218
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def O1217At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ q p : ℕ, q ∈ sigmaM G M → 5 ≤ q → p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
      q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G)) →
      (∀ A : Subgroup G, A ≤ E → Nat.card A = p →
        2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G))) →
      rankThreeGamma 1 p E ≤ M

@[expose] def O1218At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ q p : ℕ, q ∈ sigmaM G M → p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
      rankThreeGamma 1 p E ≤ M →
      ∀ H : Subgroup G, E ≤ H → q ∣ Nat.card ↥(H ⊓ M) → pCoreOf 2 H ≠ ⊥ → H ≤ M

@[expose] def O991At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  3 ∉ sigmaM G M →
  ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 → rankThreeGamma 1 3 E ≤ M →
    E ∈ uniqueSet M

@[expose] def O89At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ H : Subgroup G, IsTwoLocal H → CFSG.Open.pRank 3 H ≤ 3 →
    ∀ L : Subgroup G, L ≤ H ⊓ M → CFSG.IsPComponent 3 (L.subgroupOf (H ⊓ M)) →
      CFSG.Open.pRank 3 L = 1 → IsLThreeTwoPow (↥L ⧸ CFSG.pCore 2 ↥L) →
      ∀ A : Subgroup G, A ≤ L → Nat.card A = 3 → A ∈ uniqueSet M →
        (∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≤
            Subgroup.normalizer (A : Set G) ⊓ (H ⊓ M) →
          A.map (MulAut.conj h).toMonoidHom = A) →
        ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ M ∧
          Subgroup.normalizer (S : Set G) ⊓ H ≤ M

@[expose] def P812At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.RankThree.PartOne.IsStronglyPEmbedded p M →
    2 < CFSG.Open.pRank p M →
    ∀ L₁ L₂ : Subgroup G, L₁ ≤ M → L₂ ≤ M → L₁ ≠ L₂ →
      CFSG.IsPComponent p (L₁.subgroupOf M) → CFSG.IsPComponent p (L₂.subgroupOf M) →
      (L₁.subgroupOf M).Normal → CFSG.Open.pRank 3 M ≤ 3 →
      CFSG.Open.pRank p L₁ = 1 → CFSG.Open.pRank 3 L₁ = 1 →
      CFSG.Open.pRank p L₂ = 1 → CFSG.Open.pRank 3 L₂ = 1 →
      (∀ B : Subgroup G, B ≤ M → Nat.card B = 3 →
        2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (B : Set G)) →
        ¬ CFSG.HallHigman.IsPSolvable p ↥(M ⊓ Subgroup.centralizer (B : Set G)) →
        Subgroup.normalizer (B : Set G) ≤ M) →
      ∀ A : Subgroup G, Nat.card A = 3 → (A ≤ L₁ ∨ A ≤ L₂) → A ∈ uniqueSet M

@[expose] def O98At (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  3 ∉ sigmaM G M →
  ∀ Q : Subgroup G, Q ≤ M → IsPGroup 3 Q → ¬ IsCyclic ↥Q → rankThreeGamma 1 3 Q ≤ M →
    ∀ x : G, x ∈ M → orderOf x = 3 → (∀ y ∈ Q, x * y = y * x) →
      ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
      pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ →
      pCoreOf 2 (Subgroup.centralizer ({x} : Set G) ⊓ M) ≠ ⊥ →
        ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({x} : Set G) ∧
          CFSG.IsPComponent 3 (K.subgroupOf (Subgroup.centralizer ({x} : Set G))) ∧
          ¬ K ≤ M ∧ ThreeFourShape K M ∧
          (∀ y ∈ Subgroup.centralizer ({x} : Set G) ⊓ M, orderOf y = 7 →
            y ∈ Subgroup.normalizer (K : Set G))

theorem O1217At.of_ctx2 (h : O1217) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O1217At G M := by
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong

theorem O1218At.of_ctx2 (h : O1218) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O1218At G M := by
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong

theorem O991At.of_ctx2 (h : O991) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O991At G M := by
  intro h3
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong h3

theorem P812At.of_ctx2 (h : P812) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : P812At G M := by
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong

theorem O98At.of_ctx2 (h : O98) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O98At G M := by
  intro h3
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong h3

@[expose] def O812sixGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O812sixAt G M

@[expose] def O1517bGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O1517bAt G M

@[expose] def O1521Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O1521At G M

@[expose] def O1521bGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O1521bAt G M

@[expose] def O1219SigmaGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O1219SigmaAt G M

@[expose] def O1217Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O1217At G M

@[expose] def O89Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O89At G M

@[expose] def P812Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      P812At G M

@[expose] def O98Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O98At G M

theorem O812sixAt.of_gen (h : O812sixGen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : O812sixAt G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O1517bAt.of_gen (h : O1517bGen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : O1517bAt G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O1521At.of_gen (h : O1521Gen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : O1521At G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O1521bAt.of_gen (h : O1521bGen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : O1521bAt G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O1219SigmaAt.of_gen (h : O1219SigmaGen) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) :
    O1219SigmaAt G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O1217At.of_gen (h : O1217Gen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : O1217At G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O89At.of_gen (h : O89Gen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : O89At G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem P812At.of_gen (h : P812Gen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : P812At G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O98At.of_gen (h : O98Gen) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) : O98At G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem ctx.strong

theorem O991At.of_gen (h : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen) {G : Type} [Group G]
    [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) :
    O991At G M :=
  h G ctx.cstar M ctx.maxLocal ctx.p_mem

theorem o812six_of_gen (h : O812sixGen) : O812six := by
  intro G _ _ hS hUC M hM hwit hstrong
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (RankThree.cStarGen_of_rankThreeUC hS hUC) M hM ⟨p, hp⟩ hstrong

theorem o1517b_of_gen (h : O1517bGen) : O1517b := by
  intro G _ _ hS hUC M hM hwit hstrong
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (RankThree.cStarGen_of_rankThreeUC hS hUC) M hM ⟨p, hp⟩ hstrong

theorem o1521_of_gen (h : O1521Gen) : O1521 := by
  intro G _ _ hS hUC M hM hwit hstrong
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (RankThree.cStarGen_of_rankThreeUC hS hUC) M hM ⟨p, hp⟩ hstrong

theorem o1521b_of_gen (h : O1521bGen) : O1521b := by
  intro G _ _ hS hUC M hM hwit hstrong
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (RankThree.cStarGen_of_rankThreeUC hS hUC) M hM ⟨p, hp⟩ hstrong

theorem p812_of_gen (h : P812Gen) : P812 := by
  intro G _ _ hS hUC M hM hwit hstrong
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (RankThree.cStarGen_of_rankThreeUC hS hUC) M hM ⟨p, hp⟩ hstrong

theorem o98_of_gen (h : O98Gen) : O98 := by
  intro G _ _ hS hUC M hM hwit hstrong
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (RankThree.cStarGen_of_rankThreeUC hS hUC) M hM ⟨p, hp⟩ hstrong

theorem O1218At.of_at {G : Type} [Group G] [Finite G] (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (h1211 : O1211At G M)
    (h1521b : O1521bAt G M) : O1218At G M := by
  intro q p hq hp hp2 E hEM hE hEc hΓ H hEH hqH hO2
  obtain ⟨hN2, hHN⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.O1218Proof.isTwoLocal_normalizer_pCoreOf hO2
  have hEH0 : E ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hEH.trans hHN
  by_cases hpσ : p ∈ sigmaM G M
  · have hpp : p.Prime := hp
    have hEp : IsPGroup p E :=
      CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hE
    have hk : 2 ≤ CFSG.Open.pRank p E :=
      CFSG.SectionRank.le_pRank hpp.one_lt (le_refl E) hE hEc
    exact hHN.trans (hC.embed p hpσ.1 M hM E hEM hEp hk _ hN2 hEH0)
  · by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨H1, hH1, hH0H1⟩ :=
        CFSG.LocalAnalysis.RankThreeUC.S15.O1218Proof.exists_maxTwoLocal_ge hN2
      by_cases hH1M : H1 = M
      · exact hHN.trans (hH0H1.trans hH1M.le)
      · exfalso
        have hHH1 : H ≤ H1 := hHN.trans hH0H1
        have h9 : Nat.card E = 9 := by rw [hEc]; norm_num
        exact h1521b hpσ E hEM hE h9 hΓ H1 hH1 (hEH.trans hHH1) hH1M q hq
          (dvd_trans hqH (Subgroup.card_dvd_of_le (inf_le_inf_right M hHH1)))
    · have h5 : 5 ≤ p := by
        by_contra hlt
        have h2le := hp.two_le
        have h234 : p = 2 ∨ p = 3 ∨ p = 4 := by omega
        rcases h234 with h | h | h
        · exact hp2 h
        · exact hp3 h
        · rw [h] at hp
          exact absurd hp (by norm_num)
      exact hHN.trans (h1211 p hp h5 hpσ E hEM hE hEc hΓ _ hN2 hEH0)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
