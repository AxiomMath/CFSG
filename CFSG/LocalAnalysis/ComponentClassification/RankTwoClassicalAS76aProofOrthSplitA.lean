module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

theorem splitAt_of_typeA {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [Finite K] [CharP K 2] (Q : QuadraticForm K (ι → K))
    (q : (ι → K) → K) (hq : ⇑Q = q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} {ℓ : ℕ} (hℓ : 4 ≤ ℓ)
    (hp : HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) p .a ℓ) :
    SplitAt A (alphaGroup e p) (Nat.card K)
      (fun x => HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a 2)
      (fun x => HasSuzukiType e (fun M v => q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a (ℓ - 2)) := by
  subst hq
  obtain ⟨-, M, hpM, hM2, hr, hev, hsing⟩ := hp
  have hN := sub_one_mul_self_eq_zero hM2
  have hiso : ∀ v, Q (v + ((M : Matrix ι ι K) - 1) *ᵥ v) = Q v := fun v => by
    rw [sub_mulVec, one_mulVec, add_sub_cancel]
    exact statedOmega_isometry hpM.2.1 v
  have hrank : ((M : Matrix ι ι K) - 1).rank = ℓ := hr
  have hN0 : (M : Matrix ι ι K) - 1 ≠ 0 := by
    intro h
    rw [h, Matrix.rank_zero] at hrank
    omega
  obtain ⟨E₁, E₂, hsum, h11, h12, h21, h22, hQE₁, hQE₂, hBE₁, hBE₂, hr1, hr2, hv, hDc⟩ :=
    exists_orth_split Q hQ _ hN hN0 hiso hsing
  rw [hrank] at hr2
  have hE₁ : E₁ ≠ 0 := by
    rintro rfl
    rw [Matrix.rank_zero] at hr1
    omega
  have hE₂ : E₂ ≠ 0 := by
    rintro rfl
    rw [Matrix.rank_zero] at hr2
    omega
  have hev2 : Even (ℓ - 2) := by
    obtain ⟨j, hj⟩ := hev
    exact ⟨j - 1, by omega⟩
  have hQunip : ∀ {E : Matrix ι ι K} (hE : E * E = 0), (∀ v, Q (E *ᵥ v) = 0) →
      (∀ v, Q.polarBilin v (E *ᵥ v) = 0) → ∀ (a : K) v,
        Q ((unipGL E hE a : Matrix ι ι K) *ᵥ v) = Q v := by
    intro E hE hQE hBE a v
    rw [coe_unipGL, add_mulVec, one_mulVec, smul_mulVec, quad_add, QuadraticMap.map_smul, hQE,
      smul_zero, add_zero, map_smul, smul_eq_mul, hBE, mul_zero, add_zero]
  have hunip : ∀ {E : Matrix ι ι K} (hE : E * E = 0), (∀ v, Q (E *ᵥ v) = 0) →
      (∀ v, Q.polarBilin v (E *ᵥ v) = 0) → Even E.rank → ∀ a : K,
        unipGL E hE a ∈ StatedOmega ⇑Q := by
    intro E hE hQE hBE hevE a
    by_cases ha : a = 0
    · rw [ha, unipGL_zero]
      exact one_mem _
    · refine mem_statedOmega_of Q hQ hT (hQunip hE hQE hBE a) ?_
      rw [commRank_unipGL hE ha]
      exact hevE
  have hsingE : ∀ {E : Matrix ι ι K} (hE : E * E = 0), (∀ v, Q (E *ᵥ v) = 0) → ∀ (a : K) v,
      Q (((unipGL E hE a : Matrix ι ι K) - 1) *ᵥ v) = 0 := by
    intro E hE hQE a v
    rw [coe_unipGL, add_sub_cancel_left, smul_mulVec, QuadraticMap.map_smul, hQE, smul_zero]
  have hsplit := splitAt_of_matrices_of (e := e) hZ (RingHom.id K) hpM hM2 hsum h11 h12 h21 h22
    hv hE₂ (hunip h11 hQE₁ hBE₁ (by rw [hr1]; exact even_two))
    (hunip h22 hQE₂ hBE₂ (by rw [hr2]; exact hev2)) (fun _ _ a _ => ⟨a, rfl⟩)
    (fun c hc => by
      obtain ⟨D, hDQ, hDev, hD1, hD2⟩ := hDc c hc
      exact ⟨D, mem_statedOmega_of Q hQ hT hDQ hDev, hD1, hD2⟩)
    (fun x => HasSuzukiType e (fun M v => Q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a 2)
    (fun x => HasSuzukiType e (fun M v => Q (((M : Matrix ι ι K) - 1) *ᵥ v)) x .a (ℓ - 2))
    (fun a ha x hx2 hx => ⟨hx2, unipGL E₁ h11 a, hx, orderOf_unipGL h11 ha hE₁,
      by rw [commRank_unipGL h11 ha, hr1], even_two, hsingE h11 hQE₁ a⟩)
    (fun a ha x hx2 hx => ⟨hx2, unipGL E₂ h22 a, hx, orderOf_unipGL h22 ha hE₂,
      by rw [commRank_unipGL h22 ha, hr2], hev2, hsingE h22 hQE₂ a⟩)
  exact hsplit

theorem orthPlusSplitA :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
      D.family = .orthPlus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
        ∀ (p : G) (ℓ : ℕ), 4 ≤ ℓ → D.SuzukiType p .a ℓ →
          SplitAt A (D.alpha p) D.q (fun x => D.SuzukiType x .a 2) fun x => D.SuzukiType x .a (ℓ - 2) := by
  intro G _ _ A D hD _ hZ _ p ℓ hℓ hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    have hsplit := splitAt_of_typeA (CFSG.LieType.Universal.Spin.quadPlus n K)
      (StatedQuadPlus n K) (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K)
      (exists_totallySingular_quadPlus (by omega) K) hZ hℓ hp
    rw [hK] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem orthMinusSplitA :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
      D.family = .orthMinus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
        ∀ (p : G) (ℓ : ℕ), 4 ≤ ℓ → D.SuzukiType p .a ℓ →
          SplitAt A (D.alpha p) D.q (fun x => D.SuzukiType x .a 2) fun x => D.SuzukiType x .a (ℓ - 2) := by
  intro G _ _ A D hD _ hZ _ p ℓ hℓ hp
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    have hsplit := splitAt_of_typeA (CFSG.LieType.Universal.Spin.quadMinus n K b c)
      (StatedQuadMinus n K b c) (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c) hZ hℓ hp
    rw [hK] at hsplit
    exact hsplit
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

theorem classicalSplit_of (hPC : OrthPlusSplitC) (hMC : OrthMinusSplitC)
    (hPC2 : OrthPlusSplitCTwo) (hMC2 : OrthMinusSplitCTwo) : ClassicalSplit :=
  ⟨hPC, hMC, hPC2, hMC2⟩

end CFSG.ComponentClassification.RankTwoClassical
