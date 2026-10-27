module



public import CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
import all CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
public import CFSG.LocalAnalysis.RankThreeUC.Section11.SigmaQuotientRank

public section


namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.IrreducibleRankCentralization


open Subgroup CFSG.LocalAnalysis.RankThreeUC


variable {G : Type} [Group G] [Finite G]


theorem centralizes_base {M T V₀ V : Subgroup G} (h : Section11.Setting G M T V₀ V)
    {p : ℕ} (hp : p ∈ SourceSetting.sigmaOf G M) {X K : Subgroup G} (hXp : IsPGroup p X) (hXM : X ≤ M)
    (hrank : 1 < CFSG.Open.pRank p X) (hirr : Section6.IsIrreducibleUnder K X)
    (hKM : K ≤ M) (hKX : K ≤ normalizer (X : Set G)) :
    X ≤ centralizer (V₀ : Set G) := by
  have hV₀ : M ≤ normalizer (V₀ : Set G) := by
    rcases h.moduleChoice with hm | ⟨-, h0⟩
    · exact (mem_normalElemAbelian2.mp hm.1).2.2.2
    · subst h0
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
  have hnorm : K ≤ normalizer ((X ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G) := by
    have key : ∀ k ∈ K, ∀ x ∈ X ⊓ centralizer (V₀ : Set G),
        k * x * k⁻¹ ∈ X ⊓ centralizer (V₀ : Set G) := by
      intro k hk x hx
      obtain ⟨hxX, hxC⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hKX hk) x).mp hxX, ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      have h1 : k⁻¹ * y * k ∈ V₀ := by
        have := (mem_normalizer_iff.mp (inv_mem (hV₀ (hKM hk))) y).mp hy
        simpa using this
      have h2 := mem_centralizer_iff.mp hxC _ h1
      have : y * (k * x * k⁻¹) = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by group
      rw [this, h2]; group
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key k hk x, fun hx => ?_⟩
    have := key k⁻¹ (inv_mem hk) _ hx
    simpa [mul_assoc] using this
  rcases (show _ ∧ _ from hirr).2 _ inf_le_left hnorm with hb | hX
  · exfalso
    obtain ⟨hN, hr⟩ := Section11.SigmaQuotientRank.sigma_quotient_rank h hp hXp hXM
    have hp' := (Section12.NonTISigmaPrimeRank.sigma_prime_rank hp).1
    have key : ∀ (N : Subgroup X) (hN : N.Normal), N = ⊥ →
        CFSG.Assembly.pRank p (⊤ : Subgroup (↥X ⧸ N)) ≤ 1 → False := by
      rintro N hN rfl hr
      have e := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp'.one_lt
        (QuotientGroup.quotientBot (G := X))
      have h2 : CFSG.Open.pRank p X ≤ 1 := by
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X, ← e]
        exact hr
      omega
    exact key _ hN (by rw [hb]; simp) hr
  · rw [← hX]; exact inf_le_right


end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.IrreducibleRankCentralization
