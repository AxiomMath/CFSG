module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Pair
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

section Reduced

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

namespace D2AlmostSimple

theorem le_A_of_isPGroup_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) {W : Subgroup X} (hWY₀ : W ≤ X₀)
    (hY₀W : X₀ ≤ Subgroup.normalizer (W : Set X)) (hWp : IsPGroup p W) : W ≤ A := by
  have hKn := h.normal
  have hp2 := h.ne_two
  have h2 : (2 : GaloisField p 2) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p 2) p]; exact hp2)
  obtain ⟨hU, -⟩ := h.sylow_inf_eq_of_psl2 e
  have hCU := h.centralizer_A_le_of_psl2 e
  have hNA := h.normalizer_A_eq_of_psl2 e
  have hY₀U : X₀ ≤ Subgroup.normalizer (A : Set X) := hNA.ge
  obtain ⟨ψ, hψinj, hψU, hψc⟩ :=
    exists_torus_param_of_mulEquiv_psl2GF hp2 (by norm_num) e A (h.A_le_of_psl2 e) h.card_A
  have hY₀K : X₀ ⊓ K ≤ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) := by
    rw [hU]
    exact inf_le_left.trans hY₀U
  intro w hw
  have hWK : W ⊓ K ≤ A := hU ▸ le_sylow_inf_of_le_normalizer K R hWp.to_inf_left inf_le_right
    (fun x hx => hY₀K ⟨hWY₀ hx.1, hx.2⟩)
  obtain ⟨k, hk⟩ := hWp ⟨w, hw⟩
  have hwk : w ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hwU : ∀ a : Multiplicative (GaloisField p 2), w * ψ a * w⁻¹ ∈ ψ.range := by
    intro a
    rw [hψU]
    exact (Subgroup.mem_normalizer_iff.mp (hY₀U (hWY₀ hw)) _).mp (hψU ▸ ⟨a, rfl⟩)
  have hwc : ∀ μ : (GaloisField p 2)ˣ, ∃ c : X, (∀ a : Multiplicative (GaloisField p 2),
      c * ψ a * c⁻¹ =
        ψ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a))) ∧
      w * c * w⁻¹ * c⁻¹ ∈ ψ.range := by
    intro μ
    obtain ⟨c, hcK, hc⟩ := hψc μ
    have hcN : c ∈ Subgroup.normalizer (A : Set X) :=
      hψU ▸ mem_normalizer_range_of_torus ψ μ.ne_zero hc
    have hcY₀ : c ∈ X₀ := hNA.le hcN
    have hcW : w * c * w⁻¹ * c⁻¹ ∈ W := by
      have h' := (Subgroup.mem_normalizer_iff.mp (hY₀W hcY₀) w⁻¹).mp (W.inv_mem hw)
      simpa only [mul_assoc] using W.mul_mem hw h'
    exact ⟨c, hc, hψU ▸ hWK ⟨hcW, K.mul_mem (hKn.conj_mem c hcK w) (K.inv_mem hcK)⟩⟩
  apply hCU
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rw [← hψU] at hu
  obtain ⟨a, rfl⟩ := hu
  have h' := conj_eq_of_torus p h2 ψ hψinj hwU hwc hwk a
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

theorem isSolvable_of_psl2 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    (e : K ≃* PSL2GF p 2) : Group.IsSolvable X₀ := by
  have := h.normal
  obtain ⟨hU, -⟩ := h.sylow_inf_eq_of_psl2 e
  refine isSolvable_of_le_normalizer_of_psl2GF h.ne_two (by norm_num) e h.centralizer_eq_bot R ?_
  rw [hU]
  exact (h.normalizer_A_eq_of_psl2 e).ge

theorem pRank_top_eq (h : D2AlmostSimple p X R A X₀ K) : Open.pRank p (⊤ : Subgroup X) = 2 := by
  rw [← pRank_sylow_eq_globalRank p h.prime R]
  exact h.pRank_eq

end D2AlmostSimple

end Reduced

section Data

variable {G : Type} [Group G] [Finite G]

structure D2L2Data (p : ℕ) [Fact p.Prime] (M H R X : Subgroup G) : Prop where
  pair : AGLPair p M H R
  eq_R : X = R
  torus : ∃ φ : Multiplicative (GaloisField p 2) ≃* X, ∀ μ : (GaloisField p 2)ˣ,
    ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p 2),
      t * (φ a : G) * t⁻¹ =
        φ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a))
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  pcore_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) → Y ≤ X ⊔ GLBPrimeCore p H
  centralizer_le : ∀ d ∈ H ⊓ M, (∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
    d ∈ R ⊔ GLBPrimeCore p H
  pRank_le : Open.pRank p (H ⊓ M) ≤ 2
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H

variable {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.card_map_eq (h : D2Escape p P M A H R) {Y : Subgroup G} (hYR : Y ≤ R) :
    Nat.card ((Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) =
      Nat.card Y := by
  have hYH : Y ≤ H := hYR.trans h.le_H
  have hYp : IsPGroup p (Y.subgroupOf H) := (h.isPGroup.to_le hYR).comap_subtype
  exact (card_map_mk_of_isPGroup h.prime _ (primeComplementCore_coprime p) hYp).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv)

theorem D2Escape.A_eq_of_psl2 [Fact p.Prime] (h : D2Escape p P M A H R)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* PSL2GF p 2) : A = R := by
  have hRA := (hK.sylow_inf_eq_of_psl2 e).2
  rw [hRbar] at hRA
  refine Subgroup.eq_of_le_of_card_ge h.A_le ?_
  rw [← h.card_map_eq le_rfl, ← h.card_map_eq h.A_le, hRA]

theorem D2Escape.l2Data_of_psl2 [Fact p.Prime] (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* PSL2GF p 2) : D2L2Data p M H R A := by
  have hp : p.Prime := h.prime
  have hp2 : p ≠ 2 := h.ne_two
  have hsurv := h.survivorData_of_psl2 hglob hRbar hK e
  have hNHM : GLBPrimeCore p H ≤ H ⊓ M := le_inf (glbPrimeCore_le p H) h.primeCore_le
  have hAH : A ≤ H := h.A_le.trans h.le_H
  have hAp : IsPGroup p A := h.isPGroup.to_le h.A_le
  refine ⟨hsurv.pair, h.A_eq_of_psl2 hRbar hK e, ?_, hsurv.normal_dichotomy,
    fun Y hY hYN hYp => le_sup_glbPrimeCore_of_forall
      (fun W hW hWn hWp => hK.le_A_of_isPGroup_of_psl2 e hW hWn hWp) hY hYN hYp,
    hsurv.centralizer_le,
    pRank_inf_le_of_pRank_top_le hp hK.pRank_top_eq.le,
    fun L hL hLL => le_glbPrimeCore_of_perfect (hK.isSolvable_of_psl2 e) hL hLL⟩
  have := hK.normal
  obtain ⟨ψ, hψinj, hψU, hψc⟩ :=
    exists_torus_param_of_mulEquiv_psl2GF hp2 (by norm_num) e _ (hK.A_le_of_psl2 e) hK.card_A
  refine exists_torus_of_map_subgroupOf_eq hAH hAp hNHM ψ hψinj hψU fun μ => ?_
  obtain ⟨c, -, hc⟩ := hψc μ
  have hcN := mem_normalizer_range_of_torus ψ μ.ne_zero hc
  rw [hψU] at hcN
  exact ⟨c, (hK.normalizer_A_eq_of_psl2 e).le hcN, hc⟩

end Data

end CFSG.AGLEmbeddingD2
