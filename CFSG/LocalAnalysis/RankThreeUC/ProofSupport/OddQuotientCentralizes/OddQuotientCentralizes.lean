module

public import CFSG.LocalAnalysis.RankThreeUC.Section11.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section11.Context
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import all CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddQuotientCentralizes

open Subgroup CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem centralizes {M X V₀ V : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsPGroup p X) (hV₀V : V₀ ≤ V) (hV : ∀ v ∈ V, v ^ 2 = 1)
    (h0 : X ≤ centralizer (V₀ : Set G)) (hq : X ≤ centralizerOnQuotient M V₀ V) :
    X ≤ centralizer (V : Set G) := by
  have mem_centralizer_of_sq {g : G} {V : Subgroup G} {n : ℕ} (hn : Odd n)
      (hg : orderOf g = n) (h : g ^ 2 ∈ centralizer (V : Set G)) : g ∈ centralizer (V : Set G) := by
    obtain ⟨j, hj⟩ := hn
    have h1 : g = (g ^ 2) ^ (j + 1) := by
      rw [← pow_mul]
      have : g ^ (2 * (j + 1)) = g ^ (2 * j + 1) * g := by rw [← pow_succ]; rfl
      rw [this, ← hj, ← hg, pow_orderOf_eq_one, one_mul]
    rw [h1]
    exact pow_mem h _
  have mem_centralizer_of_commutator {g : G} {V₀ V : Subgroup G} {n : ℕ} (hn : Odd n)
      (hg : orderOf g = n) (hV₀V : V₀ ≤ V) (hV : ∀ x ∈ V, x ^ 2 = 1)
      (hV₀ : g ∈ centralizer (V₀ : Set G))
      (hq : ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ V₀) :
      g ∈ centralizer (V : Set G) := by
    apply mem_centralizer_of_sq hn hg
    rw [mem_centralizer_iff]
    intro v hv
    set w := g * v * g⁻¹ * v⁻¹ with hw
    have hwV₀ : w ∈ V₀ := hq v hv
    have hgw : g * w = w * g := by
      have := mem_centralizer_iff.mp hV₀ w hwV₀
      exact this.symm
    have hww : w * w = 1 := by simpa [pow_two] using hV w (hV₀V hwV₀)
    have e1 : g * v * g⁻¹ = w * v := by rw [hw]; group
    have e2 : g ^ 2 * v = v * g ^ 2 := by
      have : g ^ 2 * v * (g ^ 2)⁻¹ = v := by
        have : g ^ 2 * v * (g ^ 2)⁻¹ = g * (g * v * g⁻¹) * g⁻¹ := by simp [pow_two, mul_assoc]
        rw [this, e1]
        have : g * (w * v) * g⁻¹ = (g * w * g⁻¹) * (g * v * g⁻¹) := by group
        rw [this, e1]
        have : g * w * g⁻¹ = w := by rw [hgw]; group
        rw [this, ← mul_assoc, hww, one_mul]
      calc g ^ 2 * v = (g ^ 2 * v * (g ^ 2)⁻¹) * g ^ 2 := by group
        _ = v * g ^ 2 := by rw [this]
    exact e2.symm
  intro g hg
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hX.exists_orderOf_eq_pow (⟨g, hg⟩ : X)
  have hk' : orderOf g = p ^ k := by
    rw [← hk]; exact (orderOf_injective X.subtype Subtype.val_injective ⟨g, hg⟩)
  exact mem_centralizer_of_commutator
    ((hp.odd_of_ne_two hp2).pow) hk' hV₀V hV (h0 hg) (hq hg).2.2.2

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddQuotientCentralizes
