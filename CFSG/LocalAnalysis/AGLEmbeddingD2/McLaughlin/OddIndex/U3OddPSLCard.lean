module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddPSL

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  {ζ : F} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution F p f ζ = -ζ)
  (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1)

include hζ0 hζ hF hω hq3

theorem pslMk_mem_normalizer_iff (x : SL(2, fixedSubfield F p f)) :
    pslMk (fixedSubfield F p f) x ∈ Subgroup.normalizer ((Subgroup.zpowers (pslMk
      (fixedSubfield F p f) (diagSL (pow_eq_self_of_orderOf_three hω hq3))) : Subgroup _) : Set _) ↔
      levi hζ0 hζ x ∈ normA0 hF ω := by
  refine ⟨levi_mem_normA0_of_psl_normalizer hζ0 hζ hF hω hq3, fun hx => ?_⟩
  set d := (diagSL (pow_eq_self_of_orderOf_three hω hq3) : SL(2, fixedSubfield F p f)) with hd
  have hld : levi hζ0 hζ d = tSU hF ω := levi_diagSL hζ0 hζ hF _
  have key : ∀ y : SL(2, fixedSubfield F p f), levi hζ0 hζ y ∈ normA0 hF ω →
      y * d * y⁻¹ ∈ Subgroup.zpowers d := by
    intro y hy
    have h1 : levi hζ0 hζ y * tSU hF ω * (levi hζ0 hζ y)⁻¹ ∈ Subgroup.zpowers (tSU hF ω) :=
      ((Subgroup.mem_normalizer_iff.1 hy) (tSU hF ω)).1 (Subgroup.mem_zpowers _)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine ⟨n, levi_injective hζ0 hζ ?_⟩
    rw [map_zpow, hld, hn, map_mul, map_mul, map_inv, hld]
  have h1 := key x hx
  have h2 := key x⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hx)
  rw [inv_inv] at h2
  have h3 := mem_normalizer_zpowers_of_conj_mem h1 h2
  exact map_mem_normalizer_zpowers (pslMk (fixedSubfield F p f)) h3

theorem normalizer_psl_eq_map_comap :
    Subgroup.normalizer ((Subgroup.zpowers (pslMk (fixedSubfield F p f)
        (diagSL (pow_eq_self_of_orderOf_three hω hq3))) : Subgroup _) : Set _) =
      ((normA0 hF ω).comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) := by
  apply le_antisymm (normalizer_psl_le_map_comap hζ0 hζ hF hω hq3)
  rintro _ ⟨x, hx, rfl⟩
  exact (pslMk_mem_normalizer_iff hζ0 hζ hF hω hq3 x).2 hx

theorem card_normalizer_psl (hp2 : p ≠ 2) :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers (pslMk (fixedSubfield F p f)
        (diagSL (pow_eq_self_of_orderOf_three hω hq3))) : Subgroup
          (PSL2MatrixGroup (fixedSubfield F p f))) : Set (PSL2MatrixGroup (fixedSubfield F p f)))) =
      p ^ f - 1 := by
  rw [normalizer_psl_eq_map_comap hζ0 hζ hF hω hq3]
  have hTN := range_tSU_le_normA0 hF hω hq3
  have h := card_inf_centralizer_zSU_eq hζ0 hζ hF hp2 (normA0 hF ω) hTN
  have hle : normA0 hF ω ≤ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) := by
    intro x hx g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (zSU_comm_normA0 hF hω hq3 hp2 x hx).symm
  rw [inf_eq_left.2 hle, card_normA0 hF hω hq3] at h
  have hpos : 0 < 2 * ((p ^ f) ^ 2 - 1) := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    omega
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  linarith

omit hω hq3

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
