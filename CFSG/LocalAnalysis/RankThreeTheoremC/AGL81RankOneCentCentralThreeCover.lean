module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCentralThreeTorus
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.CentralThree

open CFSG.Open Matrix CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank

theorem four_le_pRank_of_linCover {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 5 ≤ n)
    (h3 : 3 ∣ Nat.card Kˣ) {L : Type*} [Group L] [Finite L]
    (ρ : SpecialLinearGroup (Fin n) K →* L)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    4 ≤ pRank 3 (⊤ : Subgroup L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  set e := specialLinearGroupEquivStatedSL n K
  let π : StatedSL n K →* L := ρ.comp e.symm.toMonoidHom
  have hπ : π.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
    intro x hx
    have hx' : e.symm x ∈ ρ.ker := hx
    rw [← map_center_eq_statedScalars n K]
    exact ⟨e.symm x, hker hx', e.apply_symm_apply x⟩
  exact four_le_pRank_torus_of_scalarKer π hπ hζ (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩)
    (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩) (i₄ := ⟨4, by omega⟩)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) fun j => torusDiag_mem_SL (prod_torusVec ζ j _)

theorem four_le_pRank_of_uniCover {K : Type} [Field K] [Finite K] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 5 ≤ n) (h3 : 3 ∣ 2 ^ f + 1) {L : Type*} [Group L]
    [Finite L] (ρ : StatedSU n (2 ^ f) K →* L)
    (hker : ρ.ker ≤ Subgroup.center (StatedSU n (2 ^ f) K)) :
    4 ≤ pRank 3 (⊤ : Subgroup L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 2 ^ f * 2 ^ f - 1 := by
    rw [Nat.card_units, hK, sq]
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [hcard]
    obtain ⟨c, hc⟩ := h3
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    refine ⟨(2 ^ f - 1) * c, ?_⟩
    have : 2 ^ f * 2 ^ f - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      zify [h1, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ f * 2 ^ f ≠ 0)]
      ring
    rw [this, hc]
    ring
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3K
  have hζq : ζ ^ (2 ^ f + 1) = 1 := by
    obtain ⟨c, hc⟩ := h3
    rw [hc, pow_mul, ← hζ, pow_orderOf_eq_one, one_pow]
  have hπ : ρ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) :=
    hker.trans (CFSG.StandardType.center_statedSU_le_scalars hK (by omega))
  refine four_le_pRank_torus_of_scalarKer ρ hπ hζ (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩)
    (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩) (i₄ := ⟨4, by omega⟩)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) fun j => torusDiag_mem_SU (by positivity) (prod_torusVec ζ j _) ?_
  rw [torusVec_pow, hζq, torusVec_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.CentralThree
