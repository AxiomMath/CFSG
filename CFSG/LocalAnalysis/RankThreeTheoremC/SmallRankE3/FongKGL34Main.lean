module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Grp
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Types
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Frame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem kGNoncycCentL34_holds : KGNoncycCentL34 := by
  intro n k F _ _ hn hcard _ _ _ S B hS hnc hSI _ hBS
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hcard2 : Nat.card F = 2 ^ (2 * k) := by
    rw [hcard, pow_mul]
    norm_num
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst hk0
    have h1 : Nat.card F = 1 := by simpa using hcard
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hf : 1 ≤ 2 * k := by omega
  have hEven : Even (Nat.card F) := by
    rw [hcard2]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hU : UnitaryFieldData 2 k F := ⟨Nat.prime_two, hk, hcard2⟩
  haveI : CharP F 2 := hU.charP
  have hSD := inf_linearAutGroup_eq_bot hn3 hEven hS hSI
  have hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
    commute_of_mem_S hn3 hcard2 hf hSD hs ht
  obtain ⟨a, ha, b, hb, ha1, hb1, hab, haa, hbb⟩ := exists_two_involutions_of_noncyclic hS hSc hnc
  obtain ⟨⟨ι₁, hι₁S, hι₁1, hι₁sq, hι₁F⟩, ⟨ι₂, hι₂S, hι₂1, hι₂sq, hι₂G⟩⟩ :=
    exists_field_and_graph_involution hn3 hcard2 hf hSD hSc ha hb ha1 hb1 hab haa hbb
  obtain ⟨A₁, σ, hσ, hι₁eq⟩ := hι₁F
  obtain ⟨A₂, hι₂eq⟩ := hι₂G
  obtain ⟨-, hσx, H, hH⟩ := even_linear_field_involution_descent hf hcard2 hn3 A₁ σ hσ
    (by rw [pow_two, ← hι₁eq]; exact hι₁sq)
  have hσk : ∀ x, σ x = x ^ 2 ^ k := fun x => by
    rw [hσx x]
    congr 2
    omega
  have hι₁H : ι₁ = conjAut n F H * fieldAut n F σ * (conjAut n F H)⁻¹ := hι₁eq.trans hH
  have hcomm : ι₁ * ι₂ = ι₂ * ι₁ := hSc _ hι₁S _ hι₂S
  obtain ⟨C, hCφ, hCs, hCnf⟩ := graph_normal_form hn3 hk hcard2 σ hσk H A₂
    (by rw [← hι₁H, ← hι₂eq]; exact hcomm) (by rw [← hι₂eq]; exact hι₂sq)
  have hι₂H : ι₂ = conjAut n F H * (conjAut n F C * dualAut n F) * (conjAut n F H)⁻¹ := by
    rw [← hCnf, ← hι₂eq]
    group
  have hgen := closure_eq_top_of_rational_symmetric hn3 σ C hCφ hCs
  have hconj := closure_fixedPoints_conj (conjAut n F H) (fieldAut n F σ)
    (conjAut n F C * dualAut n F)
  rw [hgen, Subgroup.map_top] at hconj
  rw [← hι₁H, ← hι₂H] at hconj
  refine ⟨ι₁, ι₂, hι₁S, hι₂S, hι₁1, hι₂1, fun τ hτ => hSc _ hτ _ hι₁S,
    fun τ hτ => hSc _ hτ _ hι₂S,
    fun τ hτ => commute_of_mem_normalizer hn3 hcard2 hf hSD (hBS hτ) hι₁S,
    fun τ hτ => commute_of_mem_normalizer hn3 hcard2 hf hSD (hBS hτ) hι₂S, ?_⟩
  rw [hconj]
  exact MonoidHom.range_eq_top.mpr (conjAut n F H).surjective

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
