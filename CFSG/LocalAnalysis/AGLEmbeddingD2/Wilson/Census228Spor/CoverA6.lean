module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.A6Sylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Equiv

theorem card_inf_normalizer_le_thirty {X : Type*} [Group X] [Finite X] {C : Subgroup X}
    (Φ : C →* alternatingGroup (Fin 6)) (hker : Nat.card Φ.ker ≤ 3) {k : X} (hk : k ∈ C)
    (hΦk : orderOf (Φ ⟨k, hk⟩) = 5) :
    Nat.card (C ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) : Subgroup X) ≤
      30 := by
  let K : Subgroup X := C ⊓ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X)
  let k' : C := ⟨k, hk⟩
  let ι : K →* C := Subgroup.inclusion inf_le_left
  let ψ : K →* alternatingGroup (Fin 6) := Φ.comp ι
  have hforward : ∀ y : K, ∀ n : ℤ,
      Φ (ι y) * Φ k' ^ n * (Φ (ι y))⁻¹ ∈ Subgroup.zpowers (Φ k') := by
    intro y n
    have hy : (y : X) ∈ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup X) : Set X) :=
      (Subgroup.mem_inf.mp y.2).2
    have hmem : (y : X) * k ^ n * (y : X)⁻¹ ∈ Subgroup.zpowers k :=
      (Subgroup.mem_normalizer_iff.mp hy (k ^ n)).mp
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) n)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have : ι y * k' ^ n * (ι y)⁻¹ = k' ^ j := by
      apply Subtype.ext
      simpa [ι, k'] using hj.symm
    rw [← map_zpow, ← map_inv, ← map_mul, ← map_mul, this, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hrange : ψ.range ≤ nz (Φ k') := by
    rintro _ ⟨y, rfl⟩
    show Φ (ι y) ∈ nz (Φ k')
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact hforward y n
    · intro hh
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hback := hforward y⁻¹ n
      rw [map_inv, map_inv, inv_inv] at hback
      have : (Φ (ι y))⁻¹ * Φ k' ^ n * Φ (ι y) = h := by
        rw [hn]
        group
      rw [this] at hback
      exact hback
  have hker' : Nat.card ψ.ker ≤ 3 := by
    refine le_trans ?_ hker
    refine Nat.card_le_card_of_injective
      (fun y : ψ.ker => (⟨ι y.1, y.2⟩ : Φ.ker)) ?_
    intro a b h
    have h' : ι a.1 = ι b.1 := congrArg (fun z : Φ.ker => (z : C)) h
    have h'' : (a.1 : X) = (b.1 : X) := congrArg (fun z : C => (z : X)) h'
    exact Subtype.ext (Subtype.ext h'')
  have hcard : Nat.card K = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have h10 : Nat.card ψ.range ≤ 10 := by
    refine le_trans (Subgroup.card_le_of_le hrange) ?_
    exact card_normalizer_zpowers_le_ten (Φ k') hΦk
  show Nat.card K ≤ 30
  rw [hcard]
  calc Nat.card ψ.range * Nat.card ψ.ker ≤ 10 * 3 := Nat.mul_le_mul h10 hker'
    _ = 30 := by norm_num

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
