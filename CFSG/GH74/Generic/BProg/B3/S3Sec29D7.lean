module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace S3Sec29D7

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J R : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup {H H' : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hH' : g ∈ normalizer (H' : Set G)) : g ∈ normalizer ((H ⊔ H' : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hH' ⊢
  rw [Subgroup.map_sup, hH, hH']

omit [Finite G] in
theorem false_of_D8 {M P : Subgroup G} {a w : G} (hui : ∀ r ∈ P, r * r ∈ cSec M → r ∈ cSec M ∨ r * y⁻¹ ∈ cSec M)
    (hyM : y ∉ cSec M) (hPM : P ≤ normalizer (M : Set G)) (haP : a ∈ P) (hwP : w ∈ P)
    (haa : a * a = y) (hww : w * w = 1) (hwa : w * a * w⁻¹ = a⁻¹) (hya : y * a = a * y) : False := by
  have hn : ∃ n ∈ cSec M, n * a * n⁻¹ = a⁻¹ := by
    rcases hui w hwP (by rw [hww]; exact one_mem _) with h1 | h1
    · exact ⟨w, h1, hwa⟩
    · refine ⟨w * y⁻¹, h1, ?_⟩
      have hya' : y⁻¹ * a * y = a := by
        calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
          _ = y⁻¹ * (y * a) := by rw [hya]
          _ = a := by group
      calc w * y⁻¹ * a * (w * y⁻¹)⁻¹ = w * (y⁻¹ * a * y) * w⁻¹ := by group
        _ = w * a * w⁻¹ := by rw [hya']
        _ = a⁻¹ := hwa
  obtain ⟨n, hnM, hna⟩ := hn
  have h1 : a * n⁻¹ * a⁻¹ ∈ cSec M := Stage1.Thm2.Recip.cSec_conj M (hPM haP) (inv_mem hnM)
  have h2 : n * (a * n⁻¹ * a⁻¹) ∈ cSec M := mul_mem hnM h1
  have h3 : n * (a * n⁻¹ * a⁻¹) = y⁻¹ := by
    calc n * (a * n⁻¹ * a⁻¹) = (n * a * n⁻¹) * a⁻¹ := by group
      _ = a⁻¹ * a⁻¹ := by rw [hna]
      _ = (a * a)⁻¹ := by group
      _ = y⁻¹ := by rw [haa]
  rw [h3] at h2
  exact hyM (by simpa using inv_mem h2)

end S3Sec29D7

end CFSG.GH74.Generic.BProg.B3
