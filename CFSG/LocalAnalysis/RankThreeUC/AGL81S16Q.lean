module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDStrongOrbit

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemmaQ {V A M M' : Subgroup G} {k : ℕ} (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hAM : A ≤ M) (hMV : M ≤ normalizer (V : Set G)) (hM'A : M' ≤ normalizer (A : Set G))
    (hne : M' ≠ M)
    (hU : ∀ u ∈ V, u ≠ 1 → M ⊓ centralizer ({u} : Set G) ≤ M' → M' = M)
    (hr : ∀ U' : Subgroup G, U' ≤ A → ¬ centralizer (U' : Set G) ≤ M' →
      2 ^ k ≤ U'.relIndex A)
    (hδ : ∀ t ∈ M', IsPGroup 2 (zpowers t) → ∀ a ∈ A, ⁅a, t⁆ ≠ 1 →
      ¬ centralizer ({⁅a, t⁆} : Set G) ≤ M' →
      2 ^ k ≤ (A ⊓ centralizer ({t} : Set G)).relIndex A) :
    ∀ B : Subgroup G, B ≤ A → B.relIndex A < 2 ^ k →
      V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G) := by
  intro B hBA hB v hv
  have hvV : v ∈ V := hv.1
  have hvB : v ∈ centralizer (B : Set G) := hv.2
  have hCB : centralizer (B : Set G) ≤ M' := by
    by_contra hcon
    exact absurd (hr B hBA hcon) (not_le.mpr hB)
  have hvM' : v ∈ M' := hCB hvB
  have hvN : v ∈ normalizer (A : Set G) := hM'A hvM'
  rw [mem_centralizer_iff]
  intro a ha
  by_contra hcomm
  have hu1 : ⁅a, v⁆ ≠ 1 := by
    intro h
    apply hcomm
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have haM : a ∈ M := hAM ha
  have huV : ⁅a, v⁆ ∈ V := by
    have h1 : a * v * a⁻¹ ∈ V := (mem_normalizer_iff.mp (hMV haM) v).mp hvV
    have h2 : a * v * a⁻¹ * v⁻¹ ∈ V := V.mul_mem h1 (V.inv_mem hvV)
    simpa [commutatorElement_def] using h2
  have hCu : ¬ centralizer ({⁅a, v⁆} : Set G) ≤ M' := by
    intro hle
    apply hne
    refine hU _ huV hu1 (le_trans ?_ hle)
    exact inf_le_right
  have hv2 : IsPGroup 2 (zpowers v) := isPGroup_two_zpowers_of_sq_eq_one (hV2 v hvV)
  have h2k := hδ v hvM' hv2 a ha hu1 hCu
  have hle : (A ⊓ centralizer ({v} : Set G)).relIndex A ≤ B.relIndex A := by
    refine relIndex_le_of_le_left ?_ (Subgroup.index_ne_zero_of_finite (H := B.subgroupOf A))
    intro b hb
    refine ⟨hBA hb, mem_centralizer_iff.mpr fun h hh => ?_⟩
    have := mem_centralizer_iff.mp hvB b hb
    simp only [Set.mem_singleton_iff] at hh
    subst hh
    exact this.symm
  exact absurd (le_trans h2k hle) (not_le.mpr hB)

end CFSG.LocalAnalysis.RankThreeUC
