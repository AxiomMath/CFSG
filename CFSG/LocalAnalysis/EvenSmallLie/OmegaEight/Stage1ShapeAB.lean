module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Fusion
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G] {t : G} {L U Q P : Subgroup G}

namespace ShapeA

variable (hA : ShapeA t L)
include hA

theorem not_square (h : G) : h * h ≠ t := by
  intro hh
  have hc : h ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hh]
    group
  obtain ⟨l, hl, rfl | rfl⟩ := hA.mem_iff.1 hc
  · exact hA.not_mem (hh ▸ mul_mem hl hl)
  · apply hA.not_mem
    have hct := hA.commute_of_mem hl
    have : l * t * (l * t) = l * l := by
      calc l * t * (l * t) = l * (t * l) * t := by group
        _ = l * (l * t) * t := by rw [hct]
        _ = l * l * (t * t) := by group
        _ = l * l := by rw [hA.mul_self, mul_one]
    rw [← hh, this]
    exact mul_mem hl hl

theorem t_mem_centralizer {X : Subgroup G} (hX : X ≤ L) : t ∈ centralizer (X : Set G) :=
  mem_centralizer_iff.2 fun _ hx => hA.commute_of_mem (hX hx)

theorem t_mem_normalizer {X : Subgroup G} (hX : X ≤ L) : t ∈ normalizer (X : Set G) :=
  centralizer_le_normalizer _ (hA.t_mem_centralizer hX)

theorem centralizer_le_normalizer' : centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  rw [hA.centralizer_eq]
  exact sup_le le_normalizer (zpowers_le.2 (hA.t_mem_normalizer le_rfl))

theorem shapeAB (hUL : U ≤ L) (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U)
    (hQL : Q ≤ L) (hP : P = L ⊓ normalizer (Q : Set G))
    (hQ : ∀ l ∈ L, (∀ q ∈ Q, l * q = q * l) → l ∈ Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : ShapeAB t L U Q P := by
  have htQ : t ∈ normalizer (Q : Set G) := hA.t_mem_normalizer hQL
  have hEL : (Q ⊔ zpowers t : Subgroup G) ⊓ L = Q := by
    refine le_antisymm (fun x ⟨hxE, hxL⟩ => ?_) (le_inf le_sup_left hQL)
    obtain ⟨q, hq, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => by
        rcases hA.mem_zpowers_iff.1 hb with rfl | rfl
        · rw [mul_one, one_mul]
        · exact hA.commute_of_mem (hQL ha)) hxE
    rcases hA.mem_zpowers_iff.1 hz with rfl | rfl
    · rwa [mul_one]
    · exact absurd (by simpa using L.mul_mem (L.inv_mem (hQL hq)) hxL) hA.not_mem
  refine ⟨hA.orderOf_eq, hA.not_mem, hA.le_centralizer, hA.not_mem_closure_odd, hA.not_square,
    fun V hV hV2 hUV => eq_sup_of_le hA hUL hUmax hV hV2 hUV, ?_, ?_⟩
  · apply le_antisymm
    · rintro x ⟨hxC, hxN⟩
      have hxL : x ∈ normalizer (L : Set G) := hA.centralizer_le_normalizer' hxC
      have hxQ : x ∈ normalizer (Q : Set G) := mem_normalizer_iff.2 fun y => by
        rw [← hEL]
        change y ∈ (Q ⊔ zpowers t : Subgroup G) ∧ y ∈ L ↔
          x * y * x⁻¹ ∈ (Q ⊔ zpowers t : Subgroup G) ∧ x * y * x⁻¹ ∈ L
        rw [← mem_normalizer_iff.1 hxN y, ← mem_normalizer_iff.1 hxL y]
      obtain ⟨l, hl, rfl | rfl⟩ := hA.mem_iff.1 hxC
      · exact mem_sup_left (hP ▸ ⟨hl, hxQ⟩)
      · have hlQ : l ∈ normalizer (Q : Set G) := by
          simpa using mul_mem hxQ (inv_mem htQ)
        exact mul_mem (mem_sup_left (hP ▸ ⟨hl, hlQ⟩)) (mem_sup_right (mem_zpowers t))
    · refine sup_le (fun x hx => ?_) (zpowers_le.2 ⟨mem_centralizer_singleton_iff.2 rfl,
        mem_normalizer_sup htQ (le_normalizer (mem_zpowers t))⟩)
      rw [hP] at hx
      refine ⟨hA.le_centralizer hx.1, mem_normalizer_sup hx.2 (mem_normalizer_zpowers ?_)⟩
      exact hA.commute_of_mem hx.1
  · apply le_antisymm
    · rintro x ⟨hxC, hxQ⟩
      obtain ⟨l, hl, h | h⟩ := hA.mem_iff.1 hxC <;> rw [h] at hxQ ⊢
      · exact mem_sup_left (hQ l hl fun q hq => (mem_centralizer_iff.1 hxQ q hq).symm)
      · have htQ' : t ∈ centralizer (Q : Set G) := hA.t_mem_centralizer hQL
        have hlQ : l ∈ centralizer (Q : Set G) := by
          simpa using Subgroup.mul_mem _ hxQ (Subgroup.inv_mem _ htQ')
        exact mul_mem (mem_sup_left (hQ l hl fun q hq => (mem_centralizer_iff.1 hlQ q hq).symm))
          (mem_sup_right (mem_zpowers t))
    · refine sup_le (fun x hx => ⟨hA.le_centralizer (hQL hx),
        mem_centralizer_iff.2 fun y hy => hQab y hy x hx⟩) (zpowers_le.2 ⟨
        mem_centralizer_singleton_iff.2 rfl, hA.t_mem_centralizer hQL⟩)

end ShapeA

end CFSG.EvenSmallLie.OmegaEight.Stage1
