module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section API
variable {X : Type} [Group X] {W K : Subgroup X} [W.Normal]

theorem toBar_props (W K : Subgroup X) [W.Normal] :
    Function.Surjective (toBar W K) ∧ ∀ k : ↥K, toBar W K k = 1 ↔ (k : X) ∈ W := by
  refine ⟨?_, fun k => ?_⟩
  · rintro ⟨y, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · constructor
    · intro h
      have h' : ((toBar W K k : ↥(bar W K)) : X ⧸ W) = 1 := by rw [h]; rfl
      exact (QuotientGroup.eq_one_iff _).1 h'
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).2 h

theorem zPre_iff_center (k : ↥K) :
    (k : X) ∈ zPre W K ↔ toBar W K k ∈ Subgroup.center ↥(bar W K) := by
  obtain ⟨hsurj, hker⟩ := toBar_props W K
  have key : ∀ k' : ↥K, (⁅(k : X), (k' : X)⁆ ∈ W ↔
      toBar W K k' * toBar W K k = toBar W K k * toBar W K k') := by
    intro k'
    have h1 : ((⁅k, k'⁆ : ↥K) : X) = ⁅(k : X), (k' : X)⁆ := rfl
    rw [← h1, ← hker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, eq_comm]
  rw [Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hk⟩ g
    obtain ⟨k', rfl⟩ := hsurj g
    exact (key k').1 (hk k' k'.2)
  · intro h
    exact ⟨k.2, fun k' hk' => (key ⟨k', hk'⟩).2 (h _)⟩

theorem mem_indAut_iff {B : Subgroup X} (hB : B ≤ Subgroup.normalizer (K : Set X))
    (φ : MulAut ↥(bar W K)) :
    φ ∈ indAut W K B ↔ ∃ b ∈ B, ∀ k k' : ↥K, (k' : X) = b * k * b⁻¹ →
      φ (toBar W K k) = toBar W K k' := by
  obtain ⟨hsurj, -⟩ := toBar_props W K
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨b, hb, hbg⟩ := (Subgroup.mem_subgroupOf.1 hg)
    refine ⟨b, hb, fun k k' hk' => ?_⟩
    apply Subtype.ext
    show (g : X ⧸ W) * QuotientGroup.mk (k : X) * (g : X ⧸ W)⁻¹ = QuotientGroup.mk (k' : X)
    rw [← hbg, hk']
    simp
  · rintro ⟨b, hb, h⟩
    have hbn : QuotientGroup.mk' W b ∈ Subgroup.normalizer (bar W K : Set (X ⧸ W)) :=
      Subgroup.le_normalizer_map (QuotientGroup.mk' W) ⟨b, hB hb, rfl⟩
    refine ⟨⟨QuotientGroup.mk' W b, hbn⟩, Subgroup.mem_subgroupOf.2 ⟨b, hb, rfl⟩, ?_⟩
    ext y
    obtain ⟨k, rfl⟩ := hsurj y
    have hk' : b * (k : X) * b⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 (hB hb) k).1 k.2
    rw [h k ⟨b * k * b⁻¹, hk'⟩ rfl]
    show QuotientGroup.mk b * QuotientGroup.mk (k : X) * (QuotientGroup.mk b)⁻¹ =
      QuotientGroup.mk (b * (k : X) * b⁻¹)
    simp

end API

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
