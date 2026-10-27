module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G]

theorem conj_barM_mem {X M : Subgroup G} {z : ↥X} (hz : (z : G) ∈ Subgroup.normalizer (M : Set G))
    {b : ↥X ⧸ CFSG.pCore 2 ↥X} (hb : b ∈ barM X M) :
    (QuotientGroup.mk z : ↥X ⧸ CFSG.pCore 2 ↥X) * b * (QuotientGroup.mk z)⁻¹ ∈ barM X M := by
  obtain ⟨m, hm, rfl⟩ := (mem_barM _).1 hb
  have hm' : (z : G) * (m : G) * (z : G)⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 hz _).1 hm
  refine (mem_barM _).2 ⟨z * m * z⁻¹, ?_, ?_⟩
  · simpa using hm'
  · simp

theorem conj_barM_iff {X M : Subgroup G} {z : ↥X} (hz : (z : G) ∈ Subgroup.normalizer (M : Set G))
    (b : ↥X ⧸ CFSG.pCore 2 ↥X) :
    b ∈ barM X M ↔
      (QuotientGroup.mk z : ↥X ⧸ CFSG.pCore 2 ↥X) * b * (QuotientGroup.mk z)⁻¹ ∈ barM X M := by
  constructor
  · exact conj_barM_mem hz
  · intro h
    have hz' : ((z⁻¹ : ↥X) : G) ∈ Subgroup.normalizer (M : Set G) := by
      simpa using inv_mem hz
    have := conj_barM_mem hz' h
    simpa [mul_assoc] using this

theorem mem_normalizer_barM {X M : Subgroup G} {z : ↥X}
    (hz : (z : G) ∈ Subgroup.normalizer (M : Set G)) :
    (QuotientGroup.mk z : ↥X ⧸ CFSG.pCore 2 ↥X) ∈
      Subgroup.normalizer ((barM X M : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  exact conj_barM_iff hz b

end CFSG.HardMathSupport.Cooperstein.Proving

end
