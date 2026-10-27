module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Core

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

private theorem sec5b517Q8_isPGroup' {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}
    (hq : Sec5B517Quad K z) : IsPGroup 2 (Sec5B517Q8 hq) := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  simpa using Sec5B517Q8.pow_four hq g.2

theorem exists_sylow_normalizer_Q8 {G : Type} [Group G] [Finite G] {z : G}
    {K : Fin 4 → Subgroup G} (hq : Sec5B517Quad K z) :
    ∃ T : Subgroup G, Sec5B517Q8 hq ≤ T ∧
      IsSylow2Of T (normalizer (Sec5B517Q8 hq : Set G)) := by
  let Q := Sec5B517Q8 hq
  let N := normalizer (Q : Set G)
  have hQN : Q ≤ N := le_normalizer
  have hQ2 : IsPGroup 2 (Q.subgroupOf N) := (sec5b517Q8_isPGroup' hq).comap_subtype
  obtain ⟨P, hQP⟩ := hQ2.exists_le_sylow
  refine ⟨(P : Subgroup ↥N).map N.subtype, ?_, isSylow2Of_map_sylow P⟩
  calc Q = (Q.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hQN).symm
    _ ≤ (P : Subgroup ↥N).map N.subtype := map_mono hQP

end CFSG.OddStandard.SmallF3.Omega
