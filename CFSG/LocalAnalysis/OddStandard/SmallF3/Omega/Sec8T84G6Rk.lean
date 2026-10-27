module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L65

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec8t84g6_rank [Finite G] (h64 : Asc82Lemma64) {γ : G} {K : Subgroup G}
    (hS : Sec3SettingLB G γ K) (hHyp : Asc82Hyp62 G) (hXC : InC K) (hXF : InFStar K)
    (hno : ¬ (IsU33 K ∨ IsL29 K)) :
    ∀ E : Subgroup G, E ≤ centralizer (K : Set G) → CFSG.Open.IsElemAbelian 2 E →
      Nat.card E ≤ 4 := by
  intro E hEC hE
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, IsSylow2Of T (centralizer (K : Set G)) :=
    ⟨_, isSylow2Of_map_sylow (Classical.arbitrary (Sylow 2 ↥(centralizer (K : Set G))))⟩
  have hE2 : IsPGroup 2 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 (g : G) g.2)⟩
  have hrank : ∀ m : ℕ, CFSG.Open.pRank 2 T ≤ m → CFSG.Open.pRank 2 E ≤ m :=
    fun m hm => sec65_pRank_le_of_sylow hT hEC hE2 hm
  have hE2' : CFSG.Open.pRank 2 E ≤ 2 := by
    rcases h64 G γ K hS hHyp K hXC hXF T hT with hcyc | ⟨-, hr2⟩ | ⟨hshape, -⟩
    · exact hrank 2 ((sec65_pRank_cyclic hcyc).trans (by norm_num))
    · exact hrank 2 hr2.le
    · exact absurd hshape hno
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2
  have hk2 : k ≤ CFSG.Open.pRank 2 E := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hk
  calc Nat.card E = 2 ^ k := hk
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hk2.trans hE2')
    _ = 4 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
