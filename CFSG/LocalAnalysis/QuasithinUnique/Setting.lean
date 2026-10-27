module

public import CFSG.LocalAnalysis.QuasithinUnique.Reduction

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem index_subgroupOf_top (H : Subgroup G) : (H.subgroupOf ⊤).index = H.index :=
  Subgroup.relIndex_top_right H

theorem isSylowTwoOf_top_of_sylow (T : Sylow 2 G) : IsSylowTwoOf (T : Subgroup G) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, T.isPGroup', ?_⟩
  rw [index_subgroupOf_top]
  exact T.not_dvd_index

theorem uniqueSetting_of_sylow [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : QTKECore G) (T : Sylow 2 G)
    (hT : ∃! M : Subgroup G,
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M) :
    ∃ M : Subgroup G, UniqueSetting G T M := by
  obtain ⟨M, ⟨hM, hTM⟩, huniq⟩ := hT
  exact ⟨M, ⟨inferInstance, hnonab, hqtke, isSylowTwoOf_top_of_sylow T, hM, hTM,
    fun M' hM' hTM' => huniq M' ⟨hM', hTM'⟩⟩⟩

namespace UniqueSetting

variable {T M : Subgroup G} (h : UniqueSetting G T M)
include h

theorem isPGroup : IsPGroup 2 T := h.sylow.2.1

theorem isTwoLocal : CFSG.Open.IsTwoLocal M := h.maxLocal.1

theorem charTwo : CharTwo M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : ¬ 2 ∣ (T : Subgroup G).index := by
    simpa only [index_subgroupOf_top] using h.sylow.2.2
  let S : Sylow 2 G := h.isPGroup.toSylow hT2
  exact h.qtke.2.1 M h.maxLocal.1 ⟨S, h.le⟩

end UniqueSetting

end CFSG.QuasithinUnique
