module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxCfg
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection
  isSimpleGroup_of_section_bot exists_not_comm_of_section_bot
  commutator_zpowers_le_of_le_normalizer exists_not_commute_of_ne_bot)
open scoped commutatorElement

theorem p622_le_of_inf_ne_bot {G : Type} [Group G] {M : Subgroup G} {x z : G}
    (h614 : P622Prop614At M x z) (hBM : zpowers x ⊔ zpowers z ≤ M) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hBS : zpowers x ⊔ zpowers z ≤ normalizer (S : Set G))
    (hSM : S ⊓ M ≠ ⊥) : S ≤ M := by
  have hS1 : S ≠ ⊥ := fun h => hSM (by rw [h]; exact bot_inf_eq _)
  have hH : IsTwoLocal (normalizer (S : Set G)) := ⟨S, hS1, hS2, rfl⟩
  refine le_normalizer.trans (h614 _ hH hBS ⟨S ⊓ M, ?_, hS2.to_le inf_le_left, hSM, ?_⟩)
  · exact inf_le_inf le_normalizer le_rfl
  · exact (le_inf hBS (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

namespace P622KxCfg

theorem prime (c : P622KxCfg p P M x z T S L) : p.Prime :=
  c.conf.failure.prime

theorem ne_two (c : P622KxCfg p P M x z T S L) : p ≠ 2 :=
  c.conf.failure.ne_two

theorem orderOf_z (c : P622KxCfg p P M x z T S L) : orderOf z = p := by
  haveI : Fact p.Prime := ⟨c.conf.failure.prime⟩
  exact orderOf_eq_prime c.conf.failure.central.pow_eq_one c.conf.failure.central.ne_one

theorem isSimple (c : P622KxCfg p P M x z T S L) : IsSimpleGroup ↥L :=
  isSimpleGroup_of_section_bot c.simple

theorem S_le_normalizer (c : P622KxCfg p P M x z T S L) : S ≤ normalizer (L : Set G) :=
  (le_inf (c.conf.S_le_M c.setting) c.conf.S_le_centralizer).trans c.norm

theorem commutator_le (c : P622KxCfg p P M x z T S L) : ⁅zpowers z, S⁆ ≤ L :=
  commutator_zpowers_le_of_le_normalizer c.z_mem c.S_le_normalizer

theorem normalizer_le (c : P622KxCfg p P M x z T S L) {U : Subgroup G} (hUL : U ≤ L)
    (hU2 : IsPGroup 2 U) (hz : z ∈ normalizer (U : Set G)) (hUM : U ⊓ M ≠ ⊥) :
    normalizer (U : Set G) ≤ M := by
  have hU1 : U ≠ ⊥ := fun h => hUM (by rw [h]; exact bot_inf_eq _)
  have hxU : x ∈ normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer (U : Set G) (mem_centralizer_iff.mpr fun h hh =>
      mem_centralizer_singleton_iff.mp (c.le_C (hUL hh)))
  have hB : zpowers x ⊔ zpowers z ≤ normalizer (U : Set G) :=
    sup_le (zpowers_le.mpr hxU) (zpowers_le.mpr hz)
  have hUM' : U ≤ M :=
    p622_le_of_inf_ne_bot c.conf.prop614 (c.conf.B_le_M c.setting) hU2 hB hUM
  exact c.conf.normalizer_le_of_invariant hU2 hU1 hUM' hB

theorem normalizer_zpowers_le (c : P622KxCfg p P M x z T S L) :
    normalizer (zpowers z : Set G) ⊓ L ≤ M :=
  inf_le_left.trans (c.conf.failure.normalizer_zpowers_le c.setting)

theorem exists_not_commute (c : P622KxCfg p P M x z T S L) :
    ∃ y ∈ (⁅zpowers z, S⁆ : Subgroup G), z * y ≠ y * z :=
  exists_not_commute_of_ne_bot c.conf.failure.prime c.conf.failure.ne_two
    c.conf.failure.central.pow_eq_one c.conf.S_isPGroup
    (c.conf.z_le_normalizer (mem_zpowers z)) (c.conf.R_ne_bot c.setting)

theorem B_le_M (c : P622KxCfg p P M x z T S L) : zpowers x ⊔ zpowers z ≤ M :=
  c.conf.B_le_M c.setting

theorem S_le_M (c : P622KxCfg p P M x z T S L) : S ≤ M :=
  c.conf.S_le_M c.setting

theorem centralizer_z_le (c : P622KxCfg p P M x z T S L) : centralizer ({z} : Set G) ≤ M :=
  c.conf.centralizer_le_M c.setting

theorem P_le_M (c : P622KxCfg p P M x z T S L) : (P : Subgroup G) ≤ M :=
  c.conf.failure.sylow_le c.setting

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
