module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped MatrixGroups

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem false_of_benderBorel {q k : ℕ} (hB : fusionBenderBorel X q k) {U Y : Subgroup X}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hY : Y ≤ Subgroup.normalizer (U : Set X))
    (hYns : ¬ Group.IsSolvable ↥Y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hUQ⟩ := hU2.exists_le_sylow
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hND⟩, -⟩ := hB Q
  set N := Subgroup.normalizer ((Q : Subgroup X) : Set X) with hNdef
  have hQN : (Q : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hNU : Subgroup.normalizer (U : Set X) ≤ N := by
    intro g hg
    by_contra hgN
    have hgodd := hSE.2.2 g hgN
    have hUle : U ≤ N ⊓ N.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro u hu
      refine ⟨hQN (hUQ hu), Subgroup.mem_map.mpr ⟨g * u * g⁻¹, ?_, ?_⟩⟩
      · exact hQN (hUQ ((Subgroup.mem_normalizer_iff.mp hg u).mp hu))
      · simp [mul_assoc]
    have hne : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU
    obtain ⟨n, hn, hcard⟩ := hU2.nontrivial_iff_card.mp hne
    have hdvd : 2 ∣ Nat.card (N ⊓ N.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup X) :=
      (dvd_pow_self 2 hn.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hUle)
    exact (Nat.not_even_iff_odd.mpr hgodd) (even_iff_two_dvd.mpr hdvd)
  have hDN : D ≤ N := le_sup_right.trans hND.le
  have hQsolv : Group.IsSolvable ↥((Q : Subgroup X).subgroupOf N) := by
    have hp : IsPGroup 2 ((Q : Subgroup X).subgroupOf N) :=
      Q.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
    have := hp.isNilpotent
    infer_instance
  have hsup : ((Q : Subgroup X).subgroupOf N) ⊔ D.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQN hDN, hND, Subgroup.subgroupOf_self]
  have hDcyc' : IsCyclic ↥(D.subgroupOf N) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hDN)).mpr hDcyc
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' ((Q : Subgroup X).subgroupOf N)).comp (D.subgroupOf N).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : (((Q : Subgroup X).subgroupOf N) ⊔ D.subgroupOf N).map
        (QuotientGroup.mk' ((Q : Subgroup X).subgroupOf N)) = ⊤ := by
      rw [hsup]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    exact h1
  have hDsolv : Group.IsSolvable ↥(D.subgroupOf N) := inferInstance
  have hquot : Group.IsSolvable (↥N ⧸ (Q : Subgroup X).subgroupOf N) :=
    Group.isSolvable_of_surjective hsurj
  have hNsolv : Group.IsSolvable ↥N :=
    Group.isSolvable_of_subgroup_quotient ((Q : Subgroup X).subgroupOf N)
  exact hYns (Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion (hY.trans hNU) : ↥Y →* ↥N)) (Subgroup.inclusion_injective _))

theorem exists_fusionBenderBorel_of_fusionIsBenderGroup (h : fusionIsBenderGroup X) :
    ∃ q k : ℕ, fusionBenderBorel X q k := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩

end Abstract

section Config

variable {G : Type} [Group G] [Finite G] {K B B' P R : Subgroup G} {m : ℕ}

theorem ExamConfig.false_of_bender (h : ExamConfig K B B' P R m) {q k : ℕ}
    (hB : fusionBenderBorel (↥K ⧸ Subgroup.center ↥K) q k) : False := by
  obtain ⟨Ab, Bb, hA, hp, hn, hns⟩ := h.exists_bar
  exact false_of_benderBorel hB hA hp hn hns

theorem examExcludes_evenL2 : ExamExcludes FamEvenL2 := by
  intro G _ _ K B B' P R m h ⟨f, hf, hmodel⟩
  obtain ⟨q, k, hB⟩ := exists_fusionBenderBorel_of_fusionIsBenderGroup
    (K1.fusionIsBenderGroup_of_stated_psl_two hf hmodel)
  exact h.false_of_bender hB

theorem examExcludes_evenU3 : ExamExcludes FamEvenU3 := by
  intro G _ _ K B B' P R m h ⟨f, hf, hmodel⟩
  obtain ⟨q, k, hB⟩ := exists_fusionBenderBorel_of_fusionIsBenderGroup
    (K1.fusionIsBenderGroup_of_stated_psu_three hf hmodel)
  exact h.false_of_bender hB

theorem examExcludes_sz : ExamExcludes FamSz := by
  rintro G _ _ K B B' P R m h ⟨f, -, -, hmodel⟩
  obtain ⟨q, k, hB⟩ := exists_fusionBenderBorel_of_fusionIsBenderGroup
    (K1.fusionIsBenderGroup_of_suzukiModel hmodel)
  exact h.false_of_bender hB

end Config

end CFSG.QuasithinUnique.Lin2
