module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Arrow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Norm
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_not_quot_z4_elem {E K : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) :
    ¬ QuotEquivTo E K (Multiplicative (ZMod 4)) := by
  rintro ⟨φ, hφ, -⟩
  obtain ⟨e, he⟩ := hφ (Multiplicative.ofAdd (1 : ZMod 4))
  have h2 : e ^ 2 = 1 := Subtype.ext (by simpa using hE.2 e e.2)
  have h3 : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1 := by
    rw [← he, ← map_pow, h2, map_one]
  have h4 : (2 : ZMod 4) = 0 := by
    have := congrArg Multiplicative.toAdd h3
    simpa [toAdd_pow] using this
  exact absurd h4 (by decide)

theorem sec63_om6p_rank_cent [Finite G] (h33 : Asc82Lemma33) (hF : Asc82AutFacts) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G)
    {y b : G} {Y Vb E : Subgroup G} (hy : orderOf y = 2)
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hYF : InFStar Y) (hYC : InCStar Y)
    (hY6 : IsOmega6Plus Y) (hb : orderOf b = 2) (hbY : b ∈ Y)
    (hVb : IsComponentIn Vb (Y ⊓ centralizer ({b} : Set G))) (hVbF : InFStar Vb)
    (hVb29 : IsL29 Vb) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hEle : E ≤ centralizer (Vb : Set G) ⊓ centralizer ({y} : Set G)) :
    CFSG.Open.pRank 2 E ≤ 2 := by
  have hYq : IsQuasisimple ↥Y := hYc.isQuasisimple
  have hE2 : IsPGroup 2 ↥E := CFSG.Open.IsElemAbelian.isPGroup hE
  have hVbY : Vb ≤ Y := hVb.le.trans inf_le_left
  have hEN : E ≤ normalizer (Y : Set G) ⊓ centralizer (Vb : Set G) := by
    intro r hr
    refine ⟨?_, (hEle hr).1⟩
    refine sec63_mem_normalizer_of_centralizes hYc (hEle hr).2 hVb hVbY ?_
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hEle hr).1 a ha).symm
  have hshape : IsOm6P Y ∨ IsOm6M Y ∨ IsOm5Q Y ∨ (IsQuasisimple Y ∧ IsL281 Y) :=
    Or.inl ⟨hYq, hY6⟩
  have hbN : b ∈ normalizer (Y : Set G) := Subgroup.le_normalizer hbY
  have hH : IsOm6P Y → Hyp62At Y := fun hP => hHyp Y ⟨y, hy, hYc⟩ hP.2
  have hUcyc : IsCyclic ↥(E ⊓ centralizer (Y : Set G)) := sec63_isCyclic_inf h33 hS hYC hYF hE2
  have hrel : (centralizer (Y : Set G)).relIndex E ≤ 2 := by
    rcases hF.aut_cent G Y b Vb hshape hb hbN hVb hVbF hH E hE2 hEN with h | h | h | h
    · exact h
    · exact (sec63_not_om6m hYq (Or.inl hY6) h.2.1.2).elim
    · exact (sec63_not_om6m hYq (Or.inl hY6) h.2.1.2).elim
    · exact (sec63P_not_quot_z4_elem hE h.2.2).elim
  refine CFSG.SectionRank.pRank_le (p := 2) (k := 2) (by norm_num) ?_
  intro E' hE'E hE'
  calc Nat.card E' ≤ 4 := sec63_elem_le_of_relIndex hUcyc hrel E' hE'E hE'
    _ = 2 ^ 2 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
