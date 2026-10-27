module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterUniAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterUniTorus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.Proj

theorem kd291OuterUni_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : KD291OuterUni := by
  intro p hp hp5 Y _ _ L _ hq hZp n r f _ K _ _ _ hpn hK hpq e x hx hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSU 0 (r ^ f) K)) :=
        inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  obtain ⟨φ, -, hφπ⟩ := exists_cover_unitary hp hp5 hGA hq hZp hn5 hK e
  haveI : Group.IsPerfect (CFSG.Open.StatedSU n (r ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  have hU := AutSU.unitaryFieldData_of_card hK
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have hαp : (l212in_descend e (odC L x)) ^ p = 1 := by
    have h1 : (l212in_descend e (odC L x)) ^ p = ((l212in_descend e).comp (odC L)) (x ^ p) := by
      rw [map_pow]
      rfl
    rw [h1, hxp, map_one]
  obtain ⟨H, σ, hσp, hσ1, hαH⟩ := KD291Out.uni_outer_form hU hn5 hK hp hp2
    (l212in_descend e (odC L x)) hαp hnot
  obtain ⟨Ã, hÃ, hÃfix⟩ := KD291Out.uni_lift hU (by omega) H σ
  obtain ⟨F, hFi, hFfix⟩ := KD291Out.exists_uni_torus hK hp hn5 hpq hσp
  have hfi : Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
      (StatedSU n (r ^ f) K))).comp ((uLift hU H 1).comp F)) := by
    intro a b hab
    apply hFi
    have h1 : (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
        (StatedSU n (r ^ f) K))).comp ((uLift hU H 1).comp F) =
        ((uConjAut hU (by omega) H : MulAut (StatedProj (StatedSU n (r ^ f) K))) :
          StatedProj (StatedSU n (r ^ f) K) →* StatedProj (StatedSU n (r ^ f) K)).comp
        ((QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K))).comp F) := by
      refine MonoidHom.ext fun y => ?_
      have h2 := uLift_proj hU (by omega : 1 ≤ n) H 1 (F y)
      rw [map_one, mul_one] at h2
      exact h2.symm
    rw [h1] at hab
    exact (uConjAut hU (by omega) H).injective hab
  exact KD291Out.three_le_pRank_of_lift L (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
    (StatedSU n (r ^ f) K))) e φ hφπ Ã
    (fun s => by
      have h1 := hÃ s
      rw [← hαH] at h1
      exact h1) _ hfi (fun a => hÃfix (F a) (hFfix a))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
