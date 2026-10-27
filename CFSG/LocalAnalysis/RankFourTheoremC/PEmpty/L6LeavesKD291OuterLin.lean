module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLinAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem kd291OuterLin_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : KD291OuterLin := by
  intro p hp hp5 Y _ _ L _ hq hZp n K _ _ hpn hpK e x hx hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  let e' : ↥L ⧸ center ↥L ≃* projectiveSL n K :=
    e.trans (l212in_projectiveSLEquivStated n K).symm
  obtain ⟨φ, -, hφπ⟩ := exists_cover_linear hp hp5 hGA hq hZp (by omega) e'
  haveI : Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have hαp : (l212in_descend e' (odC L x)) ^ p = 1 := by
    have h1 : (l212in_descend e' (odC L x)) ^ p =
        ((l212in_descend e').comp (odC L)) (x ^ p) := by
      rw [map_pow]
      rfl
    rw [h1, hxp, map_one]
  obtain ⟨H, σ, hσp, hσ1, hαH⟩ := KD291Out.linear_outer_form (by omega) hp
    (by omega) (l212in_descend e' (odC L x)) hαp hnot
  obtain ⟨Ã, hÃ, hÃfix⟩ := KD291Out.linear_lift H σ
  obtain ⟨F, hFi, hFfix⟩ := KD291Out.exists_linear_torus hp hn5 hpK hσp
  have hfi : Function.Injective ((proj n K).comp
      (((slConjugation n K H : MulAut (SpecialLinearGroup (Fin n) K)) :
        SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K).comp F)) := by
    intro a b hab
    apply hFi
    have h1 : (proj n K).comp
        (((slConjugation n K H : MulAut (SpecialLinearGroup (Fin n) K)) :
          SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K).comp F) =
        ((conjAut n K H : MulAut (projectiveSL n K)) :
          projectiveSL n K →* projectiveSL n K).comp ((proj n K).comp F) := by
      refine MonoidHom.ext fun y => ?_
      exact (conjAut_proj H (F y)).symm
    rw [h1] at hab
    exact (conjAut n K H).injective hab
  exact KD291Out.three_le_pRank_of_lift L (proj n K) e' φ hφπ Ã
    (fun s => by rw [hÃ s, ← hαH]) _ hfi (fun a => hÃfix (F a) (hFfix a))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
