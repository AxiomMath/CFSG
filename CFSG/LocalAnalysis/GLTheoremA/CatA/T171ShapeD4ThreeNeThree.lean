module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151ExcDefs
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedD4
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


theorem d4ExitAt_of_ne_three (R : Type) [Group R] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : F151.D4ExitAt R p := by
  intro _ w _ _ hwp _ Kc _ hcat hw hmem
  let Q := ↥Kc ⧸ Subgroup.center ↥Kc
  let g : CFSG.GroupActions.subgroupStabAut Kc := ⟨MulAut.conj w, hw⟩
  let α : MulAut Q :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Kc
      (CFSG.GroupActions.subgroupStabRestrict Kc g)
  have hg : g ^ p = 1 := by
    apply Subtype.ext
    change ((MulAut.conj w : MulAut R) ^ p) = 1
    rw [← map_pow, hwp, map_one]
  have hαp : α ^ p = 1 := by
    change (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Kc
      (CFSG.GroupActions.subgroupStabRestrict Kc g)) ^ p = 1
    rw [← map_pow, ← map_pow, hg, map_one, map_one]
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨d', hv⟩ | _
  · exact absurd hi (by simp [onLie])
  · exact absurd hi (by simp [onLie])
  · obtain ⟨q, rfl, -⟩ := hi
    let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
    haveI : Finite F :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.D 4 q, hv⟩
    let θ : Q ≃* adjointGroup Tag.D4 F :=
      e.trans ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid
          4 q hv).trans
        (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
          F).some)
    have hmem' : MulAut.congr θ α ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
          (adjointGroup Tag.D4 F) :=
      (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hmem
    have hpow' : MulAut.congr θ α ^ p = 1 := by
      rw [← map_pow, hαp, map_one]
    obtain ⟨h, hh⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.exists_conj_eq_of_mem_innAutDerived_D4
        hp hp2 hp3 hmem' hpow'
    refine (CFSG.HardMathSupport.Dickson.Sec6.I923.congr_mem_inner_iff_of_equiv θ α).1 ?_
    rw [hh]
    exact ⟨h, rfl⟩
  · exact absurd hi (by simp [onLie])

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
