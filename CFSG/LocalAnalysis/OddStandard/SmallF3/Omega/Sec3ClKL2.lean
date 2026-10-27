module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClKL
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClGroup
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClShape
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem cl_clFixHom_injective (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 0 < Module.finrank (ZMod 3) (commSp s)) : Function.Injective (clFixHom hQ hs) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hcoe : toProj Q (blockHom hs ((a : OGroup (Q.restrict (fixSp s))), 1)) = 1 := by
    have h := congrArg Subtype.val ha
    simpa [coe_clFixHom] using h
  have hmem : blockHom hs ((a : OGroup (Q.restrict (fixSp s))), 1) ∈ piGroup Q :=
    (QuotientGroup.eq_one_iff _).mp hcoe
  rcases mem_piGroup_iff.mp hmem with h1 | hpi
  · apply Subtype.ext
    have hp : ((a : OGroup (Q.restrict (fixSp s))),
        (1 : OGroup (Q.restrict (commSp s)))) =
        ((1 : OGroup (Q.restrict (fixSp s))), (1 : OGroup (Q.restrict (commSp s)))) := by
      apply blockHom_injective hs
      rw [h1]
      exact (map_one (blockHom hs)).symm
    simpa using congrArg Prod.fst hp
  · have hp : ((a : OGroup (Q.restrict (fixSp s))),
        (1 : OGroup (Q.restrict (commSp s)))) =
        (piOrth (Q.restrict (fixSp s)), piOrth (Q.restrict (commSp s))) := by
      apply blockHom_injective hs
      rw [hpi, blockHom_piOrth_piOrth]
    exact absurd (congrArg Prod.snd hp) (fun h => piOrth_ne_one hU h.symm)

theorem cl_clCommHom_injective (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : 0 < Module.finrank (ZMod 3) (fixSp s)) : Function.Injective (clCommHom hQ hs) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hcoe : toProj Q (blockHom hs (1, (b : OGroup (Q.restrict (commSp s))))) = 1 := by
    have h := congrArg Subtype.val hb
    simpa [coe_clCommHom] using h
  have hmem : blockHom hs (1, (b : OGroup (Q.restrict (commSp s)))) ∈ piGroup Q :=
    (QuotientGroup.eq_one_iff _).mp hcoe
  rcases mem_piGroup_iff.mp hmem with h1 | hpi
  · apply Subtype.ext
    have hp : ((1 : OGroup (Q.restrict (fixSp s))),
        (b : OGroup (Q.restrict (commSp s)))) =
        ((1 : OGroup (Q.restrict (fixSp s))), (1 : OGroup (Q.restrict (commSp s)))) := by
      apply blockHom_injective hs
      rw [h1]
      exact (map_one (blockHom hs)).symm
    simpa using congrArg Prod.snd hp
  · have hp : ((1 : OGroup (Q.restrict (fixSp s))),
        (b : OGroup (Q.restrict (commSp s)))) =
        (piOrth (Q.restrict (fixSp s)), piOrth (Q.restrict (commSp s))) := by
      apply blockHom_injective hs
      rw [hpi, blockHom_piOrth_piOrth]
    exact absurd (congrArg Prod.fst hp) (fun h => piOrth_ne_one hW h.symm)

theorem cl_isSolvable_or_isFStarGroup_omegaGroup (hQ : Q.Nondegenerate)
    (hn : Module.finrank (ZMod 3) V ≤ 7) :
    Group.IsSolvable (omegaGroup hQ) ∨ IsFStarGroup (omegaGroup hQ) := by
  have hcases : Module.finrank (ZMod 3) V ≤ 3 ∨ Module.finrank (ZMod 3) V = 4 ∨
      Module.finrank (ZMod 3) V = 5 ∨ Module.finrank (ZMod 3) V = 6 ∨
      Module.finrank (ZMod 3) V = 7 := by omega
  rcases hcases with hsmall | h4 | h5 | h6 | h7
  · exact Or.inl (cl_isSolvable_omegaGroup_of_small hQ (Or.inl hsmall))
  · rcases Int.units_eq_one_or (quadSign Q) with hs | hs
    · exact Or.inl (cl_isSolvable_omegaGroup_of_small hQ (Or.inr ⟨h4, hs⟩))
    · exact Or.inr (cl_isFStarGroup_omegaGroup_four_minus hQ h4 hs)
  · exact Or.inr (cl_isFStarGroup_omegaGroup_five hQ h5)
  · rcases Int.units_eq_one_or (quadSign Q) with hs | hs
    · exact Or.inr (cl_isFStarGroup_omegaGroup_six_plus hQ h6 hs)
    · exact Or.inr (cl_isFStarGroup_omegaGroup_six_minus hQ h6 hs)
  · exact Or.inr (cl_isFStarGroup_omegaGroup_seven hQ h7)

theorem cl_inFStar_of_isComponentIn_range {G : Type} [Group G] (hQ : Q.Nondegenerate)
    (hn : Module.finrank (ZMod 3) V ≤ 7) (f : omegaGroup hQ →* G)
    (hf : Function.Injective f) {K : Subgroup G} (hK : IsComponentIn K f.range) : InFStar K := by
  have hns : ¬ Group.IsSolvable (omegaGroup hQ) := by
    intro hsol
    have hsurj : Function.Surjective (f.codRestrict f.range fun x => ⟨x, rfl⟩) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩
    exact hK.not_isSolvable (Group.isSolvable_of_surjective hsurj)
  have hfs : IsFStarGroup (omegaGroup hQ) :=
    (cl_isSolvable_or_isFStarGroup_omegaGroup hQ hn).resolve_left hns
  have hq : CFSG.IsQuasisimple (omegaGroup hQ) := hfs.elim (fun h => h.1) (fun h => h.1)
  have hqf : CFSG.IsQuasisimple ↥f.range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hf) hq
  have hKtop : K = f.range := hK.eq_of_isQuasisimple hqf
  rw [show InFStar K = IsFStarGroup ↥K from rfl, hKtop]
  exact isFStarGroup_of_mulEquiv (MonoidHom.ofInjective hf) hfs

theorem cl_inFStar_of_isComponentIn_fix (hQ : Q.Nondegenerate)
    (hn : Module.finrank (ZMod 3) V ≤ 8) {x : OGroup Q} (hx : x * x = 1)
    (hW : 0 < Module.finrank (ZMod 3) (fixSp x)) (hU : 0 < Module.finrank (ZMod 3) (commSp x))
    {K : Subgroup (omegaProj hQ)} (hK : IsComponentIn K (fixSub (projAut hQ x))) :
    InFStar K := by
  have hdim := finrank_fixSp_add_finrank_commSp (Q := Q) x
  rcases cl_isComponentIn_range_of_fix hQ hx hK with h | h
  · exact cl_inFStar_of_isComponentIn_range (V := fixSp x) (Q := Q.restrict (fixSp x))
      (nondegenerate_restrict_fixSp hQ hx) (by omega) (clFixHom hQ hx)
      (cl_clFixHom_injective hQ hx hU) h
  · exact cl_inFStar_of_isComponentIn_range (V := commSp x) (Q := Q.restrict (commSp x))
      (nondegenerate_restrict_commSp hQ hx) (by omega) (clCommHom hQ hx)
      (cl_clCommHom_injective hQ hx hW) h

end CFSG.OddStandard.SmallF3.Omega
