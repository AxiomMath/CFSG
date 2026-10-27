module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClKL2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClGroup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_cent_of_split (hQ : Q.Nondegenerate)
    (hn : Module.finrank (ZMod 3) V = 5 ∨ Module.finrank (ZMod 3) V = 6) (S : FGSplit Q)
    (hdim : Module.finrank (ZMod 3) S.W + Module.finrank (ZMod 3) S.P =
      Module.finrank (ZMod 3) V) (hP : 0 < Module.finrank (ZMod 3) S.P)
    (hsign : quadSign Q = quadSign (Q.restrict S.W) * quadSign (Q.restrict S.P) *
      (-1) ^ (Module.finrank (ZMod 3) S.W * Module.finrank (ZMod 3) S.P))
    (f : omegaGroup S.nondegW →* omegaProj hQ)
    (hf : ∀ a, ((f a : omegaProj hQ) : ProjOrth Q) = toProj Q (S.extW a))
    (hfinj : Function.Injective f) {J : Subgroup (omegaProj hQ)} (hJ : IsComponentIn J f.range)
    {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q))
    (hyp62 : Module.finrank (ZMod 3) V = 6 → quadSign Q = 1 →
      ∀ a ∈ A, SimInGStar a → SimInOmegaStar hQ a) :
    Nat.card A ≤ 2 ∨
      (Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 ∧ LieModel ↥J .PSL 2 3 2 ∧
        Nonempty (↥A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = 1 ∧ LieModel ↥J .PSL 2 3 2 ∧
        Nonempty (↥A ≃* Multiplicative (ZMod 4))) := by
  have hW7 : Module.finrank (ZMod 3) S.W ≤ 7 := by omega
  have hns : ¬ Group.IsSolvable (omegaGroup S.nondegW) := by
    intro hsol
    have hsurj : Function.Surjective (f.codRestrict f.range fun x => ⟨x, rfl⟩) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩
    exact hJ.not_isSolvable (Group.isSolvable_of_surjective hsurj)
  have hfs : IsFStarGroup (omegaGroup S.nondegW) :=
    (cl_isSolvable_or_isFStarGroup_omegaGroup S.nondegW hW7).resolve_left hns
  have hq : CFSG.IsQuasisimple (omegaGroup S.nondegW) := hfs.elim (fun h => h.1) (fun h => h.1)
  have hqf : CFSG.IsQuasisimple ↥f.range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hfinj) hq
  have hJeq : J = f.range := hJ.eq_of_isQuasisimple hqf
  have hW4 : 4 ≤ Module.finrank (ZMod 3) S.W := by
    by_contra hlt
    exact hns (cl_isSolvable_omegaGroup_of_small S.nondegW (Or.inl (by omega)))
  have hW4s : Module.finrank (ZMod 3) S.W = 4 → quadSign (Q.restrict S.W) = -1 := by
    intro h4
    rcases Int.units_eq_one_or (quadSign (Q.restrict S.W)) with hs | hs
    · exact absurd (cl_isSolvable_omegaGroup_of_small S.nondegW (Or.inr ⟨h4, hs⟩)) hns
    · exact hs
  have hperf : Group.IsPerfect (omegaGroup S.nondegW) := hq.1
  have h3 : 3 ≤ Module.finrank (ZMod 3) S.W := by omega
  have hA : ∀ γ ∈ A, ∀ a ∈ omegaGroup S.nondegW,
      projSimAct Q γ (toProj Q (S.extW a)) = toProj Q (S.extW a) := by
    intro γ hγ a ha
    have h := hAJ γ hγ (f ⟨a, ha⟩) (by rw [hJeq]; exact ⟨⟨a, ha⟩, rfl⟩)
    rwa [hf] at h
  rcases (by omega : Module.finrank (ZMod 3) S.P = 1 ∨ Module.finrank (ZMod 3) S.P = 2)
    with hP1 | hP2
  · exact Or.inl (fg_cent_dim_one S h3 hperf hA hP1)
  · have hV6 : Module.finrank (ZMod 3) V = 6 := by omega
    have hW4' : Module.finrank (ZMod 3) S.W = 4 := by omega
    have hsW := hW4s hW4'
    have hLie : LieModel ↥J .PSL 2 3 2 := by
      rw [hJeq]
      exact LieModel.of_mulEquiv (MonoidHom.ofInjective hfinj)
        (lieModel_omegaGroup_four_minus S.nondegW hW4' hsW)
    rw [hsW, hW4', hP2] at hsign
    rcases Int.units_eq_one_or (quadSign (Q.restrict S.P)) with hp | hp
    · have hQs : quadSign Q = -1 := by rw [hsign, hp]; decide
      rcases fg_cent_two_plus S h3 hperf hA hP2 hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hV6, hQs, hLie, h⟩)
    · have hQs : quadSign Q = 1 := by rw [hsign, hp]; decide
      have hdet : ∀ b : OGroup (Q.restrict S.P), fgIotaP S b ∈ A →
          QuadraticMap.orthogonalDet (Q.restrict S.P) b = 1 := fun b hb =>
        fg_det_of_simInOmegaStar hQ S (by rw [hV6]; exact ⟨3, rfl⟩) b
          (hyp62 hV6 hQs _ hb ⟨toProj Q (S.extP b), rfl⟩)
      rcases fg_cent_two_minus S h3 hperf hA hP2 hp hdet with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hV6, hQs, hLie, h⟩)

theorem fg_cent_invol (hQ : Q.Nondegenerate)
    (hn : Module.finrank (ZMod 3) V = 5 ∨ Module.finrank (ZMod 3) V = 6) {s : OGroup Q}
    (hs : s * s = 1) (hF : 0 < Module.finrank (ZMod 3) (fixSp s))
    (hC : 0 < Module.finrank (ZMod 3) (commSp s)) {J : Subgroup (omegaProj hQ)}
    (hJ : IsComponentIn J (fixSub (projAut hQ s))) {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q))
    (hyp62 : Module.finrank (ZMod 3) V = 6 → quadSign Q = 1 →
      ∀ a ∈ A, SimInGStar a → SimInOmegaStar hQ a) :
    Nat.card A ≤ 2 ∨
      (Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 ∧ LieModel ↥J .PSL 2 3 2 ∧
        Nonempty (↥A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = 1 ∧ LieModel ↥J .PSL 2 3 2 ∧
        Nonempty (↥A ≃* Multiplicative (ZMod 4))) := by
  have hdimFC := finrank_fixSp_add_finrank_commSp (Q := Q) s
  rcases cl_isComponentIn_range_of_fix hQ hs hJ with h | h
  · exact fg_cent_of_split hQ hn (FGSplit.fix hQ hs) hdimFC hC (quadSign_eq_fixSp_commSp hQ hs)
      (clFixHom hQ hs) (fun a => coe_clFixHom hQ hs a) (cl_clFixHom_injective hQ hs hC) h hAJ
      hyp62
  · refine fg_cent_of_split hQ hn (FGSplit.comm hQ hs)
      (by show Module.finrank (ZMod 3) (commSp s) + Module.finrank (ZMod 3) (fixSp s) = _
          omega) hF ?_ (clCommHom hQ hs) (fun b => coe_clCommHom hQ hs b)
      (cl_clCommHom_injective hQ hs hF) h hAJ hyp62
    show quadSign Q = quadSign (Q.restrict (commSp s)) * quadSign (Q.restrict (fixSp s)) *
      (-1) ^ (Module.finrank (ZMod 3) (commSp s) * Module.finrank (ZMod 3) (fixSp s))
    rw [mul_comm (quadSign (Q.restrict (commSp s))), Nat.mul_comm]
    exact quadSign_eq_fixSp_commSp hQ hs

end CFSG.OddStandard.SmallF3.Omega
