module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentSmall

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem lo4_psl_two {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) : SylowProps X :=
  ⟨CFSG.QuasithinUnique.Bridge.Over.overgroups_isPSL_two h,
    CFSG.QuasithinUnique.Bridge.sylowAutTrivial_isPSL_two h⟩

theorem lo4_psl_three {X : Type} [Group X] [Finite X] (hS : IsSimpleGroup X) {f : ℕ}
    (hf : 2 ≤ f) (h : StatedClassicalModel X .PSL 3 2 f) : SylowProps X :=
  ⟨CFSG.QuasithinUnique.Bridge.Over.l3_overgroups X f hS hf h,
    CFSG.QuasithinUnique.Bridge.l3_sylowAutTrivial X f hf h⟩

theorem lo4_psl_three_two
    {X : Type} [Group X] [Finite X]
    (h : StatedClassicalModel X .PSL 3 2 1) : SylowProps X :=
  ⟨CFSG.QuasithinUnique.Bridge.Over.overgroups_psl_three_two h,
    CFSG.QuasithinUnique.Bridge.sylowAutTrivial_psl_three_two h⟩

theorem asLieTwoAt_psl_of
    (h4 : AsLieTwoPSLGe4) : AsLieTwoAt .PSL := by
  intro n f X _ _ hS hadm hmod
  have hmc : StatedClassicalModel X .PSL n 2 f := hmod.statedClassicalModel (by decide)
  have hn : 2 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · interval_cases n
    · exact lo4_psl_two hmc
    · rcases Nat.lt_or_ge f 2 with hf2 | hf2
      · obtain rfl : f = 1 := by omega
        exact lo4_psl_three_two hmc
      · exact lo4_psl_three hS hf2 hmc
  · exact h4 n f X hn4 hS hadm hmod

private theorem lo5_two_le_psu (f : ℕ) (hadm : StatedLieAdmissible .PSU 3 2 f) : 2 ≤ f := by
  by_contra hf
  have h1 : f = 1 := by
    have := hadm.2.1
    omega
  subst h1
  exact hadm.2.2.2 rfl

private theorem lo5_two_le_psp (f : ℕ) (hadm : StatedLieAdmissible .PSp 2 2 f) : 2 ≤ f := by
  by_contra hf
  have h1 : f = 1 := by
    have := hadm.2.1
    omega
  subst h1
  exact hadm.2.2.2 rfl

theorem asLieTwoAt_psu_of (h4 : AsLieTwoPSUGe4) : AsLieTwoAt .PSU := by
  intro n f X _ _ hS hadm hmod
  rcases Nat.lt_or_ge n 4 with hn | hn
  · have hn3 : n = 3 := by
      have := hadm.2.2.1
      omega
    subst hn3
    have hcl : StatedClassicalModel X .PSU 3 2 f :=
      LieModel.statedClassicalModel hmod (by decide)
    have hf : 2 ≤ f := lo5_two_le_psu f hadm
    exact And.intro (CFSG.QuasithinUnique.Bridge.Over.overgroups_isPSU_three hf hcl)
      (CFSG.QuasithinUnique.Bridge.sylowAutTrivial_isPSU_three hf hcl)
  · exact h4 n f X hn hS hadm hmod

theorem asLieTwoAt_psp_of (h3 : AsLieTwoPSpGe3) : AsLieTwoAt .PSp := by
  intro n f X _ _ hS hadm hmod
  rcases Nat.lt_or_ge n 3 with hn | hn
  · have hn2 : n = 2 := by
      have := hadm.2.2.1
      omega
    subst hn2
    have hcl : StatedClassicalModel X .PSp 2 2 f :=
      LieModel.statedClassicalModel hmod (by decide)
    have hf : 2 ≤ f := lo5_two_le_psp f hadm
    exact And.intro (CFSG.QuasithinUnique.Bridge.Over.sp4_overgroups X f hS hf hcl)
      (CFSG.QuasithinUnique.Bridge.sp4_sylowAutTrivial X f hf hcl)
  · exact h3 n f X hn hS hadm hmod

end CFSG.Quasithin.LieOver
