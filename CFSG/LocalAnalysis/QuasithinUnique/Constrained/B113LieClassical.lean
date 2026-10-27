module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieL5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.B113Lie

theorem l3_overgroups (S : Type) [Group S] [Finite S] (f : ℕ) (_hS : IsSimpleGroup S)
    (hf : 2 ≤ f) (h : StatedClassicalModel S .PSL 3 2 f) : Overgroups S :=
  overgroups_of_forall_sylowFacts fun _ hT => l3_sylowFacts hf h hT

theorem sp4_overgroups (S : Type) [Group S] [Finite S] (f : ℕ) (_hS : IsSimpleGroup S)
    (hf : 2 ≤ f) (h : StatedClassicalModel S .PSp 2 2 f) : Overgroups S :=
  overgroups_of_forall_sylowFacts fun _ hT => sp4_sylowFacts hf h hT

theorem l5_overgroups (S : Type) [Group S] [Finite S] (_hS : IsSimpleGroup S)
    (h : StatedClassicalModel S .PSL 5 2 1) : Overgroups S :=
  overgroups_of_forall_sylowFacts fun _ hT => l5_sylowFacts h hT

end CFSG.QuasithinUnique.Bridge.Over

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.B113Lie

theorem l3_sylowAutTrivial (S : Type) [Group S] [Finite S] (f : ℕ) (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSL 3 2 f) : SylowAutTrivial S :=
  oddAut_of_forall_sylowFacts fun _ hT => l3_sylowFacts hf h hT

theorem sp4_sylowAutTrivial (S : Type) [Group S] [Finite S] (f : ℕ) (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSp 2 2 f) : SylowAutTrivial S :=
  oddAut_of_forall_sylowFacts fun _ hT => sp4_sylowFacts hf h hT

theorem l5_sylowAutTrivial (S : Type) [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 5 2 1) : SylowAutTrivial S :=
  oddAut_of_forall_sylowFacts fun _ hT => l5_sylowFacts h hT

end CFSG.QuasithinUnique.Bridge
