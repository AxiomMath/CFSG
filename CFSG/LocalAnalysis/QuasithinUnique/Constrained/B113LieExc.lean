module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieG2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieF4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieTits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Blueprint CFSG.QuasithinUnique.B113Lie

theorem g2_overgroups
    (S : Type) [Group S] [Finite S] (f : ℕ) (_hS : IsSimpleGroup S)
    (_hf : 2 ≤ f) (h : ChevalleyExceptionalModel S .G2 2 f) : Overgroups S :=
  overgroups_of_forall_sylowFacts fun _ hT => g2_sylowFacts h hT

theorem d4_overgroups
    (S : Type) [Group S] [Finite S] (f : ℕ) (_hS : IsSimpleGroup S)
    (hf : 1 ≤ f) (h : ChevalleyExceptionalModel S .trialityD4 2 f) : Overgroups S :=
  overgroups_of_forall_sylowFacts fun _ hT => d4_sylowFacts hf h hT

theorem f4_overgroups
    (S : Type) [Group S] [Finite S] (f : ℕ) (_hS : IsSimpleGroup S)
    (hodd : Odd f) (hf : 3 ≤ f) (h : ReeTitsModel S .twistedF4 2 f) : Overgroups S :=
  overgroups_of_forall_sylowFacts fun _ hT => f4_sylowFacts hodd hf h hT

theorem tits_overgroups
    (S : Type) [Group S] [Finite S] (_hS : IsSimpleGroup S)
    (h : ReeTitsModel S .Tits 2 1) : Overgroups S :=
  overgroups_of_forall_sylowFacts fun _ hT => tits_sylowFacts h hT

end CFSG.QuasithinUnique.Bridge.Over

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Blueprint CFSG.QuasithinUnique.B113Lie

theorem g2_sylowAutTrivial
    (S : Type) [Group S] [Finite S] (f : ℕ) (_hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : SylowAutTrivial S :=
  oddAut_of_forall_sylowFacts fun _ hT => g2_sylowFacts h hT

theorem d4_sylowAutTrivial
    (S : Type) [Group S] [Finite S] (f : ℕ) (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : SylowAutTrivial S :=
  oddAut_of_forall_sylowFacts fun _ hT => d4_sylowFacts hf h hT

theorem f4_sylowAutTrivial
    (S : Type) [Group S] [Finite S] (f : ℕ) (hodd : Odd f) (hf : 3 ≤ f)
    (h : ReeTitsModel S .twistedF4 2 f) : SylowAutTrivial S :=
  oddAut_of_forall_sylowFacts fun _ hT => f4_sylowFacts hodd hf h hT

theorem tits_sylowAutTrivial
    (S : Type) [Group S] [Finite S] (h : ReeTitsModel S .Tits 2 1) :
    SylowAutTrivial S :=
  oddAut_of_forall_sylowFacts fun _ hT => tits_sylowFacts h hT

end CFSG.QuasithinUnique.Bridge
