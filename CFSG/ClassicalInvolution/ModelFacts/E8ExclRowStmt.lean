module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.NonClassical (PerpTableR)

variable (p f : ℕ) [Fact p.Prime]

abbrev Fund12 : Type :=
  {R : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K //
    R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D}

abbrev D8Layer : Type := Option (Option (Fund12 p f))

@[expose] def D8Layer.rel : D8Layer p f → D8Layer p f → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some none, some none => False
  | some none, some (some _) => True
  | some (some _), some none => True
  | some (some R), some (some R') => Commutes R.1 R'.1

@[expose] def E8D8NoThreeAdj : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → D8NoThreeAdjPairs p .POmegaPlus 8 f

@[expose] def E8D8Row' : Prop :=
  PerpTableR p f (D8Layer.rel p f) none .POmegaPlus 8

end CFSG.ClassicalInvolution.RouteD.TypeE8
