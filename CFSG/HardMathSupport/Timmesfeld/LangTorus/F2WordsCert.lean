module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words

set_option maxRecDepth 200000 in
theorem certCheck_E6 : certCheck .E6 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem certCheck_E7 : certCheck .E7 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem certCheck_E8 : certCheck .E8 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by decide +kernel


open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem commute_xOp_yOp_E7 {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    (z : Module.End R (RootModule Tag.E7 R))
    (hxj : Commute z (xOp Tag.E7 R ⟨0, by decide⟩ 1)) (hyj : Commute z (yOp Tag.E7 R ⟨0, by decide⟩ 1))
    (hxk : Commute z (xOp Tag.E7 R ⟨2, by decide⟩ 1)) (hyk : Commute z (yOp Tag.E7 R ⟨2, by decide⟩ 1))
    (c : R) :
    Commute z (xOp Tag.E7 R ⟨0, by decide⟩ c) ∧ Commute z (yOp Tag.E7 R ⟨0, by decide⟩ c) ∧
      Commute z (xOp Tag.E7 R ⟨2, by decide⟩ c) ∧ Commute z (yOp Tag.E7 R ⟨2, by decide⟩ c) :=
  commute_xOp_yOp_of_certCheck (RootOps.dataChecks Tag.E7) certCheck_E7 h2 z hxj hyj hxk hyk c

theorem commute_xOp_yOp_E8 {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    (z : Module.End R (RootModule Tag.E8 R))
    (hxj : Commute z (xOp Tag.E8 R ⟨0, by decide⟩ 1)) (hyj : Commute z (yOp Tag.E8 R ⟨0, by decide⟩ 1))
    (hxk : Commute z (xOp Tag.E8 R ⟨2, by decide⟩ 1)) (hyk : Commute z (yOp Tag.E8 R ⟨2, by decide⟩ 1))
    (c : R) :
    Commute z (xOp Tag.E8 R ⟨0, by decide⟩ c) ∧ Commute z (yOp Tag.E8 R ⟨0, by decide⟩ c) ∧
      Commute z (xOp Tag.E8 R ⟨2, by decide⟩ c) ∧ Commute z (yOp Tag.E8 R ⟨2, by decide⟩ c) :=
  commute_xOp_yOp_of_certCheck (RootOps.dataChecks Tag.E8) certCheck_E8 h2 z hxj hyj hxk hyk c

theorem commute_xOp_yOp_E6 {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    (z : Module.End R (RootModule Tag.E6 R))
    (hxj : Commute z (xOp Tag.E6 R ⟨0, by decide⟩ 1)) (hyj : Commute z (yOp Tag.E6 R ⟨0, by decide⟩ 1))
    (hxk : Commute z (xOp Tag.E6 R ⟨2, by decide⟩ 1)) (hyk : Commute z (yOp Tag.E6 R ⟨2, by decide⟩ 1))
    (c : R) :
    Commute z (xOp Tag.E6 R ⟨0, by decide⟩ c) ∧ Commute z (yOp Tag.E6 R ⟨0, by decide⟩ c) ∧
      Commute z (xOp Tag.E6 R ⟨2, by decide⟩ c) ∧ Commute z (yOp Tag.E6 R ⟨2, by decide⟩ c) :=
  commute_xOp_yOp_of_certCheck (RootOps.dataChecks Tag.E6) certCheck_E6 h2 z hxj hyj hxk hyk c

end CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words
