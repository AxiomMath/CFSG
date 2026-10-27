
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InBCheck
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKleinInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Sporadic.Th.Setup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Bridge CFSG.Perm
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

@[expose] noncomputable def compInv {P N K : Type*} [Group P] [Group N] [Group K] (f : P →* N)
    (hf : Function.Bijective f) (g : P →* K) : N →* K :=
  g.comp (MulEquiv.ofBijective f hf).symm.toMonoidHom

theorem compInv_apply {P N K : Type*} [Group P] [Group N] [Group K] (f : P →* N)
    (hf : Function.Bijective f) (g : P →* K) (x : P) : compInv f hf g (f x) = g x := by
  show g ((MulEquiv.ofBijective f hf).symm (MulEquiv.ofBijective f hf x)) = g x
  rw [MulEquiv.symm_apply_apply]

end Generic

section Phi

theorem toJ_bijective : Function.Bijective Fi23.toJ := by
  have hfin := CFSG.Sporadic.Presentation.Fi23.finite_card_le
  have : Finite TauCeti.Sporadic.fi23Presentation.Group := hfin.1
  refine Fi23.toJ_surjective.bijective_of_nat_card_le ?_
  rw [card_J]
  exact hfin.2

theorem toJ_presGen {k : ℕ} (hk : k < 10) :
    Fi23.toJ (presGen TauCeti.Sporadic.fi23Presentation k) = Fi23.img k := by
  rw [Fi23.toJ, presHom_presGen _ _ _ (by rw [Fi23.generatorCount_eq]; exact hk)]

noncomputable def toB' : TauCeti.Sporadic.fi23Presentation.Group →* Fi23InB.SMˣ :=
  Fi23InB.toB

theorem toB'_presGen {k : ℕ} (hk : k < 10) :
    toB' (presGen TauCeti.Sporadic.fi23Presentation k) = Fi23InB.img k := by
  show Fi23InB.toB (presGen TauCeti.SporadicName.Fi23.presentation k) = _
  rw [Fi23InB.toB, presHom_presGen _ _ _
    (by rw [show TauCeti.SporadicName.Fi23.presentation = TauCeti.Sporadic.fi23Presentation
      from rfl, Fi23.generatorCount_eq]; exact hk)]

@[expose] noncomputable def phiB : CFSG.Sporadic.Fi23.J →* CFSG.Blueprint.NativeSporadic.B :=
  compInv Fi23.toJ toJ_bijective toB'

theorem phiB_img {k : ℕ} (hk : k < 10) : phiB (Fi23.img k) = Fi23InB.img k := by
  rw [← toJ_presGen hk, phiB, compInv_apply]
  exact toB'_presGen hk

theorem phiB_injective : Function.Injective phiB := by
  have : IsSimpleGroup CFSG.Sporadic.Fi23.J := CFSG.Sporadic.Fi23.isSimpleGroup_J
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal phiB.ker with h | h
  · exact h
  · exfalso
    have hmem : Fi23.img 0 ∈ phiB.ker := by rw [h]; trivial
    rw [MonoidHom.mem_ker, phiB_img (by norm_num)] at hmem
    exact Fi23InB.img_zero_ne_one hmem

end Phi

section Reps

@[expose] noncomputable def zJ : CFSG.Sporadic.Fi23.J := (Fi23Native.kleinZ.map (pairG gs)).prod

@[expose] noncomputable def t3 : Fin 4 → CFSG.Sporadic.Fi23.J :=
  ![Fi23.img 2 * Fi23.img 3, zJ, Fi23.img 4 * Fi23.img 5 * Fi23.img 2 * Fi23.img 1,
    Fi23.img 5 * Fi23.img 3 * Fi23.img 7 * Fi23.img 0 * Fi23.img 6 * Fi23.img 1]

end Reps

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
