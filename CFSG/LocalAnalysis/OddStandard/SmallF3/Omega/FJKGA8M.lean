module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAEng
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGA8Cls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGA8K4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimFaith
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeHigh

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fjKGAAt_omegaProj_eight_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = -1)
    (hsurj : Function.Surjective (ffSimOmegaAct hQ (by omega) : ProjSim Q →* _))
    (h53 : ∀ (s : OGroup Q) (hs : s * s = 1), Fj53 hQ hs) : FJKGAAt ↥(omegaProj hQ) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite ↥(omegaGroup hQ) := Subtype.finite
  have hinj : Function.Injective (ffSimOmegaAct hQ h2 : ProjSim Q →* _) :=
    ffSimOmegaAct_injective hQ (by omega)
  intro y B hy hB α hαα hα1 hfix hαy
  obtain ⟨x, rfl⟩ := hsurj α
  have hx2 : x * x = 1 := hinj (by rw [map_mul, map_one]; exact hαα)
  rcases fj_involution_cases_eight_minus hQ hdim hs h2 hx2 with ⟨s, hs2, hxs⟩ | ⟨ρ, hρx, hρ, hρρ⟩
  · rw [hxs] at hα1 hfix hαy ⊢
    obtain ⟨J, hJ, hJF, hBJ⟩ := fj_kga_engine hQ (by omega) hs2 (h53 s hs2) hα1 hy hB hfix hαy
    exact ⟨J, by rw [l34g_fix_eq_fixSub]; exact hJ, hJF, hBJ⟩
  · exfalso
    subst hρx
    exact fj_no_pocket_negsim hQ hdim h2 hρ hρρ hy hB hfix

theorem fjKGAAt_of_lieModel_minus {Y : Type} [Group Y] (h : LieModel Y .POmegaMinus 4 3 1)
    (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = -1)
    (hsurj : Function.Surjective (ffSimOmegaAct hQ (by omega) : ProjSim Q →* _))
    (h53 : ∀ (s : OGroup Q) (hs : s * s = 1), Fj53 hQ hs) : FJKGAAt Y := by
  obtain ⟨f⟩ := (isOmegaStar_of_lieModel_minus h).nonempty_equiv (by norm_num : 2 ≤ 8) hQ hdim hs
  exact fjKGAAt_of_mulEquiv f.symm (fjKGAAt_omegaProj_eight_minus hQ hdim hs hsurj h53)

end CFSG.OddStandard.SmallF3.Omega
