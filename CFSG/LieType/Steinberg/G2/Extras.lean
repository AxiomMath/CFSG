module

public import CFSG.LieType.Steinberg.Adjoint.CommAll
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.Steinberg.G2.RankOne

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.TitsSimplicity

@[expose] def cartanInvG2 : Matrix (Fin (Tag.rank .G2)) (Fin (Tag.rank .G2)) ℤ :=
  !![2, 1; 3, 2]

theorem cartan_mul_cartanInvG2 : Tag.cartan .G2 * cartanInvG2 = 1 := by
  decide +kernel

variable (K : Type) [Field K]

abbrev g2Datum :
    UniversalRootDatum ↥(adjointGroup .G2 K) :=
  adjDatum (rootOperatorFamily .G2) K

theorem g2_isCTGroupDatum :
    CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (g2Datum K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (g2Datum K).isFiniteType) (g2Datum K).roots
      (g2Datum K).rootGroup (CFSG.LieType.Chevalley.weylElement .G2 K) (torus (τ := .G2) K) :=
  adjDatum_isCTGroupDatum _ K

theorem g2_steinbergExtras :
    SteinbergExtras (g2Datum K) (CFSG.LieType.Chevalley.weylElement .G2 K)
      (torus (τ := .G2) K) :=
  steinbergExtras_of_normalizer K (fun i _ hu hn => g2_eq_one_of_mem_normalizer i hu hn)
    cartan_mul_cartanInvG2

theorem g2_bruhatExtras
    : BruhatExtras (g2Datum K) (torus (τ := .G2) K) :=
  adjDatum_bruhatExtras _ K

theorem g2_rootGroupCommutators
    : RootGroupCommutators (g2Datum K) :=
  rootGroupCommutators_adjDatum

end CFSG.LieType.Steinberg.Adjoint
