module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGUMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open Polynomial

section Centralizer

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem oddPCoreInClosure_unitaryCentralizer_of_squarefree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ = 2) (hK : UnitaryFieldData ℓ f K) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {x : LinearMap.GeneralLinearGroup K V} (hx : x ∈ sesqUnitaryGroup B)
    (hsq : Squarefree (minpoly K (x : Module.End K V))) :
    OddPCoreInClosure p ↥(unitaryCentralizer B x) := by
  classical
  haveI : Finite K := hK.finite
  haveI : CharP K 2 := hℓ ▸ hK.charP
  have HA := r3e_unitary_semisimple_primary_algebra_and_full_centralizer hK B hB hBl x hx hsq
  haveI : Finite (LinearMap.GeneralLinearGroup K V) := finite_generalLinearGroup'
  have hfin : Finite ↥(adjointOrbits hK x) := by
    have : (adjointOrbits hK x).Finite := Set.Finite.image _ (Finset.finite_toSet _)
    exact this.to_subtype
  obtain ⟨hcomm, hind, hsup⟩ := HA.directProduct
  have hprod := OddPCoreInClosure.of_noncommPiCoprod hp
    (fun O : ↥(adjointOrbits hK x) => supportedUnitary B x (O : Set K[X]))
    (fun i j hij g g' hg hg' => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) g hg g' hg')
    hind ?_
  · exact OddPCoreInClosure.of_mulEquiv (MulEquiv.subgroupCongr hsup) hprod
  · rintro ⟨O, a, ha, rfl⟩
    by_cases hself : dualPoly hK.bar a = a
    ·
      obtain ⟨hE, -, -, Hf, hHf, hHfl, -, -, φ, -⟩ := (HA.selfDual ⟨a, ha⟩ hself).unitaryForm
      haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
      haveI : Finite (AdjoinRoot a) := Module.finite_of_finite K
      haveI : CharP (AdjoinRoot a) 2 := charP_of_injective_ringHom (AdjoinRoot.of a).injective 2
      have h1 : OddPCoreInClosure p ↥(supportedUnitary B x {a}) :=
        OddPCoreInClosure.of_mulEquiv φ.symm (oddPCoreInClosure_sesqUnitaryGroup hp hp2 hℓ hHf hHfl)
      have hset : ({a, dualPoly hK.bar a} : Set K[X]) = {a} := by
        rw [hself, Set.pair_eq_singleton]
      exact OddPCoreInClosure.of_mulEquiv
        (MulEquiv.subgroupCongr (congrArg (supportedUnitary B x) hset.symm)) h1
    ·
      obtain ⟨φ, -, -, -, -, -⟩ := (HA.paired ⟨a, ha⟩ (Ne.symm hself)).factor
      haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
      haveI : Finite (AdjoinRoot a) := Module.finite_of_finite K
      haveI : CharP (AdjoinRoot a) 2 := charP_of_injective_ringHom (AdjoinRoot.of a).injective 2
      exact OddPCoreInClosure.of_mulEquiv φ.symm (oddPCoreInClosure_generalLinearGroup hp hp2)

end Centralizer

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
