module

public import CFSG.ClassicalInvolution.Q3.Q3WAE78
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE8Layer
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.ModelFacts (E7sc stdRankOne)
open CFSG.Blueprint.Chevalley (Tag)
open CFSG.ClassicalInvolution.ModelFacts.Levi (thetaE8 thetaE8_eq)
open CFSG.ClassicalInvolution.Q3.Q3W (exists_psi_E7_3)


theorem exists_thetaE8 (hadm : StatedLieAdmissible .E8 0 3 1) :
    ∃ Θ : E7sc 3 1 →* ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 3 1)),
      Θ.ker ≤ Subgroup.center (E7sc 3 1) ∧ Θ.range = layerE7 (GaloisField 3 1) ∧
      ∀ x ∈ layerE7 (GaloisField 3 1),
        ∀ r ∈ stdRankOne (CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 3 1)) thetaE8,
          x * r = r * x := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadmY : StatedLieAdmissible .E7 0 3 1 := ⟨hp, le_rfl, rfl⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E8 0 3 1 hp trivial hadm
  set D := (modelUniv .E8 0 3 1 Nat.prime_three).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E8 0 3 1 hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 8; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta8 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta8
  obtain ⟨ψ, hψker, hψrange, -⟩ := exists_psi_E7_3 hadmY
    (X := (modelUniv .E8 0 3 1 Nat.prime_three).K)
    (fun i : Fin 7 => rankOne D.rootGroup i.castSucc)
    (fun i j hij h1 h2 =>
      commutes_rankOne_of_cartan_eq_zero D hext hℓ (castSucc_comm i j hij h1 h2))
    (fun i j h => stdPair_edge_E8 (castSucc_edge i j h))
  have hcomm : Commutes (⨆ i : Fin 7, rankOne D.rootGroup i.castSucc)
      (D.rootGroup theta8 ⊔ D.rootGroup (-theta8)) := by
    refine commutes_iSup_left.mpr fun i : Fin 7 => ?_
    exact commutes_rankOne_theta D hext hℓ hθ (k := i.castSucc)
      ((coroot_apply D.cartan i.castSucc theta8).trans (coroot_theta8 _ (castSucc_ne i)))
  refine ⟨ψ, hψker, hψrange, ?_⟩
  intro x hx r hr
  have hthe : (thetaE8 : Fin (Tag.rank .E8) → ℤ) = theta8 := thetaE8_eq
  have hr' : r ∈ D.rootGroup theta8 ⊔ D.rootGroup (-theta8) := by
    rw [← hthe]
    exact hr
  exact hcomm x hx r hr'

end CFSG.OddStandard.HigherRank.F3
