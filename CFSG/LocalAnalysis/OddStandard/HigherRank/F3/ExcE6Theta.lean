module

public import CFSG.ClassicalInvolution.Q3.Q3WAE6
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution
open CFSG.Open (StatedLieAdmissible)
open scoped MatrixGroups

theorem e6Isogeny_injective_three :
    Function.Injective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 3 1)) := by
  have hZ : Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 3 1)) = ⊥ := by
    have h1 := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (GaloisField 3 1)).1
    rw [card_gf3] at h1
    have h2 : Nat.gcd 3 (3 - 1) = 1 := by norm_num
    rw [h2] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  rw [← MonoidHom.ker_eq_bot_iff,
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, hZ]

theorem center_e6_three_eq_bot :
    Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 3 1)) = ⊥ := by
  rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
  exact (MonoidHom.ker_eq_bot_iff _).2 e6Isogeny_injective_three

theorem exists_theta_e6 :
    ∃ Θ : SL(6, GaloisField 3 1) →* (modelUniv .E6 0 3 1 Nat.prime_three).K,
      Θ.ker ≤ Subgroup.center SL(6, GaloisField 3 1) ∧
      Θ.range = ⨆ i : Fin 5,
        rankOne (modelUniv .E6 0 3 1 Nat.prime_three).D.rootGroup (path6 i) ∧
      ∀ i : Fin 5, (WeakCT.blockSL2 (GaloisField 3 1) 5 i).range.map Θ =
        rankOne (modelUniv .E6 0 3 1 Nat.prime_three).D.rootGroup (path6 i) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .E6 0 3 1 := ⟨hp, le_rfl, rfl⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E6 0 3 1 hp trivial hadm
  set D := (modelUniv .E6 0 3 1 Nat.prime_three).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E6 0 3 1 hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 6; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  obtain ⟨ψ, hψker, hψrange, hψblk⟩ := exists_psi_of_chain3 (K := GaloisField 3 1) card_gf3
    (m := 3) (by norm_num) (G := (modelUniv .E6 0 3 1 Nat.prime_three).K)
    (U := fun i => rankOne D.rootGroup (path6 i))
    (fun i j hij => commutes_rankOne_of_cartan_eq_zero D hext hℓ (path6_comm i j hij))
    (fun i j hij => stdPair_edge_E6 (path6_edge i j hij))
  exact ⟨ψ, hψker, hψrange, hψblk⟩

theorem commutes_iSup_rankOne_theta_e6 :
    Commutes (⨆ i : Fin 5, rankOne (modelUniv .E6 0 3 1 Nat.prime_three).D.rootGroup (path6 i))
      ((modelUniv .E6 0 3 1 Nat.prime_three).D.rootGroup theta6 ⊔
        (modelUniv .E6 0 3 1 Nat.prime_three).D.rootGroup (-theta6)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .E6 0 3 1 := ⟨hp, le_rfl, rfl⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E6 0 3 1 hp trivial hadm
  set D := (modelUniv .E6 0 3 1 Nat.prime_three).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E6 0 3 1 hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 6; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta6 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta6
  refine commutes_iSup_left.mpr fun i => ?_
  exact commutes_rankOne_theta D hext hℓ hθ (k := path6 i)
    ((coroot_apply D.cartan (path6 i) theta6).trans (coroot_theta6 _ (path6_ne i)))

end CFSG.OddStandard.HigherRank.F3
