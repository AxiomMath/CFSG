module

public import CFSG.ClassicalInvolution.Q3.Q3WACore
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem nonempty_extModel3_E6 (hadm : StatedLieAdmissible .E6 0 3 1) :
    Nonempty (ExtModel3 .E6 0 .PSL 6 1) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadmY : StatedLieAdmissible .PSL 6 3 1 := ⟨hp, le_rfl, by norm_num, by simp, by simp⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E6 0 3 1 hp trivial hadm
  set D := (modelUniv .E6 0 3 1 Nat.prime_three).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E6 0 3 1 hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 6; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta6 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta6
  have hRθ := fund_of_longest (t := .E6) D (isLongestRoot_of_lenSq D hℓ hθ)
  have hlong : ∀ k, CFSG.ClassicalInvolution.Generic.IsLongestRoot D (Pi.single k 1) :=
    fun k => isLongestRoot_of_lenSq D hℓ (single_mem_roots D k)
  obtain ⟨ψ, hψker, hψrange, hψblk⟩ := exists_psi_of_chain3 (K := GaloisField 3 1) card_gf3
    (m := 3) (by norm_num) (G := (modelUniv .E6 0 3 1 Nat.prime_three).K)
    (U := fun i => rankOne D.rootGroup (path6 i))
    (fun i j hij => commutes_rankOne_of_cartan_eq_zero D hext hℓ (path6_comm i j hij))
    (fun i j hij => stdPair_edge_E6 (path6_edge i j hij))
  let y0 : Fin (modelUniv .PSL 6 3 1 Nat.prime_three).D.rank := ⟨0, by show 0 < 5; decide⟩
  obtain ⟨W₀, hW₀⟩ := stdPair_edge_E6 (F := GaloisField 3 1) (i := 0) (j := 2) (by decide)
  let Θ : (modelUniv .PSL 6 3 1 Nat.prime_three).K →* (modelUniv .E6 0 3 1 Nat.prime_three).K := ψ
  have hΘker : Θ.ker ≤ Subgroup.center (modelUniv .PSL 6 3 1 Nat.prime_three).K := hψker
  have hΘrange : Θ.range = ⨆ i, rankOne D.rootGroup (path6 i) := hψrange
  have hRY : rankOne (modelUniv .PSL 6 3 1 Nat.prime_three).D.rootGroup y0 =
      (WeakCT.blockSL2 (GaloisField 3 1) 5 0).range :=
    WeakCT.rankOne_eq_range (K := GaloisField 3 1) (n := 5) 0
  have hΘ₀ : (rankOne (modelUniv .PSL 6 3 1 Nat.prime_three).D.rootGroup y0).map Θ =
      rankOne D.rootGroup (path6 0) := by
    rw [hRY]
    exact hψblk 0
  have hcopT : ∀ w ∈ Subgroup.center (modelUniv .E6 0 3 1 Nat.prime_three).K,
      ¬ 3 ∣ orderOf w := by
    intro w hw
    have hcard := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (k := GaloisField 3 1)).1
    rw [card_gf3] at hcard
    have hw' : w ∈ Subgroup.center
        (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 3 1)) := hw
    have hd : orderOf w ∣ Nat.gcd 3 (3 - 1) :=
      (Subgroup.orderOf_dvd_natCard _ hw').trans (dvd_of_eq hcard)
    have h1 : orderOf w = 1 := Nat.dvd_one.mp (by simpa using hd)
    omega
  have hcopY : ∀ w ∈ Subgroup.center (modelUniv .PSL 6 3 1 Nat.prime_three).K,
      ¬ 3 ∣ orderOf w := fun w hw =>
    orderOf_not_dvd_three_of_center card_gf3 (by norm_num : 1 ≤ 6) hw
  refine nonempty_extModel3U_one
    (ModelFacts.fundamentalSingleClass .E6 0 3 1 hp trivial hadm (by decide) (by decide))
    (ModelFacts.fundamentalSingleClass .PSL 6 3 1 hp trivial hadmY (by decide) (by decide))
    (rankOne_mem_fundamental D (hlong z0)) (pow3_of_stdPair card_gf3 hW₀).1
    (R₀Y := rankOne (modelUniv .PSL 6 3 1 Nat.prime_three).D.rootGroup y0)
    (rankOne_mem_fundamental _
      (ModelFacts.isLongestRoot_single .PSL 6 3 1 hp trivial hadmY y0 trivial))
    ?_ hRθ Θ hΘker ?_ ?_ hcopT hcopY
  · rw [hRY]
    exact pow3_range_sl2 card_gf3 _
  · rw [hΘ₀]
    exact rankOne_mem_fundamental D (hlong (path6 0))
  · rw [hΘrange]
    refine commutes_iSup_left.mpr fun i => ?_
    exact commutes_rankOne_theta D hext hℓ hθ (k := path6 i)
      ((coroot_apply D.cartan (path6 i) theta6).trans (coroot_theta6 _ (path6_ne i)))

end CFSG.ClassicalInvolution.Q3.Q3W
