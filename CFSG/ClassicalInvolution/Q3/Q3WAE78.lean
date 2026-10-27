module

public import CFSG.ClassicalInvolution.Q3.Q3WATwinDRow

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem exists_psi_E7_3 (hadm : StatedLieAdmissible .E7 0 3 1) {X : Type} [Group X]
    (U : Fin 7 → Subgroup X)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 7, edgeE 7 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E7 0 3 1 Nat.prime_three).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e7Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := weakCT3_e7 hadm (F := GaloisField 3 1) card_gf3
    (X := ↥(⨆ k, U k)) (fun k => (U k).subgroupOf (⨆ k, U k))
    (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : ↥(Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 3 1)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e7Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key

theorem exists_psi_E8_3 (hadm : StatedLieAdmissible .E8 0 3 1) {X : Type} [Group X]
    (U : Fin 8 → Subgroup X)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 8, edgeE 8 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E8 0 3 1 Nat.prime_three).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Adjoint.e8Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := weakCT3_e8 hadm (F := GaloisField 3 1) card_gf3
    (X := ↥(⨆ k, U k)) (fun k => (U k).subgroupOf (⨆ k, U k))
    (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 3 1)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Adjoint.e8Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key

theorem nonempty_extModel3_E7 (hadm : StatedLieAdmissible .E7 0 3 1) :
    Nonempty (ExtModel3 .E7 0 .POmegaPlus 6 1) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadmY : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨hp, le_rfl, by norm_num⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 3 1 hp trivial hadm
  set D := (modelUniv .E7 0 3 1 Nat.prime_three).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E7 0 3 1 hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 7; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta7 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta7
  have hRθ := fund_of_longest (t := .E7) D (isLongestRoot_of_lenSq D hℓ hθ)
  have hlong : ∀ k, CFSG.ClassicalInvolution.Generic.IsLongestRoot D (Pi.single k 1) :=
    fun k => isLongestRoot_of_lenSq D hℓ (single_mem_roots D k)
  obtain ⟨ψ, hψker, hψrange, hψrk⟩ := exists_psi_of_chain_plus3 (N := 6) hadmY
    (G := (modelUniv .E7 0 3 1 Nat.prime_three).K) (fun i => rankOne D.rootGroup (iota7 i))
    (fun i j hij h1 h2 => commutes_rankOne_of_cartan_eq_zero D hext hℓ (iota7_comm i j hij h1 h2))
    (fun i j h => stdPair_adj_E7 (iota7_edge i j h))
  let y0 : Fin (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rank := ⟨0, by show 0 < 6; decide⟩
  obtain ⟨W₀, hW₀⟩ := stdPair_edge_E7 (F := GaloisField 3 1) (i := 0) (j := 2) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := GaloisField 3 1)
    (by norm_num : 3 ≤ 6) (by norm_num : 4 ≤ 6)
  let Θ : (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K →*
      (modelUniv .E7 0 3 1 Nat.prime_three).K := ψ
  have hΘker : Θ.ker ≤ Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K :=
    hψker
  have hΘrange : Θ.range = ⨆ i, rankOne D.rootGroup (iota7 i) := hψrange
  have hΘ₀ : (rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup y0).map Θ =
      rankOne D.rootGroup (iota7 0) := hψrk 0
  have hcopT : ∀ w ∈ Subgroup.center (modelUniv .E7 0 3 1 Nat.prime_three).K,
      ¬ 3 ∣ orderOf w := by
    intro w hw
    have hcard := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7
      (k := GaloisField 3 1)).1
    rw [card_gf3] at hcard
    have hw' : w ∈ Subgroup.center
        (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 3 1)) := hw
    have hd : orderOf w ∣ Nat.gcd 2 (3 - 1) :=
      (Subgroup.orderOf_dvd_natCard _ hw').trans (dvd_of_eq hcard)
    exact fun h3 => absurd (h3.trans hd) (by norm_num)
  have hcopY : ∀ w ∈ Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K,
      ¬ 3 ∣ orderOf w := fun w hw h3 =>
    absurd (h3.trans (orderOf_dvd_of_pow_eq_one (pow_four_of_mem_center_spinPlus
      (by norm_num : 3 ≤ 6) hw))) (by norm_num)
  refine nonempty_extModel3U_one
    (ModelFacts.fundamentalSingleClass .E7 0 3 1 hp trivial hadm (by decide) (by decide))
    (ModelFacts.fundamentalSingleClass .POmegaPlus 6 3 1 hp trivial hadmY (by decide) (by decide))
    (rankOne_mem_fundamental D (hlong z0)) (pow3_of_stdPair card_gf3 hW₀).1
    (R₀Y := rankOne (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D.rootGroup y0)
    (rankOne_mem_fundamental _
      (ModelFacts.isLongestRoot_single .POmegaPlus 6 3 1 hp trivial hadmY y0 trivial))
    (pow3_of_stdPair card_gf3 hW₁).1 hRθ Θ hΘker ?_ ?_ hcopT hcopY
  · rw [hΘ₀]
    exact rankOne_mem_fundamental D (hlong (iota7 0))
  · rw [hΘrange]
    refine commutes_iSup_left.mpr fun i => ?_
    exact commutes_rankOne_theta D hext hℓ hθ (k := iota7 i)
      ((coroot_apply D.cartan (iota7 i) theta7).trans (coroot_theta7 _ (iota7_ne i)))

theorem nonempty_extModel3_E8 (hadm : StatedLieAdmissible .E8 0 3 1) :
    Nonempty (ExtModel3 .E8 0 .E7 0 1) := by
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
  have hRθ := fund_of_longest (t := .E8) D (isLongestRoot_of_lenSq D hℓ hθ)
  have hlong : ∀ k, CFSG.ClassicalInvolution.Generic.IsLongestRoot D (Pi.single k 1) :=
    fun k => isLongestRoot_of_lenSq D hℓ (single_mem_roots D k)
  obtain ⟨ψ, hψker, hψrange, hψrk⟩ := exists_psi_E7_3 hadmY
    (X := (modelUniv .E8 0 3 1 Nat.prime_three).K)
    (fun i : Fin 7 => rankOne D.rootGroup i.castSucc)
    (fun i j hij h1 h2 =>
      commutes_rankOne_of_cartan_eq_zero D hext hℓ (castSucc_comm i j hij h1 h2))
    (fun i j h => stdPair_edge_E8 (castSucc_edge i j h))
  let y0 : Fin (modelUniv .E7 0 3 1 Nat.prime_three).D.rank := ⟨0, by show 0 < 7; decide⟩
  obtain ⟨W₀, hW₀⟩ := stdPair_edge_E8 (F := GaloisField 3 1) (i := 0) (j := 2) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e7Datum (F := GaloisField 3 1)
  let Θ : (modelUniv .E7 0 3 1 Nat.prime_three).K →* (modelUniv .E8 0 3 1 Nat.prime_three).K := ψ
  have hΘker : Θ.ker ≤ Subgroup.center (modelUniv .E7 0 3 1 Nat.prime_three).K := hψker
  have hΘrange : Θ.range = ⨆ i : Fin 7, rankOne D.rootGroup i.castSucc := hψrange
  have hΘ₀ : (rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup y0).map Θ =
      rankOne D.rootGroup (0 : Fin 7).castSucc := hψrk y0
  have hcopT : ∀ w ∈ Subgroup.center (modelUniv .E8 0 3 1 Nat.prime_three).K,
      ¬ 3 ∣ orderOf w := by
    intro w hw
    have hZ : Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 3 1)) =
        ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    have hw1 : w = 1 := by
      have hmem : w ∈ (⊥ : Subgroup
          ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 3 1))) := by
        rw [← hZ]
        exact hw
      exact Subgroup.mem_bot.mp hmem
    rw [hw1, orderOf_one]
    omega
  have hcopY : ∀ w ∈ Subgroup.center (modelUniv .E7 0 3 1 Nat.prime_three).K,
      ¬ 3 ∣ orderOf w := by
    intro w hw
    have hcard := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7
      (k := GaloisField 3 1)).1
    rw [card_gf3] at hcard
    have hw' : w ∈ Subgroup.center
        (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 3 1)) := hw
    have hd : orderOf w ∣ Nat.gcd 2 (3 - 1) :=
      (Subgroup.orderOf_dvd_natCard _ hw').trans (dvd_of_eq hcard)
    exact fun h3 => absurd (h3.trans hd) (by norm_num)
  refine nonempty_extModel3U_one
    (ModelFacts.fundamentalSingleClass .E8 0 3 1 hp trivial hadm (by decide) (by decide))
    (ModelFacts.fundamentalSingleClass .E7 0 3 1 hp trivial hadmY (by decide) (by decide))
    (rankOne_mem_fundamental D (hlong z0)) (pow3_of_stdPair card_gf3 hW₀).1
    (R₀Y := rankOne (modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup y0)
    (rankOne_mem_fundamental _
      (ModelFacts.isLongestRoot_single .E7 0 3 1 hp trivial hadmY y0 trivial))
    (pow3_of_stdPair card_gf3 hW₁).1 hRθ Θ hΘker ?_ ?_ hcopT hcopY
  · rw [hΘ₀]
    exact rankOne_mem_fundamental D (hlong _)
  · rw [hΘrange]
    refine commutes_iSup_left.mpr fun i : Fin 7 => ?_
    exact commutes_rankOne_theta D hext hℓ hθ (k := i.castSucc)
      ((coroot_apply D.cartan i.castSucc theta8).trans (coroot_theta8 _ (castSucc_ne i)))

end CFSG.ClassicalInvolution.Q3.Q3W
