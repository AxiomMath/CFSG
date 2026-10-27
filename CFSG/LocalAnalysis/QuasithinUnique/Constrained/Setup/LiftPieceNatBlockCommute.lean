module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatBlockTools

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
open scoped commutatorElement

theorem natCommuteProp
    : NatCommuteProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hcore hcan hA hB
  classical
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hothers := nat_others hS ctx.comps
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS := L ⊔ baum R with hLS
  have hker : LS ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 LS := hcore.ker.kernel.2
  have hBLS : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ LS := fun j =>
    (oddOrderSubgroup_le _).trans inf_le_left
  have hBL : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ L := fun j =>
    oddOrderSubgroup_mono le_top
  have hLSnB : ∀ j, LS ≤ Subgroup.normalizer
      ((blockOf (⊤ : Subgroup G) R V hX (Lc j) : Subgroup G) : Set G) := fun j =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS j)).1 (hA.normal_B j)
  have hLSnLc : ∀ j, autOn LS V ≤ Subgroup.normalizer (Lc j : Set (MulAut V)) := by
    intro j
    have h1 := autOn_le_normalizer_autOn (hnormV LS) (hnormV _) (hLSnB j)
    rwa [hA.image j] at h1
  have hLSnI : ∀ j, LS ≤ Subgroup.normalizer ((modComm V (Lc j) : Subgroup G) : Set G) := fun j =>
    le_normalizer_modComm (hLSnLc j)
  have hρB : ∀ j, (blockOf (⊤ : Subgroup G) R V hX (Lc j)).map
      (MulAut.conjNormal (H := V)) = Lc j := fun j => by
    rw [← autOn_eq_map_conjNormal]
    exact hA.image j
  have hρmem : ∀ j, ∀ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc j),
      MulAut.conjNormal (H := V) b ∈ Lc j := by
    intro j b hb
    rw [← hρB j]
    exact Subgroup.mem_map_of_mem _ hb
  have hcommute : ∀ j k, j ≠ k →
      ⁅blockOf (⊤ : Subgroup G) R V hX (Lc j), blockOf (⊤ : Subgroup G) R V hX (Lc k)⁆ = ⊥ := by
    intro j k hjk
    set Bj := blockOf (⊤ : Subgroup G) R V hX (Lc j) with hBj
    set Bk := blockOf (⊤ : Subgroup G) R V hX (Lc k) with hBk
    have hAφ : (⁅Bj, Bk⁆).map (MulAut.conjNormal (H := V)) = ⊥ := by
      rw [Subgroup.map_commutator, hρB j, hρB k]
      exact hbridge.commute j k hjk
    have hAQ : ⁅Bj, Bk⁆ ≤ pCoreOf 2 LS := by
      intro x hx
      have hxLS : x ∈ LS := commutator_le_of_le_of_le (hBLS j) (hBLS k) hx
      have h1 : MulAut.conjNormal (H := V) x = 1 :=
        (Subgroup.map_eq_bot_iff _).1 hAφ hx
      rw [← hker]
      exact ⟨hxLS, conjNormal_eq_one_iff.1 h1⟩
    have hAB : ⁅⁅Bj, Bk⁆, Bj⁆ ≤ modComm V (Lc j) :=
      ((Subgroup.commutator_mono hAQ le_rfl).trans (hA.coreComm j).2.le)
    have hAI : ⁅Bj, Bk⁆ ≤ modComm V (Lc j) :=
      perfect_commutator_le_mod (K := LS) (hBLS j) (hBLS k) (hLSnI j) (hB j).2.1 hAB
    have hjI : ⁅⁅Bj, Bk⁆, Bk⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have haI : a ∈ modComm V (Lc j) := hAI ha
      have haV : a ∈ V := modComm_le V (Lc j) haI
      have h1 := hothers j k (Ne.symm hjk) (MulAut.conjNormal (H := V) b) (hρmem k b hb)
        ⟨a, haV⟩ haI
      have h2 : b * a * b⁻¹ = a := by
        have h3 := congrArg (fun z : V => (z : G)) h1
        simpa [MulAut.conjNormal_apply] using h3
      have h3 : a * b = b * a := by
        calc a * b = (b * a * b⁻¹) * b := by rw [h2]
          _ = b * a := by group
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm.2 h3]
    have hperf_k : Group.IsPerfect ↥Bk := Subgroup.isPerfect_iff.2 (hB k).2.1
    have h4 : ⁅⁅Bk, Bj⁆, Bk⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Bk Bj]
      exact hjI
    have h5 := CFSG.LocalCores.perfect_double_commutator hperf_k h4
    rw [Subgroup.commutator_comm]
    exact h5
  have hDBle : (⨆ j, blockOf (⊤ : Subgroup G) R V hX (Lc j)) ≤ L := iSup_le hBL
  have hLSnD : LS ≤ Subgroup.normalizer
      ((⨆ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) : Subgroup G) : Set G) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    have h1 : (blockOf (⊤ : Subgroup G) R V hX (Lc j)).map (MulAut.conj g).toMonoidHom =
        blockOf (⊤ : Subgroup G) R V hX (Lc j) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hLSnB j hg)
    rw [h1]
    exact le_iSup (fun j => blockOf (⊤ : Subgroup G) R V hX (Lc j)) j
  have hDn : ((⨆ j, blockOf (⊤ : Subgroup G) R V hX (Lc j)).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDBle).2 (le_sup_left.trans hLSnD)
  have himgD : autOn (⨆ j, blockOf (⊤ : Subgroup G) R V hX (Lc j)) V = ⨆ j, Lc j := by
    rw [autOn_iSup_of_le _ (fun j => hnormV _)]
    exact iSup_congr fun j => hA.image j
  have himgL : autOn L V = ⨆ j, Lc j := hbridge.K_eq.trans hbridge.K_prod
  have hLeq : (⨆ j, blockOf (⊤ : Subgroup G) R V hX (Lc j)) = L :=
    eq_of_map_le_of_two_kernel (MulAut.conjNormal (H := V)) (B := L)
      (D := ⨆ j, blockOf (⊤ : Subgroup G) R V hX (Lc j)) le_sup_left hDBle hDn
      (oddOrderSubgroup_idem _)
      (fun x hx h1 => two_elt_of_conjNormal_eq_one hker hx h1)
      (by rw [← autOn_eq_map_conjNormal, ← autOn_eq_map_conjNormal, himgL, himgD])
  refine ⟨hcommute, hLeq.symm, fun j => ?_⟩
  intro x hx
  obtain ⟨hxB, hxD⟩ := Subgroup.mem_inf.1 hx
  have hcent : (⨆ k, ⨆ (_ : k ≠ j), blockOf (⊤ : Subgroup G) R V hX (Lc k)) ≤
      Subgroup.centralizer (blockOf (⊤ : Subgroup G) R V hX (Lc j) : Set G) :=
    iSup₂_le fun k hk => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcommute k j hk)
  exact Subgroup.mem_inf.2 ⟨hxB, hcent hxD⟩

end CFSG.QuasithinUnique.Setup.Lift
