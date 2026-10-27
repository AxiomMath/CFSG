module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
open scoped commutatorElement

section Main

theorem delBlockCommuteProp
    : DelBlockCommuteProp := by
  intro G _ _ R M V n F _ r Lc ctx hcore hall hImage hCore
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hfam := del_family_data hS ctx.comps ctx.deleted
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  have hr : 0 < r := hbridge.r_pos
  obtain ⟨Fs0, P0, hP0⟩ := hall ⟨0, hr⟩
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS := L ⊔ baum R with hLS
  have hker : LS ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 LS := hP0.ker.kernel.2
  have hBLS : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ LS := fun j =>
    (oddOrderSubgroup_le _).trans inf_le_left
  have hBL : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ L := fun j =>
    oddOrderSubgroup_mono le_top
  have hLSnB : ∀ j, LS ≤ Subgroup.normalizer
      ((blockOf (⊤ : Subgroup G) R V hX (Lc j) : Subgroup G) : Set G) := fun j =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS j)).1 (hImage.normal_B j)
  have hLSnLc : ∀ j, autOn LS V ≤ Subgroup.normalizer (Lc j : Set (MulAut V)) := by
    intro j
    have h1 := autOn_le_normalizer_autOn (hnormV LS) (hnormV _) (hLSnB j)
    rwa [hImage.image j] at h1
  have hLSnI : ∀ j, LS ≤ Subgroup.normalizer ((modComm V (Lc j) : Subgroup G) : Set G) := fun j =>
    le_normalizer_modComm (hLSnLc j)
  have hρB : ∀ j, (blockOf (⊤ : Subgroup G) R V hX (Lc j)).map
      (MulAut.conjNormal (H := V)) = Lc j := fun j => by
    rw [← autOn_eq_map_conjNormal]
    exact hImage.image j
  have hρmem : ∀ j, ∀ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc j),
      MulAut.conjNormal (H := V) b ∈ Lc j := by
    intro j b hb
    rw [← hρB j]
    exact Subgroup.mem_map_of_mem _ hb
  have hcommute : ∀ i j, i ≠ j →
      ⁅blockOf (⊤ : Subgroup G) R V hX (Lc i), blockOf (⊤ : Subgroup G) R V hX (Lc j)⁆ = ⊥ := by
    intro i j hij
    set Bi := blockOf (⊤ : Subgroup G) R V hX (Lc i) with hBi
    set Bj := blockOf (⊤ : Subgroup G) R V hX (Lc j) with hBj
    have hAφ : (⁅Bi, Bj⁆).map (MulAut.conjNormal (H := V)) = ⊥ := by
      rw [Subgroup.map_commutator, hρB i, hρB j]
      exact hbridge.commute i j hij
    have hAQ : ⁅Bi, Bj⁆ ≤ pCoreOf 2 LS := by
      intro x hx
      have hxLS : x ∈ LS := commutator_le_of_le_of_le (hBLS i) (hBLS j) hx
      have h1 : MulAut.conjNormal (H := V) x = 1 :=
        (Subgroup.map_eq_bot_iff _).1 hAφ hx
      rw [← hker]
      exact ⟨hxLS, conjNormal_eq_one_iff.1 h1⟩
    have hAB : ⁅⁅Bi, Bj⁆, Bi⁆ ≤ modComm V (Lc i) :=
      ((Subgroup.commutator_mono hAQ le_rfl).trans (hCore.coreComm i).2.le)
    have hAI : ⁅Bi, Bj⁆ ≤ modComm V (Lc i) :=
      perfect_commutator_le_mod (K := LS) (hBLS i) (hBLS j) (hLSnI i) (hImage.perfect_self i) hAB
    have hjI : ⁅⁅Bi, Bj⁆, Bj⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have haI : a ∈ modComm V (Lc i) := hAI ha
      have haV : a ∈ V := modComm_le V (Lc i) haI
      have h1 := hfam.others i j (Ne.symm hij) (MulAut.conjNormal (H := V) b) (hρmem j b hb)
        ⟨a, haV⟩ haI
      have h2 : b * a * b⁻¹ = a := by
        have h3 := congrArg (fun z : V => (z : G)) h1
        simpa [MulAut.conjNormal_apply] using h3
      have h3 : a * b = b * a := by
        calc a * b = (b * a * b⁻¹) * b := by rw [h2]
          _ = b * a := by group
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm.2 h3]
    have hperf_j : Group.IsPerfect ↥Bj := Subgroup.isPerfect_iff.2 (hImage.perfect_self j)
    have h4 : ⁅⁅Bj, Bi⁆, Bj⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Bj Bi]
      exact hjI
    have h5 := CFSG.LocalCores.perfect_double_commutator hperf_j h4
    rw [Subgroup.commutator_comm]
    exact h5
  have hDBle : (⨆ i, blockOf (⊤ : Subgroup G) R V hX (Lc i)) ≤ L := iSup_le hBL
  have hLSnD : LS ≤ Subgroup.normalizer
      ((⨆ i, blockOf (⊤ : Subgroup G) R V hX (Lc i) : Subgroup G) : Set G) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    have h1 : (blockOf (⊤ : Subgroup G) R V hX (Lc i)).map (MulAut.conj g).toMonoidHom =
        blockOf (⊤ : Subgroup G) R V hX (Lc i) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hLSnB i hg)
    rw [h1]
    exact le_iSup (fun i => blockOf (⊤ : Subgroup G) R V hX (Lc i)) i
  have hDn : ((⨆ i, blockOf (⊤ : Subgroup G) R V hX (Lc i)).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDBle).2 (le_sup_left.trans hLSnD)
  have himgD : autOn (⨆ i, blockOf (⊤ : Subgroup G) R V hX (Lc i)) V = ⨆ i, Lc i := by
    rw [autOn_iSup_of_le _ (fun i => hnormV _)]
    exact iSup_congr fun i => hImage.image i
  have himgL : autOn L V = ⨆ i, Lc i := hbridge.K_eq.trans hbridge.K_prod
  have hLeq : (⨆ i, blockOf (⊤ : Subgroup G) R V hX (Lc i)) = L :=
    eq_of_map_le_of_two_kernel (MulAut.conjNormal (H := V)) (B := L)
      (D := ⨆ i, blockOf (⊤ : Subgroup G) R V hX (Lc i)) le_sup_left hDBle hDn
      (oddOrderSubgroup_idem _)
      (fun x hx h1 => two_elt_of_conjNormal_eq_one hker hx h1)
      (by rw [← autOn_eq_map_conjNormal, ← autOn_eq_map_conjNormal, himgL, himgD])
  refine ⟨hcommute, hLeq.symm, fun i => ?_⟩
  intro x hx
  obtain ⟨hxB, hxD⟩ := Subgroup.mem_inf.1 hx
  have hcent : (⨆ j, ⨆ (_ : j ≠ i), blockOf (⊤ : Subgroup G) R V hX (Lc j)) ≤
      Subgroup.centralizer (blockOf (⊤ : Subgroup G) R V hX (Lc i) : Set G) :=
    iSup₂_le fun j hj => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcommute j i hj)
  exact Subgroup.mem_inf.2 ⟨hxB, hcent hxD⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift
