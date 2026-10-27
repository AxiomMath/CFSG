module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapPair
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapGen
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapTriangle

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped commutatorElement

section Common

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def planeCommutator (k : Fin n) : StatedSp n K :=
  ⁅longBlock K n k (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])),
    longBlock K n k (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two]))⁆

theorem planeCommutator_ne_one (k : Fin n) : planeCommutator (K := K) k ≠ 1 := by
  intro h
  rw [planeCommutator, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul] at h
  have h' := longBlock_injective k h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 1 1) h'
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
  simp [mkSL, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem planeCommutator_mem_perfectCore_spBlock [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {k : Fin n} {N : Finset (Fin n)} (hk : k ∈ N) (hN : 2 ≤ N.card) :
    planeCommutator (K := K) k ∈ perfectCore (spBlock K N) := by
  have hsub : longRootSp2 K n k ≤ spBlock K N := by
    rw [← spBlock_singleton]
    exact spBlock_mono (Finset.singleton_subset_iff.2 hk)
  refine (perfectCore_spBlock_of_card_two hK hN).2.2 (commutator_mem_commutator ?_ ?_)
  · exact hsub ⟨_, rfl⟩
  · exact hsub ⟨_, rfl⟩

end Common

section Main


theorem spTwoRowInput_swap : SpTwoRowInput .swap := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hswap
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set i₀ : Fin (n + 1) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (n + 1) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (n + 1) := ⟨2, by omega⟩ with hi₂
  set i₃ : Fin (n + 1) := ⟨3, by omega⟩ with hi₃
  have hne : ∀ x y : Fin (n + 1), (x : ℕ) ≠ y → x ≠ y := fun x y h hxy => h (by rw [hxy])
  have h01 : i₀ ≠ i₁ := hne _ _ (by simp [hi₀, hi₁])
  have h02 : i₀ ≠ i₂ := hne _ _ (by simp [hi₀, hi₂])
  have h03 : i₀ ≠ i₃ := hne _ _ (by simp [hi₀, hi₃])
  have h12 : i₁ ≠ i₂ := hne _ _ (by simp [hi₁, hi₂])
  have h13 : i₁ ≠ i₃ := hne _ _ (by simp [hi₁, hi₃])
  have h23 : i₂ ≠ i₃ := hne _ _ (by simp [hi₂, hi₃])
  obtain ⟨P₁, hinj₁, hrange₁⟩ := exists_swapParam_nsTorusSp hset hK hn e htC ht i₀ (hswap i₀)
  obtain ⟨P₂, hinj₂, hrange₂⟩ := exists_swapParam_nsTorusSp hset hK hn e htC ht i₁ (hswap i₁)
  obtain ⟨P₃, hinj₃, hrange₃⟩ := exists_swapParam_nsTorusSp hset hK hn e htC ht i₂ (hswap i₂)
  have hO := perfectCore_modelToG_complSp_inf_centralizer_nsTorusSp (G := G) (L := L) hK e
  have hcard : ∀ {a b : Fin (n + 1)}, a ≠ b →
      2 ≤ (({a, b}ᶜ : Finset (Fin (n + 1)))).card := by
    intro a b hab
    rw [card_compl_pair_planes hab]
    omega
  have hS₁₂ := perfectCore_spBlock_of_card_two hK (hcard h01)
  have hS₁₃ := perfectCore_spBlock_of_card_two hK (hcard h02)
  have hS₂₃ := perfectCore_spBlock_of_card_two hK (hcard h12)
  set q : G := ((e.symm (planeCommutator (K := K) i₃) : L) : G) with hq
  have hqmem : ∀ {a b : Fin (n + 1)}, a ≠ b → a ≠ i₃ → b ≠ i₃ →
      q ∈ modelToG e (perfectCore (spBlock K ({a, b}ᶜ : Finset (Fin (n + 1))))) := by
    intro a b hab ha hb
    refine UnitaryPilot.symm_mem_modelToG e (planeCommutator_mem_perfectCore_spBlock hK ?_
      (hcard hab))
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hb⟩
  have hq1 : q ≠ 1 := by
    intro h
    have h' : e.symm (planeCommutator (K := K) i₃) = 1 := Subtype.ext h
    apply planeCommutator_ne_one (K := K) i₃
    rw [← e.apply_symm_apply (planeCommutator i₃), h', map_one]
  have hgen := perfectCore_spBlock_compl_pair_sup_sup_eq_top hK hn h01 h02 h12 h03 h13 h23
  refine E8Pilot.false_of_swapParam_triangle hset
    (isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)) e
    (swapPairExclusion_statedSp_two (by omega) hK) ht hKt P₁ P₂ P₃ hinj₁ hinj₂ hinj₃ hrange₁
    hrange₂ hrange₃ (UnitaryPilot.modelToG_le e _) (UnitaryPilot.modelToG_le e _)
    (UnitaryPilot.modelToG_le e _)
    (UnitaryPilot.modelToG_mono e (nsTorusSp_le_complSp h01.symm))
    (UnitaryPilot.modelToG_mono e (nsTorusSp_le_complSp h02.symm))
    (UnitaryPilot.modelToG_mono e (nsTorusSp_le_complSp h01))
    (UnitaryPilot.modelToG_mono e (nsTorusSp_le_complSp h12.symm))
    (UnitaryPilot.modelToG_mono e (nsTorusSp_le_complSp h02))
    (UnitaryPilot.modelToG_mono e (nsTorusSp_le_complSp h12))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hq1 ?_
  · rw [hO]
    exact OmegaPilot.isSimpleGroup_modelToG e hS₁₂.1
  · rw [hO]
    exact OmegaPilot.isSimpleGroup_modelToG e hS₁₃.1
  · rw [hO]
    exact OmegaPilot.isSimpleGroup_modelToG e hS₂₃.1
  · rw [hO]
    exact OmegaPilot.center_modelToG_eq_bot e hS₁₂.2.1
  · rw [hO]
    exact OmegaPilot.center_modelToG_eq_bot e hS₁₃.2.1
  · rw [hO]
    exact OmegaPilot.center_modelToG_eq_bot e hS₂₃.2.1
  · rw [hO]
    exact hqmem h01 h03 h13
  · rw [hO]
    exact hqmem h02 h03 h23
  · rw [hO]
    exact hqmem h12 h13 h23
  · rw [hO, hO, hO, ← UnitaryPilot.modelToG_sup, ← UnitaryPilot.modelToG_sup, hgen,
      UnitaryPilot.modelToG_top]

end Main

end CFSG.SeitzReduction.SymplecticPilot
