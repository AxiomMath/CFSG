module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowOmegaLevi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowSummandDatum
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Main

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Facts

variable {K : Type} [Field K]

theorem a2l_finrank_quadPlus_four : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

theorem a2lE0_isQuasisimple :
    CFSG.IsQuasisimple ↥(elementaryGroup (quadPlus 4 K)) :=
  CFSG.IsQuasisimple.of_mulEquiv
    (statedOmegaEquiv (coe_quadPlus 4 K) (commutator_orthogonalGroup_quadPlus (by norm_num))).symm
    (isQuasisimple_statedOmega_quadPlus (by norm_num))

theorem a2lE0_isPGroup_center [Finite K] (hK : Nat.card K = 3) :
    IsPGroup 2 ↥(center ↥(elementaryGroup (quadPlus 4 K))) :=
  Small.isPGroup_center_elementaryGroup hK (nondegenerate_polarBilin_quadPlus 4 K)
    (by rw [a2l_finrank_quadPlus_four]; norm_num)

theorem a2lE0_lieModel [Finite K] (hK : Nat.card K = 3) :
    LieModel (↥(elementaryGroup (quadPlus 4 K)) ⧸ center ↥(elementaryGroup (quadPlus 4 K)))
      .POmegaPlus 4 3 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, le_rfl⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num,
    ⟨((statedProjEquiv (coe_quadPlus 4 K)
      (commutator_orthogonalGroup_quadPlus (by norm_num))).trans
      (Small.projElementaryEquivCenter hK (nondegenerate_polarBilin_quadPlus 4 K)
        (by rw [a2l_finrank_quadPlus_four]; norm_num))).symm⟩⟩

end Facts

theorem a2l_false_of_card {S : Type} [Group S]
    (hC : Nat.card S ∈ ({60, 168, 6048} : Finset ℕ) ∨ LieModel S .PSL 2 3 2 ∨
      LieModel S .PSp 2 3 1) {c : ℕ} (hc : Nat.card S = c)
    (hne : c ∉ ({60, 168, 6048, 360, 25920} : Finset ℕ)) : False := by
  rcases hC with h | h | h
  · exact hne (by rw [← hc]; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; omega)
  · have h1 := GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 3) (f := 2) (by norm_num) h
    have h2 : Nat.card S = 360 := by rw [h1]; decide
    exact hne (by rw [← hc, h2]; decide)
  · have h1 := GH74.card_of_lieModel_PSp (G := S) (n := 2) (p := 3) (f := 1) (by norm_num)
      (by norm_num) h
    have h2 : Nat.card S = 25920 := by rw [h1]; decide
    exact hne (by rw [← hc, h2]; decide)

theorem a2l_not_inChev2_pOmegaPlus43 (hC : HypA2.ChevOddInChev2) {S : Type} [Group S] [Finite S]
    (h : LieModel S .POmegaPlus 4 3 1) : ¬ GH74.GLS.InChev2 S := fun hI =>
  a2l_false_of_card (hC S 3 Nat.prime_three (by norm_num) ⟨.POmegaPlus, 4, 1, h⟩ hI)
    (c := Open.ordD 4 (3 ^ 1))
    ((CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num)
      (GH74.statedClassicalModel_of_lieModel (by norm_num) h)).2.2.2.2.1 rfl) (by decide)

section Datum

variable {K : Type} [Field K] [Finite K]

theorem a2lE0_typU (hC : HypA2.ChevOddInChev2) (hK : Nat.card K = 3) :
    TypU ↥(elementaryGroup (quadPlus 4 K)) := by
  haveI : Finite ↥(elementaryGroup (quadPlus 4 K)) := by
    haveI := a2l_finite_linearEquiv (K := K) (V := Fin 4 ⊕ Fin 4 → K)
    infer_instance
  have hm := a2lE0_lieModel hK
  exact a2l_typU_of_not_inChev2 a2lE0_isQuasisimple (a2lE0_isPGroup_center hK)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))))
    (a2l_not_inChev2_pOmegaPlus43 hC hm)

theorem a2l_mem_commutator_of_isPerfect {G V : Type} [Group G] [Group.IsPerfect G]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (ψ : G →* (V ≃ₗ[K] V))
    (hψ : ∀ g, ψ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (g : G) :
    ψ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hg : g ∈ commutator G := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top g
  have h1 := Subgroup.mem_map_of_mem ψ hg
  rw [commutator_def, Subgroup.map_commutator] at h1
  refine Subgroup.commutator_mono ?_ ?_ h1 <;> rintro _ ⟨y, -, rfl⟩ <;> exact hψ y

theorem a2lNineLevi_mem_elementary [Fintype K] (hF : Fintype.card K = 3)
    (g : SL(2, GaloisField 3 2)) : a2lNineLevi hF g ∈ elementaryGroup (quadPlus 4 K) := by
  haveI := CFSG.RankThree.PartTwo.Census.isPerfect_sl2_nine
  rw [← commutator_orthogonalGroup_quadPlus (K := K) (n := 4) (by norm_num)]
  exact a2l_mem_commutator_of_isPerfect (a2lNineLevi hF) (a2lNineLevi_mem_orthogonalGroup hF) g

theorem a2lDatum_projElementary_of_summand_three (hC : HypA2.ChevOddInChev2)
    (hK : Nat.card K = 3) {V : Type} [AddCommGroup V] [Module K V] [Finite V]
    {Q : QuadraticForm K V} (S : A2lSummand (quadPlus 4 K) Q) {v : V} (hv0 : v ≠ 0)
    (hv : S.coords v = 0) : a2lDatum (ProjElementary Q) := by
  haveI := Fintype.ofFinite K
  have hFc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)
  haveI := Fintype.ofFinite (GaloisField 3 2)
  have hF9 : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, CFSG.RankThree.PartTwo.Census.card_galoisField_three_two]
  exact a2lDatum_projElementary_of_summand h2 S hv0 hv (q₀ := 9) (by decide) (by norm_num) hF9
    (a2lNineLevi hFc) (a2lNineLevi_injective hFc) (a2lNineLevi_mem_elementary hFc)
    (a2lNineLevi_negOne hFc) a2lE0_isQuasisimple (a2lE0_typU hC hK)

end Datum

end CFSG.OddStandard.SmallF3.HypA2Leaves
