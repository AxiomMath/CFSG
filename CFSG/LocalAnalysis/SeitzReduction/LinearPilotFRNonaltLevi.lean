module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltBasic
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallGraph

public section

namespace CFSG.SeitzReduction.LinearPilot

namespace Nonalt

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {n : ℕ} {K : Type} [Field K]

section Block

theorem blockMatrix_transpose (I : Finset (Fin n)) (B : Matrix I I K) :
    (blockMatrix I B)ᵀ = blockMatrix I Bᵀ := by
  ext j k
  rw [transpose_apply, blockMatrix_apply, blockMatrix_apply]
  by_cases hj : j ∈ I <;> by_cases hk : k ∈ I
  · rw [dite_eq_left ⟨hk, hj⟩, dite_eq_left ⟨hj, hk⟩, transpose_apply]
  · rw [dite_eq_right (fun h => hk h.1), dite_eq_right (fun h => hk h.2), one_apply, one_apply]
    simp only [eq_comm]
  · rw [dite_eq_right (fun h => hj h.2), dite_eq_right (fun h => hj h.1), one_apply, one_apply]
    simp only [eq_comm]
  · rw [dite_eq_right (fun h => hk h.1), dite_eq_right (fun h => hk h.2), one_apply, one_apply]
    simp only [eq_comm]

theorem blockMatrix_injective (I : Finset (Fin n)) :
    Function.Injective (blockMatrix (K := K) I) := by
  intro X Y h
  ext a b
  have := congrFun (congrFun h a) b
  rwa [blockMatrix_apply, blockMatrix_apply, dite_eq_left ⟨a.2, b.2⟩,
    dite_eq_left ⟨a.2, b.2⟩] at this

theorem card_univ_erase (i : Fin n) : (Finset.univ.erase i).card = n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem card_univ_erase_lt (i : Fin n) : (Finset.univ.erase i).card < n := by
  rw [card_univ_erase]
  have := i.2
  omega

theorem levi0_eq_map (i : Fin n) :
    levi0 (K := K) i = (orthSL K (Finset.univ.erase i)).map (blockEmbed (Finset.univ.erase i)) := by
  ext A
  constructor
  · intro hA
    have hT : (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Pi.single i 1 = Pi.single i 1 := by
      calc (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Pi.single i 1
          = (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ
              Pi.single i 1) := by rw [hA.2]
        _ = Pi.single i 1 := by rw [mulVec_mulVec, hA.1, one_mulVec]
    have hAI : A ∈ blockSpecialLinear (Finset.univ.erase i) := by
      intro j k hjk
      have hjk' : j = i ∨ k = i := by
        simpa only [Finset.mem_erase, Finset.mem_univ, and_true, not_not] using hjk
      rcases hjk' with rfl | rfl
      · have h := congrFun hT k
        rw [mulVec_single_one, col_apply, transpose_apply] at h
        rw [h, Pi.single_apply, one_apply]
        simp only [eq_comm]
      · have h := congrFun hA.2 j
        rw [mulVec_single_one, col_apply] at h
        rw [h, Pi.single_apply, one_apply]
    rw [← range_blockEmbed] at hAI
    obtain ⟨B, rfl⟩ := hAI
    refine ⟨B, ?_, rfl⟩
    have h1 := hA.1
    rw [coe_blockEmbed, blockMatrix_transpose, ← blockMatrix_mul, ← blockMatrix_one] at h1
    exact blockMatrix_injective _ h1
  · rintro ⟨B, hB, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [coe_blockEmbed, blockMatrix_transpose, ← blockMatrix_mul]
      have hB' : (B : Matrix (Finset.univ.erase i) (Finset.univ.erase i) K)ᵀ * B = 1 := hB
      rw [hB', blockMatrix_one]
    · ext j
      rw [coe_blockEmbed, mulVec_single_one, col_apply, blockMatrix_apply,
        dite_eq_right (fun h => by simpa using h.2), Pi.single_apply, one_apply]

theorem levi_eq_map (i : Fin n) :
    levi (K := K) i = (orthSL K (Finset.univ.erase i)).map
      ((proj n K).comp (blockEmbed (Finset.univ.erase i))) := by
  rw [levi, levi0_eq_map, Subgroup.map_map]

@[expose] noncomputable def leviEquivOrth (i : Fin n) :
    levi (K := K) i ≃* orthSL K (Finset.univ.erase i) :=
  (MulEquiv.subgroupCongr (levi_eq_map i)).trans
    ((orthSL K _).equivMapOfInjective _
      (proj_comp_blockEmbed_injective (card_univ_erase_lt i))).symm

end Block

section Isometry

variable (K) in
@[expose] noncomputable def orthToGL (i : Fin n) :
    SpecialLinearGroup (Finset.univ.erase i) K →* GL (Fin (n - 1)) K :=
  Matrix.SpecialLinearGroup.toGL.comp
    (reindexSpecialLinear ((Finset.univ.erase i).equivFin.trans
      (finCongr (card_univ_erase i)))).toMonoidHom

theorem orthToGL_injective (i : Fin n) : Function.Injective (orthToGL K i) :=
  Matrix.SpecialLinearGroup.toGL_injective.comp (MulEquiv.injective _)

theorem coe_orthToGL (i : Fin n) (B : SpecialLinearGroup (Finset.univ.erase i) K) :
    ((orthToGL K i B : GL (Fin (n - 1)) K) : Matrix (Fin (n - 1)) (Fin (n - 1)) K) =
      (B : Matrix (Finset.univ.erase i) (Finset.univ.erase i) K).submatrix
        ((Finset.univ.erase i).equivFin.trans (finCongr (card_univ_erase i))).symm
        ((Finset.univ.erase i).equivFin.trans (finCongr (card_univ_erase i))).symm :=
  rfl

theorem map_orthSL_eq [CharP K 2] (i : Fin n) :
    (orthSL K (Finset.univ.erase i)).map (orthToGL K i) =
      matrixIsometryGroup ((1 : GL (Fin (n - 1)) K) : Matrix (Fin (n - 1)) (Fin (n - 1)) K) := by
  set ε := (Finset.univ.erase i).equivFin.trans (finCongr (card_univ_erase i)) with hε
  ext g
  constructor
  · rintro ⟨B, hB, rfl⟩
    have hB' : (B : Matrix (Finset.univ.erase i) (Finset.univ.erase i) K)ᵀ * B = 1 := hB
    rw [mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one, coe_orthToGL, transpose_submatrix,
      submatrix_mul_equiv, hB', submatrix_one_equiv]
  · intro hg
    have hg' := mem_matrixIsometryGroup.mp hg
    rw [Units.val_one, Matrix.mul_one] at hg'
    have hdet : (g : Matrix (Fin (n - 1)) (Fin (n - 1)) K).det = 1 :=
      CFSG.ComponentClassification.UnbalancedCatalog.det_eq_one_of_mem_matrixIsometryGroup hg
    set A : SpecialLinearGroup (Fin (n - 1)) K := ⟨g, hdet⟩ with hA
    refine ⟨(reindexSpecialLinear ε).symm A, ?_, ?_⟩
    · change (((reindexSpecialLinear ε).symm A :
        Matrix.SpecialLinearGroup (Finset.univ.erase i) K) :
        Matrix (Finset.univ.erase i) (Finset.univ.erase i) K)ᵀ *
          ((reindexSpecialLinear ε).symm A : Matrix.SpecialLinearGroup (Finset.univ.erase i) K) = 1
      have hc : (((reindexSpecialLinear ε).symm A :
          Matrix.SpecialLinearGroup (Finset.univ.erase i) K) :
          Matrix (Finset.univ.erase i) (Finset.univ.erase i) K) =
            (g : Matrix (Fin (n - 1)) (Fin (n - 1)) K).submatrix ε ε := rfl
      rw [hc, transpose_submatrix, submatrix_mul_equiv, hg', submatrix_one_equiv]
    · apply Units.ext
      change ((reindexSpecialLinear ε ((reindexSpecialLinear ε).symm A) :
        SpecialLinearGroup (Fin (n - 1)) K) : Matrix (Fin (n - 1)) (Fin (n - 1)) K) = g
      rw [MulEquiv.apply_symm_apply]

@[expose] noncomputable def orthEquivIsometry [CharP K 2] (i : Fin n) :
    orthSL K (Finset.univ.erase i) ≃*
      matrixIsometryGroup ((1 : GL (Fin (n - 1)) K) : Matrix (Fin (n - 1)) (Fin (n - 1)) K) :=
  ((orthSL K _).equivMapOfInjective _ (orthToGL_injective i)).trans
    (MulEquiv.subgroupCongr (map_orthSL_eq i))

theorem nonempty_levi_mulEquiv_statedSp [CharP K 2] {r : ℕ} (hr : n = 2 * r + 2) (i : Fin n) :
    Nonempty (levi (K := K) i ≃* StatedSp r K) := by
  have hm : n - 1 = 2 * r + 1 := by omega
  obtain ⟨e₀⟩ := CFSG.ComponentClassification.OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_isAlt (k := K) (n := n - 1))
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_nondegenerate hm)
    (CFSG.ComponentClassification.OutcomeLocal.finrank_dotForm_ker hm)
  exact ⟨(leviEquivOrth i).trans ((orthEquivIsometry i).trans
    ((CFSG.ComponentClassification.OutcomeLocal.oneRestrictEquiv hm).trans e₀))⟩

end Isometry

section Spec

theorem isPerfect_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [Group.IsPerfect H] : Group.IsPerfect G :=
  Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem levi_spec [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ}
    (hr : n = 2 * r + 2) (hr1 : 1 ≤ r) (i : Fin n) :
    IsSimpleGroup (levi (K := K) i) ∧ ⁅levi (K := K) i, levi (K := K) i⁆ = levi i ∧
      ∀ θ ρ : MulAut (levi (K := K) i), θ * ρ * θ⁻¹ * ρ⁻¹ ∈ inner (levi (K := K) i) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨e⟩ := nonempty_levi_mulEquiv_statedSp (K := K) hr i
  rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
  · set e' : levi (K := K) i ≃* SpecialLinearGroup (Fin 2) K :=
      e.trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm with he'
    have hs : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) :=
      CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup hq
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      InvPlacement.isPerfect_specialLinearGroup_of_four_le hq (Fin 2)
    have : Group.IsPerfect (levi (K := K) i) := isPerfect_of_mulEquiv e'
    refine ⟨e'.isSimpleGroup_congr.2 hs, Subgroup.commutator_eq_self, ?_⟩
    have hcyc := CFSG.RankThree.PartOne.KCRootAxis.out_sl2_isCyclic (K := K)
    exact commutatorElement_mem_inner_of_mulEquiv e' (fun a b => hcyc.commGroup.mul_comm a b)
  · have : NeZero r := ⟨by omega⟩
    set e₃ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
      MulEquiv.ofBijective _ UnitaryHigher.proj_bijective_of_charTwo with he₃
    set e' : levi (K := K) i ≃* StatedProj (StatedSp r K) := e.trans e₃ with he'
    have hne : ¬(r = 2 ∧ Nat.card K = 2) := fun h => by omega
    obtain ⟨hs, hp⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr2 hne
    have : Group.IsPerfect (levi (K := K) i) := isPerfect_of_mulEquiv e'
    refine ⟨e'.isSimpleGroup_congr.2 hs, Subgroup.commutator_eq_self, ?_⟩
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
    · exact commutatorElement_mem_inner_of_mulEquiv e' (statedSp_two_outer_comm hK)
    · exact commutatorElement_mem_inner_of_mulEquiv e' (statedSp_outer_comm hr3)

end Spec

end Nonalt

end CFSG.SeitzReduction.LinearPilot
