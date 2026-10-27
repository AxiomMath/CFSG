module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic
import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.ModelFacts

section CharTwo

variable {K : Type} [Field K] [CharP K 2]

private def tSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 1], by rw [det_fin_two_of, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]⟩

private def sSL : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by rw [det_fin_two_of]; simp⟩

private theorem tSL_cube : tSL * tSL * tSL = (1 : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  change (!![0, 1; 1, 1] * !![0, 1; 1, 1] * !![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    (1 : Matrix (Fin 2) (Fin 2) K) i j
  rw [mul_fin_two, mul_fin_two, one_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem tSL_ne_one : tSL (K := K) ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [tSL] at this

private theorem sSL_mul_self : sSL * sSL = (1 : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  change (!![1, 1; 0, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    (1 : Matrix (Fin 2) (Fin 2) K) i j
  rw [mul_fin_two, one_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem sSL_mul_tSL_mul_sSL :
    sSL * tSL * sSL = (tSL * tSL : SpecialLinearGroup (Fin 2) K) := by
  ext i j
  change (!![1, 1; 0, 1] * !![0, 1; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    (!![0, 1; 1, 1] * !![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j
  rw [mul_fin_two, mul_fin_two, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

private theorem sSL_mul_tSL_mul_inv :
    sSL * tSL * sSL⁻¹ = (tSL : SpecialLinearGroup (Fin 2) K)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right sSL_mul_self, sSL_mul_tSL_mul_sSL,
    inv_eq_of_mul_eq_one_right (a := tSL) (b := tSL * tSL) (by rw [← mul_assoc]; exact tSL_cube)]

private noncomputable def hP (k : Fin 4) : StatedSp 4 K := longBlock K 4 k tSL

private noncomputable def wP (k : Fin 4) : StatedSp 4 K := longBlock K 4 k sSL

private theorem hP_comm (i j : Fin 4) : Commute (hP (K := K) i) (hP j) := by
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · exact commute_longBlock_longBlock hij _ _

private theorem hP_ord (i : Fin 4) : orderOf (hP (K := K) i) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [hP, ← map_pow, pow_succ, sq, tSL_cube, map_one]
  · intro h
    have h' : longBlock K 4 i (tSL : SpecialLinearGroup (Fin 2) K) = 1 := h
    exact tSL_ne_one (longBlock_injective i (h'.trans (map_one _).symm))

private theorem wP_inv (i : Fin 4) : wP i * hP i * (wP (K := K) i)⁻¹ = (hP i)⁻¹ := by
  rw [wP, hP, ← map_inv, ← map_mul, ← map_mul, sSL_mul_tSL_mul_inv, map_inv]

private theorem wP_fix (i j : Fin 4) (hij : i ≠ j) :
    wP i * hP j * (wP (K := K) i)⁻¹ = hP j :=
  (commute_longBlock_longBlock hij _ _).mul_inv_cancel

end CharTwo

section Generation

variable {K : Type} [Field K] [CharP K 2]

private theorem hP_mem_supp (k : Fin 4) : hP (K := K) k ∈ suppGroup (K := K) (coords k) := by
  rw [← range_longBlock]
  exact ⟨tSL, rfl⟩

private theorem exists_compl_pair :
    ∀ a b : Fin 4, a ≠ b → ∃ k l : Fin 4, k ≠ l ∧ k ≠ a ∧ k ≠ b ∧ l ≠ a ∧ l ≠ b := by
  decide

theorem liftableNormalizerGen_statedSp : LiftableNormalizerGen (StatedSp 4 K) := by
  refine liftableNormalizerGen_of_inverters (hP (K := K)) wP hP_comm hP_ord wP_inv wP_fix ?_
  refine eq_top_of_forall_pair_le (by norm_num) _ fun a b hab x hx => ?_
  obtain ⟨k, l, hkl, hka, hkb, hla, hlb⟩ := exists_compl_pair a b hab
  have hc : ∀ m : Fin 4, m ≠ a → m ≠ b → Commute x (hP m) := fun m hma hmb =>
    commute_suppGroup_compl hx (suppGroup_mono (fun z hz hz' => by
      rcases hz' with hz' | hz'
      · exact coords_subset_compl hma hz hz'
      · exact coords_subset_compl hmb hz hz') (hP_mem_supp m))
  exact Subgroup.subset_closure (Or.inl ⟨k, l, hkl, hc k hka hkb, hc l hla hlb⟩)

end Generation

section Carrier

open TauCeti

theorem liftableNormalizerGen_B4Two (q : PrimePower) (hv : (LieTypeIndex.B 4 q).Valid)
    (hp : q.p = 2) (_he : q.exponent = 1) :
    LiftableNormalizerGen (ValidLieTypeIndex.Group ⟨.B 4 q, hv⟩) := by
  have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B 4 q, hv⟩) 2 := by
    have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B 4 q, hv⟩)
        (ValidLieTypeIndex.characteristic ⟨.B 4 q, hv⟩) := inferInstance
    exact CharP.congr (ValidLieTypeIndex.characteristic ⟨.B 4 q, hv⟩)
      ((LieTypeIndex.characteristic_B 4 q).trans hp)
  exact liftableNormalizerGen_statedSp.of_mulEquiv
    ((CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 4 q hv hp
      (by norm_num)).trans (CFSG.LieType.SteinbergBR.EvenSp.projEquiv (by norm_num))).symm

end Carrier

end CFSG.AGLEmbedding
