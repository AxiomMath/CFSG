module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I269Six

open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.Fischer

abbrev UG : Subgroup (GL (Fin 6) F4) := primeFormUnitary hF4 (idGram F4 6)

theorem isSolvable_of_no_perfect {H : Type} [Group H] [Finite H]
    (h : ∀ K : Subgroup H, ⁅K, K⁆ = K → K = ⊥) : Group.IsSolvable H := by
  rw [isSolvable_iff_commutator_lt]
  intro K hK
  refine lt_of_le_of_ne ?_ ?_
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  · intro he
    exact hK (h K he)

theorem card_blk_add_rank (d : Fin 6 → F4) (c : F4) :
    Fintype.card (Blk d c) + (Matrix.diagonal d - Matrix.scalar (Fin 6) c).rank = 6 := by
  have hD : Matrix.diagonal d - Matrix.scalar (Fin 6) c = Matrix.diagonal (fun i => d i - c) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal_apply, Matrix.scalar_apply]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.scalar_apply, Matrix.one_apply_ne hij]
  rw [hD, Matrix.rank_diagonal]
  have h1 : Fintype.card {i // d i - c ≠ 0} = Fintype.card {i : Fin 6 // ¬ d i = c} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by simp [sub_eq_zero])
  rw [h1, Fintype.card_subtype_compl]
  have hle : Fintype.card {i : Fin 6 // d i = c} ≤ 6 := by
    simpa using Fintype.card_subtype_le (fun i : Fin 6 => d i = c)
  simp only [Blk, Fintype.card_fin]
  omega

theorem rank_conj_sub_scalar (Q : GL (Fin 6) F4) (A : Matrix (Fin 6) (Fin 6) F4) (c : F4) :
    ((Q : Matrix (Fin 6) (Fin 6) F4) * A * ((Q⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) -
      Matrix.scalar (Fin 6) c).rank = (A - Matrix.scalar (Fin 6) c).rank := by
  have hQQ : (Q : Matrix (Fin 6) (Fin 6) F4) * ((Q⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
      = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsc := (Matrix.scalar_commute c (fun _ => Commute.all _ _)
    (Q : Matrix (Fin 6) (Fin 6) F4)).eq
  have hs : (Q : Matrix (Fin 6) (Fin 6) F4) * Matrix.scalar (Fin 6) c *
      ((Q⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Matrix.scalar (Fin 6) c := by
    rw [← hsc, mul_assoc, hQQ, mul_one]
  have e : (Q : Matrix (Fin 6) (Fin 6) F4) * (A - Matrix.scalar (Fin 6) c) *
      ((Q⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (Q : Matrix (Fin 6) (Fin 6) F4) * A * ((Q⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) -
      Matrix.scalar (Fin 6) c := by
    rw [mul_sub, sub_mul, hs]
  have hQ : IsUnit (Q : Matrix (Fin 6) (Fin 6) F4).det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Q)
  have hQi : IsUnit (((Q⁻¹ : GL (Fin 6) F4)) : Matrix (Fin 6) (Fin 6) F4).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (Q⁻¹))
  rw [← e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQi, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hQ]

theorem bot_of_perfect_rank {J : Subgroup M6} (hperf : ⁅J, J⁆ = J) {h : GL (Fin 6) F4}
    (hh : h ∈ UG) (h3 : h ^ 3 = 1)
    (hJ : ∀ u ∈ J, (u : GL (Fin 6) F4) * h = h * (u : GL (Fin 6) F4))
    (hrk : ∀ c : F4, 3 ≤ ((h : Matrix (Fin 6) (Fin 6) F4) - Matrix.scalar (Fin 6) c).rank) :
    J = ⊥ := by
  obtain ⟨P, d, hd⟩ := exists_diag6 ⟨h, hh⟩ (by apply Subtype.ext; simpa using h3)
  set Q : UG := P⁻¹ with hQ
  have hDd : (((Q : GL (Fin 6) F4) * h * (Q : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := by
    rw [← hd]
    simp [hQ, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  have hJle : J ≤ (CenD h) := fun u hu => mem_CenD.2 (hJ u hu)
  have hJ' : J.map (conjM6 Q).toMonoidHom ≤ CenD ((Q : GL (Fin 6) F4) * h * (Q : GL (Fin 6) F4)⁻¹) := by
    rw [← map_CenD_conj]
    exact Subgroup.map_mono hJle
  have hcnt : ∀ c : F4, Fintype.card (Blk d c) ≤ 3 := by
    intro c
    have h1 := card_blk_add_rank d c
    have h2 : (Matrix.diagonal d - Matrix.scalar (Fin 6) c).rank =
        (((h : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) - Matrix.scalar (Fin 6) c).rank := by
      rw [← hDd, Units.val_mul, Units.val_mul]
      exact rank_conj_sub_scalar Q _ c
    have h3' := hrk c
    omega
  have hperf' : ⁅J.map (conjM6 Q).toMonoidHom, J.map (conjM6 Q).toMonoidHom⁆ =
      J.map (conjM6 Q).toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have hbot := eq_bot_of_perfect_of_small hDd hcnt hJ' hperf'
  refine (Subgroup.eq_bot_iff_forall J).2 fun u hu => ?_
  have hmem : conjM6 Q u ∈ J.map (conjM6 Q).toMonoidHom := Subgroup.mem_map_of_mem _ hu
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (Subgroup.mem_bot).2 ((conjM6 Q).injective (by simpa using hmem))

end CFSG.LocalAnalysis.GLTheoremA.I269Six

end
