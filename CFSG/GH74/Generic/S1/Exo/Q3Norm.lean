module

public import CFSG.GH74.Generic.S1.BlkSplit
public import CFSG.GH74.Generic.S1.Defs

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic.S1

theorem isBlockAt_conj_of_splitAt {F : Type} [Field F] {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {G G' : Matrix (Fin 4) (Fin 4) F} (hG : SplitAt a b c d G) (hG' : SplitAt a b c d G')
    (hGG' : G * G' = 1) {m : Matrix (Fin 4) (Fin 4) F} (hm : IsBlockAt c d m) :
    IsBlockAt c d (G * m * G') := by
  have hN : ∀ k l, ¬ ((k = c ∨ k = d) ∧ (l = c ∨ l = d)) → (m - 1) k l = 0 := by
    intro k l h
    rw [Matrix.sub_apply, hm k l h, sub_self]
  have hconj : G * m * G' = 1 + G * (m - 1) * G' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hGG']
    abel
  intro i j hij
  rw [hconj, Matrix.add_apply]
  suffices h : (G * (m - 1) * G') i j = 0 by rw [h, add_zero]
  by_cases hi : i = c ∨ i = d
  · have hj : ¬ (j = c ∨ j = d) := fun hj => hij ⟨hi, hj⟩
    have hj' : j = a ∨ j = b := by
      rcases fin4_cover hab hac had hbc hbd hcd j with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (Or.inl h) hj
      · exact absurd (Or.inr h) hj
    have hMG : ∀ k, ((m - 1) * G') k j = 0 := by
      intro k
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = c ∨ l = d
      · rw [hG' l j (Or.inr ⟨hl, hj'⟩), mul_zero]
      · rw [hN k l (fun h => hl h.2), zero_mul]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [hMG k, mul_zero]
  · have hi' : i = a ∨ i = b := by
      rcases fin4_cover hab hac had hbc hbd hcd i with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (Or.inl h) hi
      · exact absurd (Or.inr h) hi
    have hGM : ∀ l, (G * (m - 1)) i l = 0 := by
      intro l
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = c ∨ k = d
      · rw [hG i k (Or.inl ⟨hi', hk⟩), zero_mul]
      · rw [hN k l (fun h => hk h.1), mul_zero]
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [hGM l, zero_mul]

theorem blkLin_conj_mem_of_splitAt {F : Type} [Field F] {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {g : ↥(StatedSL 4 F)}
    (hg : SplitAt a b c d (((g : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hgi : SplitAt a b c d (((g⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    ∀ m ∈ blkLin (F := F) c d, g * m * g⁻¹ ∈ blkLin (F := F) c d := by
  intro m hm
  have hGGi : (((g : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (((g⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have h1 : ((g : GL (Fin 4) F) * (g : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) = 1 := mul_inv_cancel _
    have h2' := congrArg Units.val h1
    rw [Units.val_mul, Units.val_one] at h2'
    exact h2'
  rw [mem_blkLin]
  have := isBlockAt_conj_of_splitAt hab hac had hbc hbd hcd hg hgi hGGi (mem_blkLin.1 hm)
  simpa [Units.val_mul] using this

theorem blkLin_conj_mem_of_comm {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {z0 : ↥(StatedSL 4 F)} (hz0 : z0 ∈ blkLin (F := F) a b) (hz0sq : z0 * z0 = 1) (hz01 : z0 ≠ 1)
    {g : ↥(StatedSL 4 F)} (hg : g * z0 = z0 * g) :
    (∀ m ∈ blkLin (F := F) c d, g * m * g⁻¹ ∈ blkLin (F := F) c d) ∧
      (∀ m ∈ blkLin (F := F) a b, g * m * g⁻¹ ∈ blkLin (F := F) a b) := by
  have hz0mat : (((z0 : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      zblkMat F a b := by
    refine eq_zblk_of_involution h2 hab (fun i j hij => hz0 i j hij) ?_ ?_ ?_
    · have := congrArg
        (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hz0sq
      simpa using this
    · have h1 : ((z0 : ↥(StatedSL 4 F)) : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact z0.2
      rw [mem_detOne] at h1
      exact h1
    · intro h
      apply hz01
      exact Subtype.ext (Units.ext (by simpa using h))
  have hsplit : ∀ x : ↥(StatedSL 4 F), x * z0 = z0 * x →
      SplitAt a b c d (((x : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro x hx
    refine SplitAt.symm (splitAt_of_comm h2 hac.symm hbc.symm had.symm hbd.symm ?_)
    have := congrArg
      (fun y : ↥(StatedSL 4 F) => ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hx
    simpa [hz0mat] using this
  have hgs := hsplit g hg
  have hgis := hsplit g⁻¹ (Commute.inv_left (show Commute g z0 from hg))
  exact ⟨blkLin_conj_mem_of_splitAt hab hac had hbc hbd hcd hgs hgis,
    blkLin_conj_mem_of_splitAt hcd hac.symm hbc.symm had.symm hbd.symm hab
      hgs.symm hgis.symm⟩

end CFSG.GH74.Generic.S1.Exo
