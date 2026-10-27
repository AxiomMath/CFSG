module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabChain
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabSwap

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.StandardType.QTwo

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem smul_flagChamber_eq_of_blockEmb_window {m a len : ℕ}
    (h : a + len ≤ m + 1) (A : Su K 2 1 len)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
        (blockEmb K 2 1 (m + 1) len a h A))
    {j : Fin (m + 1)}
    (hj : j.val = m ∨ (j.val + 1 = m ∧ a + len ≤ m) ∨
      (j.val + 1 < m ∧ (a + len ≤ j.val + 1 ∨ j.val + 1 ≤ a))) :
    x • flagChamber E m j = flagChamber E m j := by
  apply Subtype.ext
  rw [coe_smul_flagVert, coe_flagChamber]
  have hx' : ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :
      (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
      (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
        (blockEmb K 2 1 (m + 1) len a h A) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) :=
    congrArg LinearEquiv.toLinearMap hx
  rw [hx']
  rcases hj with hj | hj
  · have hlast : j = Fin.last m := Fin.ext (by simpa using hj)
    rw [hlast, stdDChamber_elt_last_eq_coordSpan]
    exact map_coordSpan_eq_of_blockEmb (K := K) E h A
      (Or.inl (fun i _ _ => Set.mem_univ i)) (Or.inr (fun _ hj => by simp at hj))
  · rcases hj with hj | hj
    · rcases hj with ⟨hj, hle⟩
      have hjlast : j ≠ Fin.last m := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_last] at this
        omega
      rw [stdDChamber_elt_eq_alt_coordSpan hjlast hj]
      refine map_coordSpan_eq_of_blockEmb (K := K) E h A (Or.inl ?_) (Or.inr ?_)
      · intro i hi₁ hi₂
        simp only [Set.mem_setOf_eq]
        omega
      · intro j' hj'
        simp only [Set.mem_singleton_iff] at hj'
        subst hj'
        simp only [Fin.val_last]
        omega
    · rcases hj with ⟨hj, hle⟩
      have hjlast : j ≠ Fin.last m := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_last] at this
        omega
      have hjm : j.val + 1 ≠ m := by omega
      rw [stdDChamber_elt_eq_sub_coordSpan hjlast hjm]
      refine map_coordSpan_eq_of_blockEmb (K := K) E h A ?_
        (Or.inr (fun _ hj => by simp at hj))
      rcases hle with hle | hle
      · left
        intro i hi₁ hi₂
        simp only [Set.mem_setOf_eq]
        omega
      · right
        intro i hi₁ hi₂
        simp only [Set.mem_setOf_eq] at hi₁
        omega

theorem qTwoStdFamily_levi_le_qTwoParab_of_last_not_mem (hK : Nat.card K = 4)
    (m : ℕ) (hm : 3 ≤ m) {C : Set (Fin (m + 1))} (hlast : Fin.last m ∉ C) :
    (qTwoStdFamily E hK m hm).levi C ≤ qTwoParab E m C := by
  refine (qTwoStdFamily E hK m hm).levi_le_of_forall_lt ?_ ?_
  · intro i hi
    rintro x ⟨a, rfl⟩
    rw [mem_qTwoParab]
    intro j hj
    have hi_ne_last : i ≠ Fin.last m := fun heq => hlast (heq ▸ hi)
    rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | hi_last
    · have hval : (((qTwoStdFamily E hK m hm).ι (Fin.castSucc k) a :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
          suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
            (blockEmb K 2 1 (m + 1) 2 k.val (by omega) a) := by
        change ((qTwoStdIota E m hm (Fin.castSucc k) a :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = _
        rw [coe_qTwoStdIota_castSucc]
        rfl
      have hklt := k.isLt
      refine smul_flagChamber_eq_of_blockEmb_window E (a := k.val) (len := 2)
        (by omega) a hval ?_
      have hne : j.val ≠ k.val := by
        intro hjk
        apply hj
        have hjeq : j = Fin.castSucc k := Fin.ext (by simpa using hjk)
        exact hjeq.symm ▸ hi
      rcases Nat.lt_or_ge j.val m with hjm | hjm
      · by_cases hjpen : j.val + 1 = m
        · exact Or.inr (Or.inl ⟨hjpen, by omega⟩)
        · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    · exact absurd hi_last hi_ne_last
  · intro i hi j hj hij h3
    rintro x ⟨b, rfl⟩
    rw [mem_qTwoParab]
    intro j0 hj0
    have hj_ne_last : j ≠ Fin.last m := fun heq => hlast (heq ▸ hj)
    rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | hj_last
    · have hlt : i.val < j'.val := by
        rw [Fin.lt_def] at hij
        simpa using hij
      have h3' := (qtwoLabel_three_iff hm i (Fin.castSucc j')).mp h3
      simp only [Fin.val_castSucc] at h3'
      have hval_ij : i.val + 1 = j'.val := by omega
      have hival : i.val + 3 ≤ m + 1 := by
        have := j'.isLt
        omega
      have hval : (((qTwoStdFamily E hK m hm).θ i (Fin.castSucc j') b :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
          suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
            (blockEmb K 2 1 (m + 1) 3 i.val hival b) := by
        change ((qTwoStdTheta E m hm i (Fin.castSucc j') b :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = _
        rw [coe_qTwoStdTheta_chain E m hm hval_ij b]
        rfl
      refine smul_flagChamber_eq_of_blockEmb_window E (a := i.val) (len := 3)
        hival b hval ?_
      have hne_i : j0.val ≠ i.val := by
        intro hji
        apply hj0
        have hjeq : j0 = i := Fin.ext hji
        exact hjeq.symm ▸ hi
      have hne_j : j0.val ≠ j'.val := by
        intro hjj
        apply hj0
        have hjeq : j0 = Fin.castSucc j' := Fin.ext (by simpa using hjj)
        exact hjeq.symm ▸ hj
      have hlt_j := j'.isLt
      rcases Nat.lt_or_ge j0.val m with hjm | hjm
      · by_cases hjpen : j0.val + 1 = m
        · exact Or.inr (Or.inl ⟨hjpen, by omega⟩)
        · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
          rcases lt_or_gt_of_ne hne_i with hlt | hgt
          · exact Or.inr (by omega)
          · have hne_ij : j0.val ≠ i.val + 1 := by
              intro heq
              exact hne_j (by omega)
            exact Or.inl (by omega)
      · exact Or.inl (by omega)
    · exact absurd hj_last hj_ne_last

theorem qTwoStdFamily_levi_le_qTwoParab_of_pen_not_mem (hK : Nat.card K = 4)
    (m : ℕ) (hm : 3 ≤ m) {C : Set (Fin (m + 1))}
    (hpen : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C) :
    (qTwoStdFamily E hK m hm).levi C ≤ qTwoParab E m C := by
  have hlast : Fin.last m ∉ qTwoForkSwap m hm '' C := by
    rintro ⟨c, hc, hcs⟩
    have hcs' : qTwoForkSwap m hm (qTwoForkSwap m hm c) =
        qTwoForkSwap m hm (Fin.last m) := congrArg (qTwoForkSwap m hm) hcs
    rw [qTwoForkSwap_apply_apply, qTwoForkSwap_apply_last] at hcs'
    exact hpen (hcs' ▸ hc)
  have hle := qTwoStdFamily_levi_le_qTwoParab_of_last_not_mem E hK m hm hlast
  have hmap : ((qTwoStdFamily E hK m hm).levi C).map (conjTau E).toMonoidHom ≤
      (qTwoParab E m C).map (conjTau E).toMonoidHom := by
    rw [map_qTwoLevi_conjTau E hK m hm C, map_qTwoParab_conjTau E m hm C]
    exact hle
  exact (Subgroup.map_le_map_iff_of_injective (conjTau E).injective).mp hmap

private theorem levi_singleton_le_qTwoParab (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (i : Fin (m + 1)) :
    (qTwoStdFamily E hK m hm).levi ({i} : Set (Fin (m + 1))) ≤ qTwoParab E m {i} := by
  by_cases hi : i = Fin.last m
  · subst hi
    refine qTwoStdFamily_levi_le_qTwoParab_of_pen_not_mem E hK m hm ?_
    intro hmem
    have hpen : m - 1 = m := congrArg Fin.val hmem
    omega
  · exact qTwoStdFamily_levi_le_qTwoParab_of_last_not_mem E hK m hm
      (by intro hmem; exact hi hmem.symm)

private theorem levi_pair_le_qTwoParab (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hij : i < j)
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    (qTwoStdFamily E hK m hm).levi ({i, j} : Set (Fin (m + 1))) ≤ qTwoParab E m {i, j} := by
  by_cases hj : j = Fin.last m
  · subst hj
    have h3' := (qtwoLabel_three_iff hm i (Fin.last m)).mp h3
    simp only [Fin.val_last] at h3'
    have hival : i.val = m - 2 := by
      have hlt : i.val < m := by
        rw [Fin.lt_def] at hij
        simpa using hij
      omega
    refine qTwoStdFamily_levi_le_qTwoParab_of_pen_not_mem E hK m hm ?_
    intro hmem
    rcases hmem with hmem | hmem
    · have hpen : m - 1 = i.val := congrArg Fin.val hmem
      omega
    · have hpen : m - 1 = m := congrArg Fin.val hmem
      omega
  · refine qTwoStdFamily_levi_le_qTwoParab_of_last_not_mem E hK m hm ?_
    intro hmem
    rcases hmem with hmem | hmem
    · have hival : i.val = m := by
        have := congrArg Fin.val hmem
        simpa using this.symm
      have hjval := j.isLt
      rw [Fin.lt_def] at hij
      omega
    · exact hj hmem.symm

theorem qTwoStdFamily_levi_le_qTwoParab (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (C : Set (Fin (m + 1))) :
    (qTwoStdFamily E hK m hm).levi C ≤ qTwoParab E m C := by
  refine (qTwoStdFamily E hK m hm).levi_le_of_forall_lt ?_ ?_
  · intro i hi
    exact ((qTwoStdFamily E hK m hm).le_levi_node (C := {i}) (by simp)).trans
      ((levi_singleton_le_qTwoParab E hK m hm i).trans
        (qTwoParab_mono E (Set.singleton_subset_iff.mpr hi)))
  · intro i hi j hj hij h3
    exact ((qTwoStdFamily E hK m hm).le_levi_edge (C := {i, j}) (by simp) (by simp) h3).trans
      ((levi_pair_le_qTwoParab E hK m hm hij h3).trans
        (qTwoParab_mono E (by
          intro x hx
          rcases hx with rfl | rfl
          · exact hi
          · exact hj)))

end CFSG.ClassicalInvolution.PhanDn.QTwo
