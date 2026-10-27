module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaSiegInputs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpALevi

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open scoped commutatorElement

variable {K : Type} [Field K] {n j : ℕ}

section Products

variable (hjn : 2 * j ≤ n)
include hjn

theorem single_spAPar_mul_spARepMat_two (a : Fin n) {b : Fin n} (hb : b.val < 2 * j) (c : K) :
    single a (spAPar b) c * spARepMat n j = single a b c := by
  ext x y
  by_cases hx : x = a
  · subst hx
    rw [single_mul_apply_same, spARepMat_apply hjn, Matrix.single_apply]
    by_cases hy : y = b
    · subst hy
      simp [hb]
    · rw [ite_eq_right (fun h => hy (by rw [← spAPar_spAPar hjn h.1, ← h.2,
          spAPar_spAPar hjn hb])), ite_eq_right (fun h => hy h.2.symm), mul_zero]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hx, Matrix.single_apply,
      ite_eq_right (fun h => hx h.1.symm)]

theorem spARepMat_mul_single_spAPar_two {a : Fin n} (ha : a.val < 2 * j) (b : Fin n) (c : K) :
    spARepMat n j * single (spAPar a) b c = single a b c := by
  ext x y
  by_cases hy : y = b
  · subst hy
    rw [mul_single_apply_same, spARepMat_apply hjn, Matrix.single_apply, spAPar_spAPar hjn ha]
    by_cases hx : x = a
    · subst hx
      simp [spAPar_lt hjn ha]
    · rw [ite_eq_right (fun h => hx h.2), ite_eq_right (fun h => hx h.1.symm), zero_mul]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hy, Matrix.single_apply,
      ite_eq_right (fun h => hy h.2.symm)]

end Products

section Radical

variable [CharP K 2] (hjn : 2 * j ≤ n)
include hjn

theorem siegPair_mem_commutator_two {k l : Fin n} (hk : k.val < 2 * j) (hlp : l ≠ spAPar k)
    (c : K) :
    siegPair K k l c ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hkp : k ≠ spAPar k := Ne.symm (spAPar_ne hjn hk)
  have h1 : single k (spAPar k) (1 : K) * single (spAPar k) l c = single k l c := by
    rw [single_mul_single_same, one_mul]
  have h2 : single k (spAPar k) (1 : K) * single l (spAPar k) c = 0 :=
    single_mul_single_of_ne _ _ _ _ (Ne.symm hlp) _
  have h3 : single (spAPar k) l c * single (spAPar k) k (1 : K) = 0 :=
    single_mul_single_of_ne _ _ _ _ hlp _
  have h4 : single l (spAPar k) c * single (spAPar k) k (1 : K) = single l k c := by
    rw [single_mul_single_same, mul_one]
  have h5 : single k l c * single (spAPar k) k (1 : K) = 0 :=
    single_mul_single_of_ne _ _ _ _ hlp _
  have e : ⁅leviTv K hkp (1 : K), siegPair K (spAPar k) l c⁆ = siegPair K k l c := by
    rw [leviTv, siegPair, commutatorElement_leviEmbedGL_upperUnipotentSp, siegPair]
    refine upperUnipotentSp_congr _ _ ?_
    rw [TauCeti.coe_transvectionUnit, Matrix.transvection, transpose_add, transpose_one,
      transpose_single]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2, h3, h4, h5,
      add_zero]
    abel
  rw [← e]
  exact commutator_mem_commutator (leviTv_spAPar_mem_centralizer hjn hk)
    (upperUnipotentSp_mem_centralizer_spARep _)

theorem siegPair_spAPar_mul_siegDiag_mem_commutator_two {k : Fin n} (hk : k.val < 2 * j)
    (c : K) :
    siegPair K k (spAPar k) c * siegDiag K k c ∈
      ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
        centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hkp : k ≠ spAPar k := Ne.symm (spAPar_ne hjn hk)
  have e : ⁅leviTv K hkp (1 : K), siegDiag K (spAPar k) c⁆ =
      siegPair K k (spAPar k) c * siegDiag K k c := by
    rw [leviTv, siegDiag, commutatorElement_leviEmbedGL_upperUnipotentSp, siegPair, siegDiag,
      upperUnipotentSp_mul]
    refine upperUnipotentSp_congr _ _ ?_
    rw [TauCeti.coe_transvectionUnit, Matrix.transvection, transpose_add, transpose_one,
      transpose_single]
    simp only [Matrix.add_mul, Matrix.mul_add, single_mul_single_same, one_mul, mul_one]
    abel
  rw [← e]
  exact commutator_mem_commutator (leviTv_spAPar_mem_centralizer hjn hk)
    (upperUnipotentSp_mem_centralizer_spARep _)


theorem siegDiag_mem_commutator_two {k m : Fin n} (hk : k.val < 2 * j) (hm : m.val < 2 * j)
    (hmk : m ≠ k) (hmp : m ≠ spAPar k) (c : K) :
    siegDiag K k c ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  set H := ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
    centralizer ({spARep n j} : Set (StatedSp n K))⁆ with hH
  have hkk : k ≠ spAPar k := Ne.symm (spAPar_ne hjn hk)
  have hmm : m ≠ spAPar m := Ne.symm (spAPar_ne hjn hm)
  have hkm' : k ≠ spAPar m := fun h => hmp (by rw [h, spAPar_spAPar hjn hm])
  have hk'm' : spAPar k ≠ spAPar m := fun h =>
    hmk (by rw [← spAPar_spAPar hjn hm, ← h, spAPar_spAPar hjn hk])
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin n) K,
      A = TauCeti.transvectionUnit hkm' (1 : K) * TauCeti.transvectionUnit hmp (1 : K) :=
    ⟨_, rfl⟩
  have h0 : single k (spAPar m) (1 : K) * single m (spAPar k) 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ (Ne.symm hmm) _
  have hAm : (A : Matrix (Fin n) (Fin n) K) =
      1 + single k (spAPar m) 1 + single m (spAPar k) 1 := by
    rw [hA, Units.val_mul, TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit,
      Matrix.transvection, Matrix.transvection]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h0, add_zero]
  have hAt : (A : Matrix (Fin n) (Fin n) K)ᵀ =
      1 + single (spAPar m) k 1 + single (spAPar k) m 1 := by
    rw [hAm, transpose_add, transpose_add, transpose_one, transpose_single, transpose_single]
  have hE1S : single k (spAPar m) (1 : K) * spARepMat n j = single k m 1 :=
    single_spAPar_mul_spARepMat_two hjn k hm 1
  have hE2S : single m (spAPar k) (1 : K) * spARepMat n j = single m k 1 :=
    single_spAPar_mul_spARepMat_two hjn m hk 1
  have hSF1 : spARepMat n j * single (spAPar m) k (1 : K) = single m k 1 :=
    spARepMat_mul_single_spAPar_two hjn hm k 1
  have hSF2 : spARepMat n j * single (spAPar k) m (1 : K) = single k m 1 :=
    spARepMat_mul_single_spAPar_two hjn hk m 1
  have z1 : single k m (1 : K) * single (spAPar m) k 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hmm _
  have z2 : single k m (1 : K) * single (spAPar k) m 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hmp _
  have z3 : single m k (1 : K) * single (spAPar m) k 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hkm' _
  have z4 : single m k (1 : K) * single (spAPar k) m 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hkk _
  have hXX : single k m (1 : K) + single k m 1 = 0 := by
    rw [← Matrix.single_add, one_add_one_eq_two, CharTwo.two_eq_zero, Matrix.single_zero]
  have hYY : single m k (1 : K) + single m k 1 = 0 := by
    rw [← Matrix.single_add, one_add_one_eq_two, CharTwo.two_eq_zero, Matrix.single_zero]
  have hASA : (A : Matrix (Fin n) (Fin n) K) * spARepMat n j * (A : Matrix (Fin n) (Fin n) K)ᵀ =
      spARepMat n j := by
    have key : (A : Matrix (Fin n) (Fin n) K) * spARepMat n j *
        (A : Matrix (Fin n) (Fin n) K)ᵀ =
        spARepMat n j + (single k m 1 + single k m 1) + (single m k 1 + single m k 1) := by
      rw [hAt, hAm]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hE1S, hE2S,
        hSF1, hSF2, z1, z2, z3, z4, add_zero]
      abel
    rw [key, hXX, hYY, add_zero, add_zero]
  have hAC : leviEmbedGL K n A ∈ centralizer ({spARep n j} : Set (StatedSp n K)) :=
    leviEmbedGL_mem_centralizer_spARep hASA
  have w1 : single k (spAPar m) (1 : K) * single (spAPar m) (spAPar m) c =
      single k (spAPar m) c := by
    rw [single_mul_single_same, one_mul]
  have w2 : single m (spAPar k) (1 : K) * single (spAPar m) (spAPar m) c = 0 :=
    single_mul_single_of_ne _ _ _ _ hk'm' _
  have w3 : single (spAPar m) (spAPar m) c * single (spAPar m) k (1 : K) =
      single (spAPar m) k c := by
    rw [single_mul_single_same, mul_one]
  have w4 : single (spAPar m) (spAPar m) c * single (spAPar k) m (1 : K) = 0 :=
    single_mul_single_of_ne _ _ _ _ (Ne.symm hk'm') _
  have w5 : single k (spAPar m) c * single (spAPar m) k (1 : K) = single k k c := by
    rw [single_mul_single_same, mul_one]
  have w6 : single k (spAPar m) c * single (spAPar k) m (1 : K) = 0 :=
    single_mul_single_of_ne _ _ _ _ (Ne.symm hk'm') _
  have e : ⁅leviEmbedGL K n A, siegDiag K (spAPar m) c⁆ =
      siegPair K k (spAPar m) c * siegDiag K k c := by
    rw [siegDiag, commutatorElement_leviEmbedGL_upperUnipotentSp, siegPair, siegDiag,
      upperUnipotentSp_mul]
    refine upperUnipotentSp_congr _ _ ?_
    rw [hAt, hAm]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, w1, w2, w3, w4, w5,
      w6, add_zero]
    abel
  have hpair : siegPair K k (spAPar m) c ∈ H :=
    siegPair_mem_commutator_two hjn hk (Ne.symm hk'm') c
  have hcomm : ⁅leviEmbedGL K n A, siegDiag K (spAPar m) c⁆ ∈ H :=
    commutator_mem_commutator hAC (upperUnipotentSp_mem_centralizer_spARep _)
  rw [e] at hcomm
  have h1 := H.mul_mem (H.inv_mem hpair) hcomm
  rwa [inv_mul_cancel_left] at h1

theorem siegDiag_mem_commutator_of_two_le (hj2 : 2 ≤ j) {k : Fin n} (hk : k.val < 2 * j)
    (c : K) :
    siegDiag K k c ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hv := spAPar_val hjn hk
  by_cases hk2 : k.val < 2
  · exact siegDiag_mem_commutator_two hjn (m := ⟨2, by omega⟩) hk (show 2 < 2 * j by omega)
      (Fin.ne_of_val_ne (show (2 : ℕ) ≠ k.val by omega))
      (Fin.ne_of_val_ne (show (2 : ℕ) ≠ (spAPar k).val by rw [hv]; split_ifs <;> omega)) c
  · exact siegDiag_mem_commutator_two hjn (m := ⟨0, by omega⟩) hk (show 0 < 2 * j by omega)
      (Fin.ne_of_val_ne (show (0 : ℕ) ≠ k.val by omega))
      (Fin.ne_of_val_ne (show (0 : ℕ) ≠ (spAPar k).val by rw [hv]; split_ifs <;> omega)) c

theorem siegPair_spAPar_mem_commutator_of_two_le (hj2 : 2 ≤ j) {k : Fin n}
    (hk : k.val < 2 * j) (c : K) :
    siegPair K k (spAPar k) c ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have h1 := siegPair_spAPar_mul_siegDiag_mem_commutator_two hjn hk c
  have h2 := siegDiag_mem_commutator_of_two_le hjn hj2 hk c
  have h3 := mul_mem h1 (inv_mem h2)
  rwa [mul_inv_cancel_right] at h3

theorem upperUnipotentSp_mem_commutator_two (hj2 : 2 ≤ j) {X : Matrix (Fin n) (Fin n) K}
    (hX : Xᵀ = X)
    (hXs : ∀ a b, X a b ≠ 0 → a.val < 2 * j ∧ b.val < 2 * j) :
    upperUnipotentSp n K hX ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  set H := ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆
  set Xd : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => if a = b then X a b else 0 with hXd
  set Xu : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => if a < b then X a b else 0 with hXu
  have hd : ∀ a b, (single a b (Xd a b))ᵀ = single a b (Xd a b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact transpose_single a a _
    · rw [hXd, of_apply, ite_eq_right hab, Matrix.single_zero, transpose_zero]
  have hu : ∀ a b, (single a b (Xu a b) + single b a (Xu a b))ᵀ =
      single a b (Xu a b) + single b a (Xu a b) := fun a b => by
    rw [transpose_add, transpose_single, transpose_single, add_comm]
  have hone : ∀ {Y : Matrix (Fin n) (Fin n) K} (hY : Yᵀ = Y), Y = 0 →
      upperUnipotentSp n K hY ∈ H := by
    intro Y hY h0
    rw [upperUnipotentSp_congr hY transpose_zero h0, upperUnipotentSp_zero]
    exact H.one_mem
  have hdmem : ∀ a b, upperUnipotentSp n K (hd a b) ∈ H := by
    intro a b
    by_cases hab : a = b
    · subst hab
      by_cases h0 : X a a = 0
      · exact hone _ (by rw [hXd, of_apply, ite_eq_left rfl, h0, Matrix.single_zero])
      · rw [upperUnipotentSp_congr (hd a a) (transpose_single a a (X a a))
          (by rw [hXd, of_apply, ite_eq_left rfl])]
        exact siegDiag_mem_commutator_of_two_le hjn hj2 (hXs a a h0).1 (X a a)
    · exact hone _ (by rw [hXd, of_apply, ite_eq_right hab, Matrix.single_zero])
  have humem : ∀ a b, upperUnipotentSp n K (hu a b) ∈ H := by
    intro a b
    by_cases hab : a < b
    · by_cases h0 : X a b = 0
      · exact hone _ (by rw [hXu, of_apply, ite_eq_left hab, h0, Matrix.single_zero,
          Matrix.single_zero, add_zero])
      · obtain ⟨ha, -⟩ := hXs a b h0
        rw [upperUnipotentSp_congr (hu a b)
          (C' := single a b (X a b) + single b a (X a b))
          (by rw [transpose_add, transpose_single, transpose_single, add_comm])
          (by rw [hXu, of_apply, ite_eq_left hab])]
        by_cases hbp : b = spAPar a
        · subst hbp
          exact siegPair_spAPar_mem_commutator_of_two_le hjn hj2 ha (X a (spAPar a))
        · exact siegPair_mem_commutator_two hjn ha hbp (X a b)
    · exact hone _ (by rw [hXu, of_apply, ite_eq_right hab, Matrix.single_zero,
        Matrix.single_zero, add_zero])
  have hsd : ∑ a, ∑ b, single a b (Xd a b) = Xd := (matrix_eq_sum_single Xd).symm
  have hsu : ∑ a, ∑ b, (single a b (Xu a b) + single b a (Xu a b)) = Xu + Xuᵀ := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
      ← matrix_eq_sum_single Xu]
    congr 1
    conv_rhs => rw [matrix_eq_sum_single Xu]
    rw [transpose_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [transpose_sum]
    exact Finset.sum_congr rfl fun b _ => (transpose_single _ _ _).symm
  have hX3 : X = Xd + (Xu + Xuᵀ) := by
    ext a b
    rw [Matrix.add_apply, Matrix.add_apply, transpose_apply, hXd, hXu, of_apply, of_apply,
      of_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · rw [ite_eq_right h.ne, ite_eq_left h, ite_eq_right (not_lt.2 h.le), zero_add, add_zero]
    · rw [ite_eq_left rfl, ite_eq_right (lt_irrefl a), add_zero, add_zero]
    · rw [ite_eq_right h.ne', ite_eq_right (not_lt.2 h.le), ite_eq_left h, zero_add, zero_add]
      exact (congrFun (congrFun hX a) b).symm
  have hXd' : Xdᵀ = Xd := by
    rw [← hsd, transpose_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [transpose_sum]
    exact Finset.sum_congr rfl fun b _ => hd a b
  have hXu' : (Xu + Xuᵀ)ᵀ = Xu + Xuᵀ := by
    rw [transpose_add, transpose_transpose, add_comm]
  have hmd : upperUnipotentSp n K hXd' ∈ H := by
    have hin : ∀ a, (∑ b, single a b (Xd a b))ᵀ = ∑ b, single a b (Xd a b) := fun a => by
      rw [transpose_sum]
      exact Finset.sum_congr rfl fun b _ => hd a b
    rw [upperUnipotentSp_congr hXd' (by rw [hsd]; exact hXd') hsd.symm]
    exact upperUnipotentSp_sum_mem H _ _ hin (fun a _ =>
      upperUnipotentSp_sum_mem H _ _ (hd a) (fun b _ => hdmem a b) _) _
  have hmu : upperUnipotentSp n K hXu' ∈ H := by
    have hin : ∀ a, (∑ b, (single a b (Xu a b) + single b a (Xu a b)))ᵀ =
        ∑ b, (single a b (Xu a b) + single b a (Xu a b)) := fun a => by
      rw [transpose_sum]
      exact Finset.sum_congr rfl fun b _ => hu a b
    rw [upperUnipotentSp_congr hXu' (by rw [hsu]; exact hXu') hsu.symm]
    exact upperUnipotentSp_sum_mem H _ _ hin (fun a _ =>
      upperUnipotentSp_sum_mem H _ _ (hu a) (fun b _ => humem a b) _) _
  rw [upperUnipotentSp_congr hX (by rw [transpose_add, hXd', hXu']) hX3,
    ← upperUnipotentSp_mul hXd' hXu']
  exact H.mul_mem hmd hmu

end Radical

theorem spTwoLagPerfectInput_holds : SpTwoLagPerfectInput := by
  intro N j K _ _ _ hK hj3 hjN
  have hjn : 2 * j ≤ N := hjN.le
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  · refine (centralizer_spARep_le_sup hjn).trans (sup_le ?_ ?_)
    ·
      intro g hg
      obtain ⟨x, y, rfl⟩ := exists_spALeviOne_mul_spALeviTwo hjn hg
      have : Group.IsPerfect (StatedSp j K) :=
        CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp j K (Or.inr (Or.inr ⟨hK, hj3⟩))
      have hy : y = 1 := by
        have h0 : N - 2 * j = 0 := by omega
        have : IsEmpty (Fin (N - 2 * j)) := by rw [h0]; infer_instance
        apply mat_injective
        ext a b
        exact isEmptyElim a
      rw [hy, map_one, mul_one]
      exact spA_apply_mem_commutator_of_perfect _ (by
        rintro _ ⟨z, rfl⟩
        exact spALeviOne_mem_centralizer hjn z) x
    ·
      intro x hx
      obtain ⟨B, hB, X, hX, -, rfl⟩ := exists_spARadElt_of_mem hjn hx
      have hB0 : B = 0 := by
        ext a b
        rw [Matrix.zero_apply]
        by_contra hne
        have h1 := (hB a b hne).2
        have h2 := b.isLt
        omega
      have hU : spAOffUnit hB = 1 :=
        Units.ext (by rw [coe_spAOffUnit, hB0, add_zero, Units.val_one])
      rw [spARadElt, hU, map_one, one_mul]
      exact upperUnipotentSp_mem_commutator_two hjn (by omega) hX
        (fun a b _ => ⟨by have := a.isLt; omega, by have := b.isLt; omega⟩)

end CFSG.SeitzReduction.SymplecticPilot
