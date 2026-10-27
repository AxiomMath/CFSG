module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsComp
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLDiag
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Generic
open CFSG.Open (IsSubnormal)
open CFSG.ClassicalInvolution.ModelFacts (negBlockK negBlockK_eq_diagonal
  range_blockSL_eq_longRootGroupK exists_sl_conj_diagonal open_isQuasisimple_sl
  subsingleton_sl_of_le_one two_ne_zero_galoisField)
open scoped MatrixGroups

section Diagonal

variable {F : Type} [Field F] {n : ℕ}

theorem eq_diagonal_of_commute_single (h2 : (2 : F) ≠ 0) (e : Fin n → F)
    (he : ∀ p, e p = 1 ∨ e p = -1) {ν : Matrix (Fin n) (Fin n) F}
    (hD : ν * Matrix.diagonal e = Matrix.diagonal e * ν)
    (hs : ∀ i j, i ≠ j → e i = e j → Commute (Matrix.single i j (1 : F)) ν) :
    ν = Matrix.diagonal (fun p => ν p p) := by
  have hoff : ∀ p q, p ≠ q → ν p q = 0 := by
    intro p q hpq
    by_cases hep : e p = e q
    · exact row_eq_zero_of_commute_single (hs q p hpq.symm hep.symm) hpq.symm
    · have h := congrFun (congrFun hD p) q
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      rcases he p with hp | hp <;> rcases he q with hq | hq
      · exact absurd (hp.trans hq.symm) hep
      · rw [hp, hq] at h
        have h3 : (2 : F) * ν p q = 0 := by linear_combination -h
        exact (mul_eq_zero.mp h3).resolve_left h2
      · rw [hp, hq] at h
        have h3 : (2 : F) * ν p q = 0 := by linear_combination h
        exact (mul_eq_zero.mp h3).resolve_left h2
      · exact absurd (hp.trans hq.symm) hep
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp
  · rw [Matrix.diagonal_apply_ne _ hpq, hoff p q hpq]

end Diagonal

section Std

variable {F : Type} [Field F] [Finite F]

theorem sl_commute_of_isSubnormal_std (h4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) {n a : ℕ}
    (ha : a ≤ n) {g : SL(n, F)} (hg : (g : Matrix (Fin n) (Fin n) F) = negBlockK F n 0 a)
    {N : Subgroup SL(n, F)} (hNs : IsSubnormal N (Subgroup.centralizer ({g} : Set SL(n, F))))
    (hsolv : Group.IsSolvable N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  set D : Matrix (Fin n) (Fin n) F := negBlockK F n 0 a with hD
  have hDc : negBlockK F n a (n - a) = -D := negBlockK_compl ha
  have hcomm : ∀ x : SL(n, F), x ∈ Subgroup.centralizer ({g} : Set SL(n, F)) ↔
      (x : Matrix (Fin n) (Fin n) F) * D = D * x := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg (fun y : SL(n, F) => (y : Matrix (Fin n) (Fin n) F)) h
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
    · intro h
      ext i j
      have h' := congrFun (congrFun h i) j
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
  have hneg : ∀ x : SL(n, F), (x : Matrix (Fin n) (Fin n) F) * (-D) = (-D) * x ↔
      (x : Matrix (Fin n) (Fin n) F) * D = D * x := by
    intro x
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  have hNC : N ≤ Subgroup.centralizer ({g} : Set SL(n, F)) :=
    CFSG.ClassicalInvolution.isSubnormal_le hNs
  have key : ∀ (A : Subgroup SL(n, F)) (k : ℕ) (e : SL(k, F) ≃* A),
      A ≤ Subgroup.centralizer ({g} : Set SL(n, F)) →
      (∀ c ∈ Subgroup.centralizer ({g} : Set SL(n, F)), ∀ x ∈ A, c * x * c⁻¹ ∈ A) →
      ∀ x ∈ N, ∀ a ∈ A, x * a = a * x := by
    intro A k e hAC hAn x hx a ha
    by_cases hk : 2 ≤ k
    · have hq : CFSG.Open.IsQuasisimple ↥A :=
        CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
          (open_isQuasisimple_sl (F := F) hk h4)
      exact commute_of_isSubnormal_of_isSolvable hq hAC (le_normalizer_of_forall_conj_mem hAn)
        hNs hsolv x hx a ha
    · have : Subsingleton SL(k, F) := subsingleton_sl_of_le_one (by omega)
      obtain ⟨u, hu⟩ := e.surjective ⟨a, ha⟩
      have hu1 : u = 1 := Subsingleton.elim _ _
      rw [hu1, map_one] at hu
      have ha1 : a = 1 := (congrArg Subtype.val hu).symm
      rw [ha1, mul_one, one_mul]
  have h₁ : 0 + a ≤ n := by omega
  have h₂ : a + (n - a) ≤ n := by omega
  let e₁ : SL(a, F) ≃* longRootGroup (negBlockK F n 0 a) :=
    (MonoidHom.ofInjective (blockSL_injective h₁)).trans
      (MulEquiv.subgroupCongr (range_blockSL_eq_longRootGroupK h2 h₁))
  let e₂ : SL(n - a, F) ≃* longRootGroup (negBlockK F n a (n - a)) :=
    (MonoidHom.ofInjective (blockSL_injective h₂)).trans
      (MulEquiv.subgroupCongr (range_blockSL_eq_longRootGroupK h2 h₂))
  have hL := key (longRootGroup (negBlockK F n 0 a)) a e₁
    (fun x hx => (hcomm x).mpr hx.1)
    (fun c hc x hx => conj_mem_longRootGroup_of_commute ((hcomm c).mp hc) hx)
  have hC := key (longRootGroup (negBlockK F n a (n - a))) (n - a) e₂
    (fun x hx => (hcomm x).mpr ((hneg x).mp (by rw [← hDc]; exact hx.1)))
    (fun c hc x hx => by
      rw [hDc] at hx ⊢
      exact conj_mem_longRootGroup_of_commute ((hneg c).mpr ((hcomm c).mp hc)) hx)
  set e : Fin n → F := fun p => if a ≤ p.val then 1 else -1 with he_def
  have hDe : D = Matrix.diagonal e := by
    rw [hD, negBlockK_eq_diagonal]
    congr 1
    funext p
    by_cases h : p.val < a
    · simp [e, h, not_le.mpr h]
    · simp [e, h, not_lt.mp h]
  have hnegDe : -D = Matrix.diagonal (fun p => -e p) := by rw [hDe, Matrix.diagonal_neg]
  have he : ∀ p, e p = 1 ∨ e p = -1 := fun p => by
    by_cases h : a ≤ p.val
    · exact Or.inl (by simp [e, h])
    · exact Or.inr (by simp [e, h])
  have hdiag : ∀ ν ∈ N, (ν : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun p => (ν : Matrix (Fin n) (Fin n) F) p p) := by
    intro ν hν
    refine eq_diagonal_of_commute_single h2 e he ?_ ?_
    · rw [← hDe]
      exact (hcomm ν).mp (hNC hν)
    · intro i j hij hee
      rcases he i with h1 | h1
      · have hj1 : e j = 1 := hee ▸ h1
        have hx : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
            longRootGroup (negBlockK F n a (n - a)) := by
          rw [hDc, hnegDe]
          exact transvection_mem_longRootGroup_diagonal _ hij (by simp [hee]) (by simp [hj1])
        exact commute_single_of_mul_transvection hij (hC ν hν _ hx)
      · have hj1 : e j = -1 := hee ▸ h1
        have hx : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
            longRootGroup (negBlockK F n 0 a) := by
          rw [← hD, hDe]
          exact transvection_mem_longRootGroup_diagonal e hij hee (by simp [hj1])
        exact commute_single_of_mul_transvection hij (hL ν hν _ hx)
  intro x hx y hy
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hdiag x hx,
    hdiag y hy, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  exact mul_comm _ _

end Std

section General

variable {F : Type} [Field F] [Finite F]

theorem sl_commute_of_isSubnormal (h4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) {n : ℕ}
    {w : SL(n, F)} (hw : w * w = 1) {N : Subgroup SL(n, F)}
    (hNs : IsSubnormal N (Subgroup.centralizer ({w} : Set SL(n, F))))
    (hsolv : Group.IsSolvable N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton SL(0, F) := subsingleton_sl_of_le_one (by omega)
    intro x _ y _
    exact Subsingleton.elim _ _
  have hD : (w : Matrix (Fin n) (Fin n) F) * w = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hw, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨a, ha, P, hP⟩ := exists_sl_conj_diagonal h2 hn hD
  have hPP : ((P⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) * P = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  set g : SL(n, F) := P⁻¹ * w * P with hgdef
  have hg : (g : Matrix (Fin n) (Fin n) F) = negBlockK F n 0 a := by
    rw [hgdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_assoc, hP, ← Matrix.mul_assoc, hPP, Matrix.one_mul, negBlockK_eq_diagonal]
    congr 1
    funext j
    simp
  have hconj : (MulAut.conj P⁻¹) w = g := by
    rw [MulAut.conj_apply, inv_inv]
  have hinj : Function.Injective (MulAut.conj P⁻¹).toMonoidHom := (MulAut.conj P⁻¹).injective
  have hNs' : IsSubnormal (N.map (MulAut.conj P⁻¹).toMonoidHom)
      (Subgroup.centralizer ({g} : Set SL(n, F))) := by
    have h1 := CFSG.ClassicalInvolution.isSubnormal_map_conj hNs P⁻¹
    rwa [map_centralizer_singleton_mulEquiv₃ (MulAut.conj P⁻¹) w, hconj] at h1
  have hsolv' : Group.IsSolvable ↥(N.map (MulAut.conj P⁻¹).toMonoidHom) :=
    Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective N _ hinj).toMonoidHom)
      (Subgroup.equivMapOfInjective N _ hinj).surjective
  have key := sl_commute_of_isSubnormal_std h4 h2 ha hg hNs' hsolv'
  intro x hx y hy
  apply (MulAut.conj P⁻¹).injective
  rw [map_mul, map_mul]
  exact key _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)

end General

theorem classicalMemberParameters3At_PSL : ClassicalMemberParameters3At .PSL := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  have he : 1 ≤ e := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h5 : 5 ≤ r ^ e := five_le_pow_of_odd_prime_of_ne_three hr hr2 he hne
  have h4 : 4 ≤ Nat.card (GaloisField r e) := by
    rw [GaloisField.card r e (by omega)]
    omega
  have h2 : (2 : GaloisField r e) ≠ 0 := two_ne_zero_galoisField e hr2
  have : Finite (modelUniv .PSL (m + 1) r e hr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr trivial hadm
  refine false_of_isClassicalMember3_of_oddGenerated ψ hψ hker ?_ h
  intro w hw N _ hNs hsolv _
  exact derivedSeries_two_eq_bot_of_commute (sl_commute_of_isSubnormal h4 h2 hw hNs hsolv)

end CFSG.ClassicalInvolution.Q3
