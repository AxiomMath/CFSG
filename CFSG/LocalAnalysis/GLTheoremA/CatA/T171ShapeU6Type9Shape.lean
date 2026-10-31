module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Basic
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType.Line63.H5 CFSG.StandardType.TypeA.PGLTor CFSG.SectionRank.OddCover

theorem card_image_le_three_of_pow_three_eq_one {K : Type} [Field K] [DecidableEq K]
    {ι : Type} [Fintype ι]
    (f : ι → K) (hf : ∀ i, f i ^ 3 = 1) :
    (Finset.univ.image f).card ≤ 3 := by
  classical
  by_contra hle
  push_neg at hle
  set S : Finset K := Finset.univ.image f with hS
  have hroot : ∀ x ∈ S, Polynomial.eval x (Polynomial.X ^ 3 - Polynomial.C (1 : K)) = 0 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    simp [hf i]
  have hdeg : (Polynomial.X ^ 3 - Polynomial.C (1 : K)).natDegree = 3 :=
    Polynomial.natDegree_X_pow_sub_C
  have hp0 : Polynomial.X ^ 3 - Polynomial.C (1 : K) = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S hroot (by omega)
  rw [hp0] at hdeg
  norm_num at hdeg

abbrev fiber {ι M : Type*} [Fintype ι] [DecidableEq M] (f : ι → M) (v : M) : Finset ι :=
  Finset.univ.filter fun i => f i = v

theorem exists_two_le_fiber {ι M : Type*} [Fintype ι] [DecidableEq M] (f : ι → M)
    (hcard : Fintype.card ι = 6) (himage : (Finset.univ.image f).card ≤ 3) :
    ∃ v : M, 2 ≤ (fiber f v).card := by
  classical
  by_contra h
  push_neg at h
  have hsum : Finset.sum (Finset.univ.image f) (fun v => (fiber f v).card) = 6 := by
    rw [← hcard]
    exact (Finset.card_eq_sum_card_image f Finset.univ).symm
  have hle : Finset.sum (Finset.univ.image f) (fun v => (fiber f v).card) ≤ 3 := by
    calc Finset.sum (Finset.univ.image f) (fun v => (fiber f v).card)
        ≤ Finset.sum (Finset.univ.image f) (fun _ => 1) := by
          exact Finset.sum_le_sum fun v _ => by
            have hlt : (fiber f v).card < 2 := h v
            omega
      _ = (Finset.univ.image f).card := by simp
      _ ≤ 3 := himage
  omega

theorem exists_fiber_card_four_or_five {ι M : Type*} [Fintype ι] [DecidableEq M] (f : ι → M)
    (hcard : Fintype.card ι = 6) (himage : (Finset.univ.image f).card ≤ 3)
    (huniq : ∀ v w : M, v ≠ w → ¬ (2 ≤ (fiber f v).card ∧ 2 ≤ (fiber f w).card))
    (hnonconst : ∃ i j, f i ≠ f j) :
    ∃ v : M, (fiber f v).card = 4 ∨ (fiber f v).card = 5 := by
  classical
  obtain ⟨v, hv⟩ := exists_two_le_fiber f hcard himage
  have hsum : Finset.sum (Finset.univ.image f) (fun w => (fiber f w).card) = 6 := by
    rw [← hcard]
    exact (Finset.card_eq_sum_card_image f Finset.univ).symm
  have hmem : v ∈ Finset.univ.image f := by
    have hpos : 0 < (fiber f v).card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
  have hsplit := Finset.sum_erase_add (s := Finset.univ.image f)
    (f := fun w => (fiber f w).card) hmem
  have hrest : Finset.sum ((Finset.univ.image f).erase v) (fun w => (fiber f w).card) ≤ 2 := by
    calc Finset.sum ((Finset.univ.image f).erase v) (fun w => (fiber f w).card)
        ≤ Finset.sum ((Finset.univ.image f).erase v) (fun _ => 1) := by
          refine Finset.sum_le_sum fun w hw => ?_
          obtain ⟨hwv, -⟩ := Finset.mem_erase.mp hw
          have hnot := huniq v w (Ne.symm hwv)
          have hlt : (fiber f w).card < 2 := by
            by_contra hge
            exact hnot ⟨hv, Nat.le_of_not_gt hge⟩
          omega
      _ = ((Finset.univ.image f).erase v).card := by simp
      _ = (Finset.univ.image f).card - 1 := Finset.card_erase_of_mem hmem
      _ ≤ 2 := by
        have h1 : (Finset.univ.image f).card ≤ 3 := himage
        omega
  have hge : 4 ≤ (fiber f v).card := by
    have hEq : Finset.sum ((Finset.univ.image f).erase v)
        (fun w => (fiber f w).card) + (fiber f v).card = 6 := by
      rw [hsplit]
      exact hsum
    omega
  have hle6 : (fiber f v).card ≤ 6 := by
    calc (fiber f v).card ≤ (Finset.univ : Finset ι).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := hcard
  have hne6 : (fiber f v).card ≠ 6 := by
    intro h6
    have hfull : fiber f v = Finset.univ := by
      refine Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_
      rw [Finset.card_univ, hcard]
      omega
    obtain ⟨i, j, hij⟩ := hnonconst
    have hi : i ∈ fiber f v := by rw [hfull]; exact Finset.mem_univ i
    have hj : j ∈ fiber f v := by rw [hfull]; exact Finset.mem_univ j
    have hi' : f i = v := (Finset.mem_filter.mp hi).2
    have hj' : f j = v := (Finset.mem_filter.mp hj).2
    exact hij (by rw [hi', hj'])
  have h4 : 4 ≤ (fiber f v).card := hge
  have h5 : (fiber f v).card ≤ 5 := by
    have h6 : (fiber f v).card ≤ 6 := hle6
    have hn : (fiber f v).card ≠ 6 := hne6
    omega
  exact ⟨v, by omega⟩

theorem exists_fiber_card_four_or_five_of_four_le {ι M : Type*} [Fintype ι] [DecidableEq M]
    (f : ι → M) (hcard : Fintype.card ι = 6) {v : M} (hv : 4 ≤ (fiber f v).card)
    (hnonconst : ∃ i j, f i ≠ f j) :
    ∃ w : M, (fiber f w).card = 4 ∨ (fiber f w).card = 5 := by
  classical
  have hle6 : (fiber f v).card ≤ 6 := by
    calc (fiber f v).card ≤ (Finset.univ : Finset ι).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 6 := hcard
  have hne6 : (fiber f v).card ≠ 6 := by
    intro h6
    have hfull : fiber f v = Finset.univ := by
      refine Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_
      rw [Finset.card_univ, hcard]
      omega
    obtain ⟨i, j, hij⟩ := hnonconst
    have hi : i ∈ fiber f v := by rw [hfull]; exact Finset.mem_univ i
    have hj : j ∈ fiber f v := by rw [hfull]; exact Finset.mem_univ j
    have hi' : f i = v := (Finset.mem_filter.mp hi).2
    have hj' : f j = v := (Finset.mem_filter.mp hj).2
    exact hij (by rw [hi', hj'])
  refine ⟨v, ?_⟩
  omega


theorem exists_level_four_or_five_of_isComponent {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {M : GL (Fin 6) K}
    (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hM3 : M ^ 3 = 1) (hMscal : M ∉ LargeEvenScalars (Fin 6) K)
    (hcomp : CFSG.Assembly.IsComponentOf
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩))) :
    ∃ (P : GL (Fin 6) K) (_ : P ∈ primeFormUnitary h (idGram K 6)) (τ : Fin 6 → Kˣ),
      P⁻¹ * M * P = diagHom 6 τ ∧
        ∃ v : Kˣ, (fiber τ v).card = 4 ∨ (fiber τ v).card = 5 := by
  classical
  haveI : Finite K := h.finite
  have hn : 1 ≤ n := h.one_le
  have hMu : M ∈ primeFormUnitary h (idGram K 6) :=
    mem_primeFormUnitary_of_pow_three_eq_one h hpq hM hM3
  let G : Subgroup (primeFormUnitary h (idGram K 6)) := Subgroup.zpowers ⟨M, hMu⟩
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.refl (⟨M, hMu⟩ : primeFormUnitary h (idGram K 6))).zpow_zpow m k
  have hGexp : ∀ x ∈ G, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hM3' : (⟨M, hMu⟩ : primeFormUnitary h (idGram K 6)) ^ 3 = 1 := Subtype.ext hM3
    have h1 : ((⟨M, hMu⟩ : primeFormUnitary h (idGram K 6)) ^ k) ^ 3 =
        ((⟨M, hMu⟩ : primeFormUnitary h (idGram K 6)) ^ 3) ^ k := by
      calc ((⟨M, hMu⟩ : primeFormUnitary h (idGram K 6)) ^ k) ^ 3
          = (⟨M, hMu⟩ : primeFormUnitary h (idGram K 6)) ^ (k * (3 : ℤ)) := by
            rw [← zpow_natCast, ← zpow_mul]
            norm_num
        _ = (⟨M, hMu⟩ : primeFormUnitary h (idGram K 6)) ^ ((3 : ℤ) * k) := by
            rw [mul_comm]
        _ = ((⟨M, hMu⟩ : primeFormUnitary h (idGram K 6)) ^ 3) ^ k := by
            rw [zpow_mul]
            rfl
    rw [h1, hM3', one_zpow]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three hpq G hGcomm hGexp
  set Pg : GL (Fin 6) K := (P : GL (Fin 6) K) with hPg
  have hPdiag : (((Pg⁻¹ * M * Pg : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).IsDiag := by
    have := hP ⟨M, hMu⟩ (Subgroup.mem_zpowers _)
    simpa [hPg] using this
  obtain ⟨τ, hτ⟩ := TableBUE.exists_diagHom_of_isDiag hPdiag
  have hPN : Pg ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    SUTorus.mem_normalizer_of_mem_primeFormUnitary h P.2
  have hD : diagHom 6 τ ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
    rw [← hτ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
  have hτ3 : ∀ i : Fin 6, τ i ^ 3 = 1 := by
    have hcube : (diagHom 6 τ) ^ 3 = 1 := by
      rw [← hτ]
      have hconj : (Pg⁻¹ * M * Pg) ^ 3 = Pg⁻¹ * M ^ 3 * Pg := by
        simpa using (conj_pow (a := Pg⁻¹) (b := M) (i := 3))
      rw [hconj, hM3]
      simp
    intro i
    have hpow : (diagHom 6 τ) ^ 3 = diagHom 6 (τ ^ 3) := by
      rw [← map_pow]
    have hcube' : diagHom 6 (τ ^ 3) = 1 := by
      rw [← hpow]
      exact hcube
    have := congrArg (fun X : GL (Fin 6) K => ((X : Matrix (Fin 6) (Fin 6) K) i i)) hcube'
    have hval : (τ i : K) ^ 3 = 1 := by
      simpa [coe_diagHom, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply,
        Units.val_pow_eq_pow_val] using this
    exact Units.ext hval
  have hnonconst : ∃ i j : Fin 6, τ i ≠ τ j := by
    by_contra hcon
    push_neg at hcon
    apply hMscal
    have hconst : τ = fun _ => τ 0 := funext fun i => hcon i 0
    have hdiagconst : diagHom 6 τ = diagHom 6 (fun _ => τ 0) := by rw [hconst]
    have hscaldiag : diagHom 6 (fun _ => τ 0) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (τ 0) := by
      ext i j
      simp [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hMsc : M = Matrix.GeneralLinearGroup.scalar (Fin 6) (τ 0) := by
      calc M = Pg * (diagHom 6 τ) * Pg⁻¹ := by
            rw [← hτ]
            group
        _ = Pg * (Matrix.GeneralLinearGroup.scalar (Fin 6) (τ 0)) * Pg⁻¹ := by
            rw [hdiagconst, hscaldiag]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) (τ 0) := by
            calc Pg * (Matrix.GeneralLinearGroup.scalar (Fin 6) (τ 0)) * Pg⁻¹
                = (Matrix.GeneralLinearGroup.scalar (Fin 6) (τ 0)) * Pg * Pg⁻¹ := by
                  rw [(TypeA.PGLTor.commute_scalar (τ 0) Pg).eq]
              _ = Matrix.GeneralLinearGroup.scalar (Fin 6) (τ 0) := by group
    exact ⟨τ 0, hMsc.symm⟩
  have himage : (Finset.univ.image τ).card ≤ 3 := by
    have hK : (Finset.univ.image (fun i : Fin 6 => (τ i : K))).card ≤ 3 := by
      refine card_image_le_three_of_pow_three_eq_one (fun i : Fin 6 => (τ i : K)) fun i => ?_
      have := hτ3 i
      simpa using congrArg (fun u : Kˣ => (u : K)) this
    have hcard : (Finset.univ.image (fun i : Fin 6 => (τ i : K))).card =
        (Finset.univ.image τ).card := by
      have h1 : ((Finset.univ.image τ).image (fun u : Kˣ => (u : K))).card =
          (Finset.univ.image τ).card :=
        Finset.card_image_of_injective _ Units.val_injective
      have h2 : ((Finset.univ.image τ).image (fun u : Kˣ => (u : K))) =
          Finset.univ.image (fun i : Fin 6 => (τ i : K)) := by
        rw [Finset.image_image]
        rfl
      rw [h2] at h1
      exact h1
    rwa [hcard] at hK
  have hcard6 : Fintype.card (Fin 6) = 6 := by simp
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  ·
    have hn1' : n = 1 := le_antisymm (by omega) hn
    subst hn1'
    have hbig : ∃ i : Fin 6, 4 ≤ (fiber τ (τ i)).card := by
      by_contra hno
      have hsmall : ∀ (i : Fin 6) (S : Finset (Fin 6)),
          (∀ j : Fin 6, j ∈ S ↔ τ j = τ i) → S.card ≤ 3 := by
        intro i S hS
        have heq : S = fiber τ (τ i) := by
          ext j
          rw [hS j]
          simp [fiber]
        rw [heq]
        by_contra hge
        exact hno ⟨i, by omega⟩
      have hnotD := not_isComponentOf_layer_ggFix_diag_two h hD hsmall
      have hnotM := not_isComponentOf_layer_ggFix_of_conj h hMN P.2 hτ hD hnotD
      exact hnotM hcomp
    obtain ⟨i, hi⟩ := hbig
    obtain ⟨v, hv⟩ := exists_fiber_card_four_or_five_of_four_le τ hcard6 hi hnonconst
    exact ⟨Pg, P.2, τ, hτ, v, hv⟩
  ·
    have huniq : ∀ v w : Kˣ, v ≠ w →
        ¬ (2 ≤ (fiber τ v).card ∧ 2 ≤ (fiber τ w).card) := by
      rintro v w hvw ⟨hv, hw⟩
      have hv' : 2 ≤ (Finset.univ.filter (fun i : Fin 6 => τ i = v)).card := by
        simpa [fiber] using hv
      have hw' : 2 ≤ (Finset.univ.filter (fun i : Fin 6 => τ i = w)).card := by
        simpa [fiber] using hw
      have hS₁ : ∀ i : Fin 6, i ∈ (Finset.univ.filter (fun i : Fin 6 => τ i = v)) ↔ τ i = v :=
        fun i => by simp
      have hS₂ : ∀ i : Fin 6, i ∈ (Finset.univ.filter (fun i : Fin 6 => τ i = w)) ↔ τ i = w :=
        fun i => by simp
      have hnotD := not_isComponentOf_layer_ggFix_diag h hn2 hD rfl hvw
        (S₁ := Finset.univ.filter (fun i : Fin 6 => τ i = v))
        (S₂ := Finset.univ.filter (fun i : Fin 6 => τ i = w))
        hS₁ hS₂ hv' hw'
      have hnotM := not_isComponentOf_layer_ggFix_of_conj h hMN P.2 hτ hD hnotD
      exact hnotM hcomp
    obtain ⟨v, hv⟩ := exists_fiber_card_four_or_five τ hcard6 himage huniq hnonconst
    exact ⟨Pg, P.2, τ, hτ, v, hv⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
