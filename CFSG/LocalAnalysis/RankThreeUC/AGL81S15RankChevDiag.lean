module

public import CFSG.RankThree.SubgroupLists2.SpectralBounds

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevDiagProof

open Matrix CFSG.RankThree.SubgroupLists

variable {K : Type*} [Field K]

theorem exists_diagonal_of_elementary_gen {r m : ℕ} (hr : (r : K) ≠ 0)
    (E : Subgroup (GL (Fin m) K))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ r = 1)
    (hdet : ∀ a ∈ E, (a : Matrix (Fin m) (Fin m) K).det = 1) :
    ∃ P : Matrix (Fin m) (Fin m) (AlgebraicClosure K), IsUnit P ∧
      ∃ d : E → Fin m → AlgebraicClosure K,
        (∀ a : E, toAlgClosure (((a : GL (Fin m) K)) : Matrix (Fin m) (Fin m) K) * P =
          P * diagonal (d a)) ∧
        Function.Injective d ∧ (∀ a j, d a j ^ r = 1) ∧ ∀ a, ∏ j, d a j = 1 := by
  set f := algebraMap K (AlgebraicClosure K)
  set A : E → Matrix (Fin m) (Fin m) (AlgebraicClosure K) :=
    fun a => toAlgClosure (((a : GL (Fin m) K)) : Matrix (Fin m) (Fin m) K) with hA
  have hrL : (r : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast f]
    exact (map_ne_zero f).mpr hr
  have hAr : ∀ a, A a ^ r = 1 := fun a => by
    rw [hA, ← toAlgClosure_pow, ← Units.val_pow_eq_pow_val, hexp _ a.2, Units.val_one,
      toAlgClosure_one]
  have hAcomm : ∀ a b, A a * A b = A b * A a := fun a b => by
    rw [hA, ← toAlgClosure_mul, ← toAlgClosure_mul, ← Units.val_mul, ← Units.val_mul,
      hcomm _ a.2 _ b.2]
  obtain ⟨P, hP, d, hd⟩ := exists_simultaneous_diagonal A hAcomm (fun a => ⟨r, hrL, hAr a⟩)
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  refine ⟨P, hP, d, hd, ?_, fun a j => pow_eq_one_of_mul_eq_mul_diagonal hP (hd a) (hAr a) j,
    fun a => ?_⟩
  · intro a b hab
    have hAab : A a = A b := by
      calc A a = A a * P * P⁻¹ := by
            rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
        _ = A b * P * P⁻¹ := by rw [hd a, hd b, hab]
        _ = A b := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
    exact Subtype.ext (Units.ext (toAlgClosure_injective hAab))
  · have h := congrArg Matrix.det (hd a)
    rw [det_mul, det_mul, det_diagonal] at h
    have hdetA : (A a).det = 1 := by
      rw [hA, toAlgClosure_det, hdet _ a.2, map_one]
    rw [hdetA, one_mul] at h
    exact (mul_left_cancel₀ hPdet.ne_zero (h.symm.trans (mul_one _).symm) :)

theorem card_le_pow_pred_of_elementary [Finite K] {r m : ℕ} [Fact r.Prime] (hm : 1 ≤ m)
    (hr : (r : K) ≠ 0) (E : Subgroup (GL (Fin m) K))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ r = 1)
    (hdet : ∀ a ∈ E, (a : Matrix (Fin m) (Fin m) K).det = 1) :
    Nat.card E ≤ r ^ (m - 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨-, -, d, -, hinj, hpow, hprod⟩ := exists_diagonal_of_elementary_gen hr E hcomm hexp hdet
  set R := (Polynomial.nthRoots r (1 : AlgebraicClosure K)).toFinset with hRdef
  have hR : R.card ≤ r := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots r 1)
  have hmemR : ∀ a j, d a j ∈ R := fun a j => by
    rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Fact.out : r.Prime).pos]
    exact hpow a j
  let Ψ : E → (Fin k → R) := fun a j => ⟨d a (Fin.castSucc j), hmemR a _⟩
  have hΨ : Function.Injective Ψ := by
    intro a b hab
    apply hinj
    have hfst : ∀ j : Fin k, d a (Fin.castSucc j) = d b (Fin.castSucc j) := fun j =>
      congrArg Subtype.val (congrFun hab j)
    funext j
    refine Fin.lastCases ?_ (fun i => hfst i) j
    have ha := hprod a
    have hb := hprod b
    rw [Fin.prod_univ_castSucc] at ha hb
    simp only [hfst] at ha
    have hne : ∏ i : Fin k, d b (Fin.castSucc i) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hb
      exact zero_ne_one hb
    exact mul_left_cancel₀ hne (ha.trans hb.symm)
  calc Nat.card E ≤ Nat.card (Fin k → R) := Nat.card_le_card_of_injective Ψ hΨ
    _ = R.card ^ k := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
    _ ≤ r ^ k := Nat.pow_le_pow_left hR k
    _ = r ^ (k + 1 - 1) := by rw [Nat.add_sub_cancel]

end RankChevDiagProof

end CFSG.LocalAnalysis.RankThreeUC.S15
