module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthProj
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.SwapFrame

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type} [Field K] [CharP K 2] {d : ℕ}

theorem bigInv_of_swapframe [Finite K] (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q)
    (hgg : g * g = 1) (hZ : matrixDerivedScalars Q = ⊥)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (hσσ : ∀ x, g.val.right (g.val.right x) = x)
    (hTQ : ∀ v, Q (coordSemilinear g.val v) = g.val.right (Q v))
    {r : ℕ} (F : HFrame Q r)
    (hs : ∀ i, coordSemilinear g.val (F.e i) = F.f i ∧ coordSemilinear g.val (F.f i) = F.e i)
    {p : ℕ} (hp : p.Prime) (hp7 : 11 ≤ p ∨ p = 7) (M M' : Matrix (Fin r) (Fin r) K)
    (hN : (M'.map g.val.right)ᵀ = M') (hN' : (M.map g.val.right)ᵀ = M)
    (hMM' : M * M' = 1) (hMp : M ^ p = 1)
    (hns : ∀ c : K, M ≠ Matrix.scalar (Fin r) c) :
    BigInv (matrixProjectiveConjugationHom Q g) := by
  classical
  have hM'M : M' * M = 1 := mul_eq_one_comm.mp hMM'
  have hM'p : M' ^ p = 1 := by
    have hc : Commute M M' := by
      show M * M' = M' * M
      rw [hMM', hM'M]
    have := hc.mul_pow p
    rw [hMM', one_pow, hMp, one_mul] at this
    exact this.symm
  let tE := F.leviEquiv M M' hMM' hM'M
  let t : GL (Fin d) K := matrixLinearIso.symm tE
  have htE : matrixLinearIso t = tE := matrixLinearIso.apply_symm_apply tE
  have htiso : t ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    show Q (matrixLinearIso t v) = Q v
    rw [htE]
    exact F.Q_levi M M' hM'M v
  have htp : t ^ p = 1 := by
    apply matrixLinearIso.injective
    rw [map_pow, htE, map_one]
    refine LinearEquiv.ext fun v => ?_
    rw [Frame.leviEquiv_pow, hMp, hM'p, Frame.levi_one]
    rfl
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : tE = 1 := by rw [← htE, h, map_one]
    have h2 : ∀ v, F.levi M M' v = v := fun v => by
      have := congrArg (fun e : (Fin d → K) ≃ₗ[K] (Fin d → K) => e v) h1
      exact this
    exact hns 1 (by rw [map_one]; exact F.eq_one_of_levi_eq_id M M' h2)
  have hfp : Fact p.Prime := ⟨hp⟩
  have hot : orderOf t = p := orderOf_eq_prime htp ht1
  have hp2 : p ≠ 2 := by rcases hp7 with h | h <;> omega
  have htD : t ∈ matrixDerived Q := by
    let tO : matrixIsometries Q := ⟨t, htiso⟩
    have hpow : tO ^ p = 1 := Subtype.ext (by simpa using htp)
    have h1 : (Abelianization.of tO) ^ p = 1 := by rw [← map_pow, hpow, map_one]
    have hfin : Finite (Abelianization (matrixIsometries Q)) := inferInstance
    have h2 : orderOf (Abelianization.of tO) ∣ Nat.card (Abelianization (matrixIsometries Q)) :=
      orderOf_dvd_natCard _
    have h3 : orderOf (Abelianization.of tO) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have hpos : 0 < Nat.card (Abelianization (matrixIsometries Q)) := Nat.card_pos
    have h4 : orderOf (Abelianization.of tO) = 1 := by
      have hle : orderOf (Abelianization.of tO) ≤ 2 := (Nat.le_of_dvd hpos h2).trans hab
      have hpr := (Nat.dvd_prime hp).mp h3
      rcases hpr with h | h
      · exact h
      · omega
    have h5 : Abelianization.of tO = 1 := orderOf_eq_one_iff.mp h4
    have h6 : tO ∈ commutator (matrixIsometries Q) := (QuotientGroup.eq_one_iff tO).mp h5
    rw [matrixDerived_eq_map_commutator]
    exact ⟨tO, h6, rfl⟩
  have hTT : ∀ v, coordSemilinear g.val (coordSemilinear g.val v) = v := by
    intro v
    have h1 := coordinateSemilinearMap_mul g.val g.val v
    have h2 : g.val * g.val = 1 := congrArg Subtype.val hgg
    rw [h2, coordinateSemilinearMap_one] at h1
    exact h1.symm
  have hconj : matrixConjugation g.val t = t⁻¹ := by
    apply matrixLinearIso.injective
    refine LinearEquiv.ext fun v => ?_
    have h1 := matrixConjugation_vector g.val t v
    have hsymm : (coordinateSemilinearMap g.val).symm v = coordSemilinear g.val v :=
      (AddEquiv.symm_apply_eq _).mpr (hTT v).symm
    change matrixLinearEquiv (matrixConjugation g.val t) v = _ at *
    show matrixLinearEquiv (matrixConjugation g.val t) v = (matrixLinearIso t)⁻¹ v
    rw [h1, hsymm]
    have h2 : matrixLinearEquiv t = tE := htE
    rw [h2, htE]
    show coordSemilinear g.val (F.levi M M' (coordSemilinear g.val v)) = F.levi M' M v
    rw [HFrame.T_levi_swap hTQ F hs, hN, hN', hTT]
  set tD : matrixDerived Q := ⟨t, htD⟩ with htDdef
  set x := matrixProjectiveProjection Q tD with hx
  have hαx : matrixProjectiveConjugationHom Q g x = x⁻¹ := by
    show matrixProjectiveConjugation Q g (matrixProjectiveProjection Q tD) = _
    rw [matrixProjectiveConjugation_mk]
    have : matrixDerivedConjugation Q g tD = tD⁻¹ := by
      apply Subtype.ext
      rw [matrixDerivedConjugation_val]
      exact hconj
    rw [this, map_inv]
  have hxp : x ^ p = 1 := by
    rw [hx, ← map_pow]
    have : tD ^ p = 1 := Subtype.ext (by simpa [htDdef] using htp)
    rw [this, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : tD ∈ matrixDerivedScalars Q := (QuotientGroup.eq_one_iff tD).mp h
    rw [hZ, Subgroup.mem_bot] at h1
    exact ht1 (congrArg Subtype.val h1)
  have hox : orderOf x = p := orderOf_eq_prime hxp hx1
  refine ⟨x, p, hp, hp7, ?_⟩
  have hg2 : Nat.gcd p 2 = 1 :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
  rw [hαx, ← _root_.mul_inv_rev, ← pow_two, orderOf_inv, orderOf_pow, hox, hg2, Nat.div_one]

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
