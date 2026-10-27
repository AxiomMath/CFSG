module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TNineCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.SectionRank.OddCover Matrix

variable {K : Type} [Field K]

theorem exists_orderOf_nine [Finite K] (h : 9 ∣ Nat.card K - 1) : ∃ ω : Kˣ, orderOf ω = 9 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  refine ⟨g ^ (orderOf g / 9), orderOf_pow_orderOf_div ?_ ?_⟩
  · rw [hgo]; exact Nat.card_pos.ne'
  · rw [hgo, hcard]; exact h

theorem pow_nine_eq_one {ω x : Kˣ} (hω : orderOf ω = 9) (hx : x ∈ Subgroup.zpowers ω) :
    x ^ 9 = 1 := by
  have := pow_card_eq_one' (G := Subgroup.zpowers ω) (x := ⟨x, hx⟩)
  rw [Nat.card_zpowers, hω] at this
  exact congrArg Subtype.val this

theorem nineData_SL [Finite K] (h : Nat.card K % 9 = 1) : NineData ↥(StatedSL 3 K) := by
  have h9 : 9 ∣ Nat.card K - 1 := by omega
  obtain ⟨ω, hω⟩ := exists_orderOf_nine h9
  refine nineData_of_mem hω ?_ ?_
  · intro a b _ _
    refine Subgroup.subset_closure ?_
    have ha := a.ne_zero
    have hb := b.ne_zero
    simp [coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_three]
    field_simp
  · refine Subgroup.subset_closure ?_
    simp [coe_tMat, Matrix.det_fin_three]

theorem neg_one_pow_eq [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2) : (-1 : K) ^ q = -1 := by
  rcases Nat.even_or_odd q with he | ho
  · have h2 : (2 : K) = 0 := by
      have : 2 ∣ Nat.card K := by rw [hq]; exact dvd_pow he.two_dvd two_ne_zero
      haveI hf : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := K) 2 ‹2 ∣ Nat.card K›
      have hx0 : x ≠ 0 := by
        intro h0; rw [h0, addOrderOf_zero] at hx; omega
      have := addOrderOf_nsmul_eq_zero x
      rw [hx, nsmul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_right hx0
    have h1 : (-1 : K) = 1 := by linear_combination (-1 : K) * h2
    rw [h1, one_pow]
  · exact ho.neg_one_pow

theorem nineData_SU [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2) (h : q % 9 = 8) :
    NineData ↥(StatedSU 3 q K) := by
  have hq0 : 0 < q := by omega
  have h9 : 9 ∣ Nat.card K - 1 := by
    have : q ^ 2 % 9 = 1 := by
      rw [pow_two, Nat.mul_mod, h]
    have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq0
    rw [hq]; omega
  obtain ⟨ω, hω⟩ := exists_orderOf_nine h9
  have hdiv : ∀ x : Kˣ, x ^ 9 = 1 → x ^ (q + 1) = 1 := by
    intro x hx
    obtain ⟨m, hm⟩ : 9 ∣ q + 1 := by omega
    rw [hm, pow_mul, hx, one_pow]
  have hdiag : ∀ (x y z : K), x ^ (q + 1) = 1 → y ^ (q + 1) = 1 → z ^ (q + 1) = 1 →
      ((Matrix.diagonal ![x, y, z]).map (· ^ q))ᵀ * Matrix.diagonal ![x, y, z] = 1 := by
    intro x y z hx hy hz
    rw [Matrix.diagonal_map (by simp [hq0.ne'])]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three, ← pow_succ, hx, hy, hz]
  refine nineData_of_mem hω ?_ ?_
  · intro a b ha hb
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · have ha' := a.ne_zero
      have hb' := b.ne_zero
      simp [coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_three]
      field_simp
    · rw [coe_diagHom]
      have hae := hdiv a (pow_nine_eq_one hω ha)
      have hbe := hdiv b (pow_nine_eq_one hω hb)
      have hce : ((a * b)⁻¹) ^ (q + 1) = 1 := by rw [inv_pow, mul_pow, hae, hbe]; simp
      have := hdiag (a : K) (b : K) (((a * b)⁻¹ : Kˣ) : K) (by simpa using congrArg (fun u : Kˣ => (u : K)) hae)
        (by simpa using congrArg (fun u : Kˣ => (u : K)) hbe)
        (by simpa using congrArg (fun u : Kˣ => (u : K)) hce)
      have hfun : (fun i => ((![a, b, (a * b)⁻¹] i : Kˣ) : K)) =
          ![(a : K), (b : K), (((a * b)⁻¹ : Kˣ) : K)] := by
        funext i
        fin_cases i <;> rfl
      rw [hfun]
      exact this
  · refine Subgroup.subset_closure ⟨?_, ?_⟩
    · simp [coe_tMat, Matrix.det_fin_three]
    · rw [coe_tMat]
      have hn := neg_one_pow_eq hq
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, hn, hq0.ne']

theorem tables112Types_T11_9_holds : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsThreeNine K →
      ∃ T P Q : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ P ≤ Subgroup.normalizer (T : Set K) ∧
        Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
        Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) := by
  intro K _ _ _ _ h
  have hN : NineData K := by
    rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, q, hq, hF, ⟨e⟩⟩
    · exact NineData.of_mulEquiv e (nineData_SL hF)
    · exact NineData.of_mulEquiv e (nineData_SU hq hF)
  obtain ⟨T, P, Q, h1, h2, h3, h4, h5, -⟩ := hN
  exact ⟨T, P, Q, h1, h2, h3, h4, h5⟩

end CFSG.HardMathSupport.Solomon.Coordinator
