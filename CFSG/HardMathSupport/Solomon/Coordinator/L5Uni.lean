module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Lin

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LocalTwo.Torus
  CFSG.HardMathSupport.Solomon.Proving

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

noncomputable abbrev uniProj (n : ℕ) : gramSU h (idGram K n) →* primeFormP h (idGram K n) :=
  QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)

theorem uniProj_ker_scalar {n : ℕ} (g : gramSU h (idGram K n)) (hg : uniProj h n g = 1) :
    ∃ c : Kˣ, (gramSU h (idGram K n)).subtype g = GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff g).1 hg
  exact ⟨c, hc⟩

theorem mem_range_gramSU {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ primeFormUnitary h (idGram K n))
    (hdet : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    g ∈ ((gramSU h (idGram K n)).subtype).range := by
  rw [Subgroup.range_subtype]
  exact (mem_gramSU_iff_unitary h).2 ⟨hg, hdet⟩

theorem commute_of_gramSU {n : ℕ} {s t : gramSU h (idGram K n)}
    (hc : Commute (s : GL (Fin n) K) (t : GL (Fin n) K)) : Commute s t :=
  Subtype.ext hc.eq

theorem hasCentTorus_primeFormP {n r : ℕ} [NeZero r] {Lb : Type*} [Group Lb] [Finite Lb]
    {Γ : Lb →* primeFormP h (idGram K n)} (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb))) {p : ℕ}
    [Fact p.Prime] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (hζb : h.bar (ζ : K) * (ζ : K) = 1)
    (c z : Fin n) (d : Fin r → Fin n) (hd : Function.Injective d) (hcd : ∀ k, c ≠ d k)
    (hzc : z ≠ c) (hzd : ∀ k, z ≠ d k) (t : gramSU h (idGram K n))
    (ht1 : ∀ a : Kˣ, (t : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) a)
    {e : ℕ} (ht2 : t ^ 2 ^ e = 1)
    (htX : ∀ k, Commute (t : GL (Fin n) K) (starX ζ c d k))
    (htS : ∀ k, Commute (t : GL (Fin n) K) (starSw c d k)) :
    HasCentTorus p r Lb := by
  have := h.finite
  obtain ⟨D, hcard, hX, hS⟩ := exists_torusData_star hζ (gramSU h (idGram K n)).subtype
    (Subgroup.subtype_injective _) (uniProj h n) (uniProj_ker_scalar h) c z d hd hcd hzc hzd
    (fun k => mem_range_gramSU h (tvec_mem_unitary h hζb _ _) (det_starX ζ hcd k))
    (fun k => mem_range_gramSU h (sgnSwap_mem_unitary h _ _) (det_starSw hcd k))
  refine hasCentTorus_of_torusData Fact.out hΓ hker hodd D hcard (T := uniProj h n t) ?_
    ⟨e, by rw [← map_pow, ht2, map_one]⟩ ?_ ?_
  · intro h1
    obtain ⟨a, ha⟩ := uniProj_ker_scalar h t h1
    exact ht1 a ha
  · intro k
    obtain ⟨x, hx, hxk⟩ := hX k
    rw [hxk]
    have h1 := htX k
    rw [← hx] at h1
    exact (commute_of_gramSU h h1).map (uniProj h n)
  · intro k
    obtain ⟨s, hs, hsk⟩ := hS k
    rw [hsk]
    have h1 := htS k
    rw [← hs] at h1
    exact (commute_of_gramSU h h1).map (uniProj h n)

theorem exists_primitiveRoot_five_norm (h5 : 5 ∣ ℓ ^ f + 1) :
    ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5 ∧ h.bar (ζ : K) * (ζ : K) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := h.finite
  have hcardK : Nat.card Kˣ = ℓ ^ (2 * f) - 1 := by rw [Nat.card_units, h.card]
  have hdvd : 5 ∣ Nat.card Kˣ := by
    have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have h2 : Nat.card Kˣ = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have e : ℓ ^ (2 * f) = ℓ ^ f * ℓ ^ f := by rw [two_mul, pow_add]
      have h3 : 1 ≤ ℓ ^ f * ℓ ^ f := Nat.mul_le_mul h1 h1
      rw [hcardK, e]
      zify [h1, h3]
      ring
    rw [h2]
    exact Dvd.dvd.mul_right h5 _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  have hζ : IsPrimitiveRoot z 5 := hz ▸ IsPrimitiveRoot.orderOf z
  have hzq : z ^ (ℓ ^ f + 1) = 1 := (hζ.pow_eq_one_iff_dvd _).2 h5
  refine ⟨z, hζ, ?_⟩
  have := congrArg (fun u : Kˣ => (u : K)) hzq
  simpa [Units.val_pow_eq_pow_val, h.bar_apply, pow_succ] using this

section Five

variable {Lb : Type*} [Group Lb] [Finite Lb] {Γ : Lb →* primeFormP h (idGram K 5)}

theorem hasCentTorus_two_primeFormP_five (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ ℓ ^ f + 1) : HasCentTorus 5 2 Lb := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ, hζb⟩ := exists_primitiveRoot_five_norm h h5
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1
    (mem_range_gramSU h (sgnSwap_mem_unitary h (0 : Fin 5) 1) (det_sgnSwap (K := K) h01))
  refine hasCentTorus_primeFormP h hΓ hker hodd hζ hζb 2 0 ![3, 4] (by decide) (by decide)
    (by decide) (by decide) t (fun a => by
      change (gramSU h (idGram K 5)).subtype t ≠ _
      rw [ht]
      exact ne_scalar_of_entry h01 (sgnSwap_apply_ne 0 1) a)
    (e := 2) ?_ ?_ ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change ((gramSU h (idGram K 5)).subtype t) ^ 2 ^ 2 = 1
    rw [ht]
    exact sgnSwap_pow_four 0 1
  · intro k
    change Commute ((gramSU h (idGram K 5)).subtype t) _
    rw [ht, starX]
    refine commute_sgnSwap_diag (tvec_comp_swap_disj ζ ?_ ?_ ?_ ?_) <;> fin_cases k <;> decide
  · intro k
    change Commute ((gramSU h (idGram K 5)).subtype t) _
    rw [ht, starSw]
    exact commute_sgnSwap_sgnSwap (by fin_cases k <;> decide)

theorem negFourVec_mem_unitary :
    (diagHom (negFourVec (F := K)) : GL (Fin 5) K) ∈ primeFormUnitary h (idGram K 5) := by
  refine diagHom_mem_unitary h _ fun i => ?_
  fin_cases i <;> simp [negFourVec, bar_fix_neg_one h]

theorem det_negFourVec :
    ((diagHom (negFourVec (F := K)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [diagHom_apply, det_diagGL]
  simp [negFourVec, Fin.prod_univ_five]

theorem negFourVec_sq : negFourVec (F := K) ^ 2 = 1 := by
  funext i
  fin_cases i <;> simp [negFourVec]

theorem hasCentTorus_three_primeFormP_five (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ ℓ ^ f + 1) (h2 : ringChar K ≠ 2) : HasCentTorus 5 3 Lb := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ, hζb⟩ := exists_primitiveRoot_five_norm h h5
  have hneg : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two h2
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1
    (mem_range_gramSU h (negFourVec_mem_unitary h) det_negFourVec)
  refine hasCentTorus_primeFormP h hΓ hker hodd hζ hζb 0 4 ![1, 2, 3] (by decide) (by decide)
    (by decide) (by decide) t ?_ (e := 1) ?_ ?_ ?_
  · intro a h1
    change (gramSU h (idGram K 5)).subtype t = _ at h1
    rw [ht] at h1
    have h0 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 0 0) h1
    have h4 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 4 4) h1
    simp [diagHom_apply, coe_diagGL, negFourVec, GeneralLinearGroup.coe_scalar] at h0 h4
    exact hneg (h0.trans h4.symm)
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change ((gramSU h (idGram K 5)).subtype t) ^ 2 ^ 1 = 1
    rw [ht, pow_one, ← map_pow, negFourVec_sq, map_one]
  · intro k
    change Commute ((gramSU h (idGram K 5)).subtype t) _
    rw [ht]
    exact (Commute.all _ _).map diagHom
  · intro k
    change Commute ((gramSU h (idGram K 5)).subtype t) _
    rw [ht, starSw]
    refine (commute_sgnSwap_diag (comp_swap_eq_of_eq ?_)).symm
    fin_cases k <;> simp [negFourVec]

end Five

end CFSG.HardMathSupport.Solomon.Coordinator
