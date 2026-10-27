module

public import CFSG.LieType.Ree.FaithfulTriangular

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


section Lin

variable {K : Type*} [Field K] {ι : Type*}

theorem coeff_eq (T Tinv : Module.End K (ι →₀ K)) (P Q : ℕ → Module.End K (ι →₀ K))
    (σ : K → K)
    (h : ∀ c : K, T * (∑ k ∈ Finset.range 4, σ c ^ k • P k) * Tinv =
      ∑ k ∈ Finset.range 4, c ^ k • Q k) (w : ι →₀ K) (l : ι) (c : K) :
    ((T * P 0 * Tinv) w) l + σ c * ((T * P 1 * Tinv) w) l + σ c ^ 2 * ((T * P 2 * Tinv) w) l +
        σ c ^ 3 * ((T * P 3 * Tinv) w) l =
      (Q 0 w) l + c * (Q 1 w) l + c ^ 2 * (Q 2 w) l + c ^ 3 * (Q 3 w) l := by
  have e := congrArg (fun M : Module.End K (ι →₀ K) => (M w) l) (h c)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, LinearMap.add_apply, LinearMap.smul_apply,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, pow_zero, pow_one, one_smul] at e
  linear_combination e

variable [CharP K 3]

theorem second_diff (a b : ℕ → K) (σ : K →+* K)
    (E : ∀ c : K, a 0 + σ c * a 1 + σ c ^ 2 * a 2 + σ c ^ 3 * a 3 =
      b 0 + c * b 1 + c ^ 2 * b 2 + c ^ 3 * b 3) (c d : K) :
    σ c * σ d * a 2 = c * d * b 2 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h2 : (2 : K) ≠ 0 := fun h2 => one_ne_zero (by linear_combination h3 - h2 : (1 : K) = 0)
  have e1 := E (c + d)
  have e2 := E c
  have e3 := E d
  have e0 := E 0
  rw [map_add] at e1
  rw [map_zero] at e0
  have key : 2 * (σ c * σ d * a 2 - c * d * b 2) = 0 := by
    linear_combination e1 - e2 - e3 + e0 - (σ c ^ 2 * σ d + σ c * σ d ^ 2) * a 3 * h3 +
      (c ^ 2 * d + c * d ^ 2) * b 3 * h3
  linear_combination (mul_eq_zero.mp key).resolve_left h2

theorem sigma_eq_self (a b : ℕ → K) (σ : K →+* K)
    (E : ∀ c : K, a 0 + σ c * a 1 + σ c ^ 2 * a 2 + σ c ^ 3 * a 3 =
      b 0 + c * b 1 + c ^ 2 * b 2 + c ^ 3 * b 3) (hb : b 2 ≠ 0) (c : K) : σ c = c := by
  have h11 := second_diff a b σ E 1 1
  rw [map_one, one_mul, one_mul, one_mul] at h11
  have hc1 := second_diff a b σ E c 1
  rw [map_one, mul_one, mul_one, h11] at hc1
  exact mul_right_cancel₀ hb hc1

theorem cubic_eq (a b : ℕ → K)
    (E : ∀ c : K, a 0 + c * a 1 + c ^ 2 * a 2 + c ^ 3 * a 3 =
      b 0 + c * b 1 + c ^ 2 * b 2 + c ^ 3 * b 3) {c₀ : K} (hc₀ : c₀ ^ 3 ≠ c₀) : a 3 = b 3 := by
  have h22 := second_diff a b (RingHom.id K) E 1 1
  simp only [RingHom.id_apply, one_mul] at h22
  have e0 := E 0
  have e1 := E 1
  have ec := E c₀
  have key : (c₀ ^ 3 - c₀) * (a 3 - b 3) = 0 := by
    linear_combination ec - c₀ * e1 - (1 - c₀) * e0 - (c₀ ^ 2 - c₀) * h22
  linear_combination (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr hc₀)

end Lin

theorem exists_cube_ne {K : Type*} [Field K] [Finite K] (hK : 3 < Nat.card K) :
    ∃ c₀ : K, c₀ ^ 3 ≠ c₀ := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype K := Fintype.ofFinite K
  have hp0 : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K (by norm_num)
  have hsub : (Finset.univ : Finset K) ⊆
      (Polynomial.X ^ 3 - Polynomial.X : Polynomial K).roots.toFinset := by
    intro c _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def]
    simp [hcon c]
  have h1 := (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num : 1 < 3)).le))
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

@[expose] def longIdx : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def shortIdx : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem fin_g2_cases (i : Fin Tag.G2.rank) : i = longIdx ∨ i = shortIdx := by
  rcases i with ⟨_ | _ | n, h⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    have h2 : Tag.G2.rank = 2 := rfl
    omega

theorem longIdx_ne_shortIdx : longIdx ≠ shortIdx := by decide


theorem isRoot_g2_iff {v : Fin Tag.G2.rank → ℤ} :
    IsRoot .G2 v ↔ ∃ k < Tag.G2.rootCertificate.roots.length, Tag.G2.rootCertificate.root k = v :=
  RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)

theorem not_isRoot_add_three_long {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ¬IsRoot .G2 (α + ((3 : ℕ) : ℤ) • Pi.single longIdx 1) := by
  rw [isRoot_g2_iff] at hα ⊢
  obtain ⟨k, hk, rfl⟩ := hα
  rintro ⟨k', hk', he⟩
  have key : ∀ k < Tag.G2.rootCertificate.roots.length,
      ∀ k' < Tag.G2.rootCertificate.roots.length, Tag.G2.rootCertificate.root k' ≠
        Tag.G2.rootCertificate.root k + ((3 : ℕ) : ℤ) • Pi.single longIdx 1 := by
    decide +kernel
  exact key k hk k' hk' he

theorem isRoot_long_add_three_short :
    IsRoot .G2 (Pi.single longIdx 1 + ((3 : ℕ) : ℤ) • Pi.single shortIdx 1) := by
  rw [isRoot_g2_iff]
  exact ⟨3, by decide +kernel, by decide +kernel⟩

theorem not_isRoot_long_sub_short : ¬IsRoot .G2 (Pi.single longIdx 1 - Pi.single shortIdx 1) := by
  rw [isRoot_g2_iff]
  rintro ⟨k, hk, he⟩
  have key : ∀ k < Tag.G2.rootCertificate.roots.length,
      Tag.G2.rootCertificate.root k ≠ Pi.single longIdx 1 - Pi.single shortIdx 1 := by
    decide +kernel
  exact key k hk he

section Coeff

variable {R : Type*} [CommRing R]

theorem rootVec_eq_single {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    rootVec .G2 R α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 := by
  unfold rootVec
  exact dite_eq_left hα


theorem xCoeff_long_three : xCoeff .G2 R longIdx 3 = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rcases b with j | ⟨α, hα⟩
  · exact (xCoeff_hVec longIdx j 3).trans (by simp)
  · rw [← rootVec_eq_single hα]
    by_cases h₁ : α = Pi.single longIdx 1
    · subst h₁
      rw [xCoeff_rootVec_single]
      simp
    by_cases h₂ : α = -Pi.single longIdx 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single]
      simp
    have h0 : rootVec .G2 R (α + ((3 : ℕ) : ℤ) • Pi.single longIdx 1) = 0 := by
      unfold rootVec
      exact dite_eq_right (not_isRoot_add_three_long hα)
    rw [xCoeff_rootVec_of_ne longIdx 3 hα h₁ h₂, h0, smul_zero]

theorem xCoeff_short_three_ne [Nontrivial R] : xCoeff .G2 R shortIdx 3 ≠ 0 := by
  intro h
  have hα : IsRoot .G2 (Pi.single longIdx 1) := isRoot_single .G2 longIdx
  have h₁ : (Pi.single longIdx 1 : Fin Tag.G2.rank → ℤ) ≠ Pi.single shortIdx 1 := by
    decide +kernel
  have h₂ : (Pi.single longIdx 1 : Fin Tag.G2.rank → ℤ) ≠ -Pi.single shortIdx 1 := by
    decide +kernel
  have hq : stringDown .G2 shortIdx (Pi.single longIdx 1) = 0 :=
    stringDown_eq_zero hα h₁ h₂ not_isRoot_long_sub_short
  have e := congrArg (fun M : Module.End R (RootModule .G2 R) =>
    (M (rootVec .G2 R (Pi.single longIdx 1))) (Sum.inr ⟨_, isRoot_long_add_three_short⟩)) h
  simp only [LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at e
  rw [xCoeff_rootVec_of_ne shortIdx 3 hα h₁ h₂, hq, rootVec_eq_single isRoot_long_add_three_short]
    at e
  simp at e

theorem xCoeff_two_apply (i : Fin Tag.G2.rank) :
    (xCoeff .G2 R i 2 (rootVec .G2 R (-Pi.single i 1))) (Sum.inr ⟨_, isRoot_single .G2 i⟩) = 1 := by
  rw [xCoeff_rootVec_neg_single, rootVec_eq_single (isRoot_single .G2 i)]
  simp

end Coeff

theorem conj_xOp_g2 {K : Type*} [Field K] [CharP K 3] [Finite K] (hK : 3 < Nat.card K)
    (T Tinv : Module.End K (RootModule .G2 K)) (hTT : Tinv * T = 1) (σ : K →+* K)
    (i i' : Fin Tag.G2.rank) (h : ∀ c : K, T * xOp .G2 K i' (σ c) * Tinv = xOp .G2 K i c) :
    (∀ c, σ c = c) ∧ i' = i := by
  have h' : ∀ c : K, T * (∑ k ∈ Finset.range 4, σ c ^ k • xCoeff .G2 K i' k) * Tinv =
      ∑ k ∈ Finset.range 4, c ^ k • xCoeff .G2 K i k := by
    intro c
    rw [← xOp_eq_sum_xCoeff, ← xOp_eq_sum_xCoeff]
    exact h c
  have hσ : ∀ c, σ c = c := by
    set w := rootVec .G2 K (-Pi.single i 1)
    set l : Label .G2 := Sum.inr ⟨_, isRoot_single .G2 i⟩
    exact sigma_eq_self (fun k => ((T * xCoeff .G2 K i' k * Tinv) w) l)
      (fun k => (xCoeff .G2 K i k w) l) σ (coeff_eq T Tinv _ _ σ h' w l)
      (by simp only [w, l, xCoeff_two_apply]; exact one_ne_zero)
  refine ⟨hσ, ?_⟩
  obtain ⟨c₀, hc₀⟩ := exists_cube_ne hK
  have h'' : ∀ c : K, T * (∑ k ∈ Finset.range 4, (fun c : K => c) c ^ k • xCoeff .G2 K i' k) *
      Tinv = ∑ k ∈ Finset.range 4, c ^ k • xCoeff .G2 K i k := fun c => by
    have := h' c
    rwa [hσ] at this
  have h3 : T * xCoeff .G2 K i' 3 * Tinv = xCoeff .G2 K i 3 :=
    LinearMap.ext fun w => Finsupp.ext fun l =>
      cubic_eq (fun k => ((T * xCoeff .G2 K i' k * Tinv) w) l) (fun k => (xCoeff .G2 K i k w) l)
        (coeff_eq T Tinv _ _ (fun c : K => c) h'' w l) hc₀
  by_contra hne
  rcases fin_g2_cases i with rfl | rfl <;> rcases fin_g2_cases i' with rfl | rfl
  · exact hne rfl
  · rw [xCoeff_long_three] at h3
    refine xCoeff_short_three_ne (R := K) ?_
    calc xCoeff .G2 K shortIdx 3 = Tinv * T * xCoeff .G2 K shortIdx 3 * (Tinv * T) := by
          rw [hTT, one_mul, mul_one]
      _ = Tinv * (T * xCoeff .G2 K shortIdx 3 * Tinv) * T := by simp only [mul_assoc]
      _ = 0 := by rw [h3, mul_zero, zero_mul]
  · rw [xCoeff_long_three, mul_zero, zero_mul] at h3
    exact xCoeff_short_three_ne (R := K) h3.symm
  · exact hne rfl

end CFSG.ClassicalInvolution.NDB.NDBG3
