module

public import CFSG.LieType.SeitzGeneration.HeisTorusU82

public section

open scoped MatrixGroups

open CFSG.BenderSuzuki.MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.SeitzGeneration

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

section Arithmetic

theorem false_of_cube_le_sq {x Q N : ℕ} (hQ : 64 ≤ Q) (hx : x ^ 3 ≤ Q ^ 2) (hNx : N ≤ x + 1)
    (hN3 : Q + 1 ≤ 3 * N) : False := by
  have h1 : Q ≤ 3 * x + 2 := by omega
  have h2 : 21 ≤ x := by omega
  have h3 : Q ^ 2 ≤ (3 * x + 2) ^ 2 := Nat.pow_le_pow_left h1 2
  have h4 : 21 * x ^ 2 ≤ x ^ 3 :=
    calc 21 * x ^ 2 ≤ x * x ^ 2 := Nat.mul_le_mul_right _ h2
      _ = x ^ 3 := by ring
  have h5 : 21 * x ≤ x ^ 2 :=
    calc 21 * x ≤ x * x := Nat.mul_le_mul_right _ h2
      _ = x ^ 2 := by ring
  nlinarith

theorem false_of_sq_le {x Q N : ℕ} (hQ : 64 ≤ Q) (hx : x ^ 2 ≤ Q) (hNx : N ≤ x + 1)
    (hN3 : Q + 1 ≤ 3 * N) : False := by
  have h1 : Q ≤ 3 * x + 2 := by omega
  have h2 : 21 ≤ x := by omega
  have h5 : 21 * x ≤ x ^ 2 :=
    calc 21 * x ≤ x * x := Nat.mul_le_mul_right _ h2
      _ = x ^ 2 := by ring
  nlinarith

end Arithmetic

section Dickson

variable {K : Type} [Field K]

open CFSG.Glauberman.Dickson CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
  CFSG.GorensteinWalter in
theorem card_ge_of_pair_of_order {p f : ℕ} [Fact p.Prime] [CharP K p]
    [Finite K] (hK : Nat.card K = p ^ (2 * f)) (hq : 64 ≤ p ^ f) (H : Subgroup (PSL2MatrixGroup K))
    {A B : SpecialLinearGroup (Fin 2) K} (hA : (A : PSL2MatrixGroup K) ∈ H)
    (hB : (B : PSL2MatrixGroup K) ∈ H) {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    {N : ℕ} (hμ : orderOf (μ ^ 2) = N) (hN : N ∣ p ^ f + 1) (hN3 : p ^ f + 1 ≤ 3 * N)
    (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card H := by
  classical
  have hp' : p.Prime := Fact.out
  have hf1 : 1 ≤ f := by
    by_contra hlt
    have : f = 0 := by omega
    subst this
    simp at hq
  have hN22 : 22 ≤ N := by omega
  have hord1 : orderOf (A : PSL2MatrixGroup K) = N := by
    rw [orderOf_mk_eq hP hAP]
    exact hμ
  have hdvd1 : orderOf (A : PSL2MatrixGroup K) ∣ p ^ f + 1 := by
    rw [hord1]
    exact hN
  have hμ4 : μ ^ 4 ≠ 1 := by
    intro h4
    have h2 : orderOf (μ ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h4)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hcop : Nat.Coprime p (p ^ f + 1) := by
    have : p ^ f + 1 = p * p ^ (f - 1) + 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hf1]
    rw [this, Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right p
  set a : H := ⟨(A : PSL2MatrixGroup K), hA⟩ with ha
  set b : H := ⟨(B : PSL2MatrixGroup K), hB⟩ with hb
  have hao : orderOf a = N := by rw [ha, Subgroup.orderOf_mk, hord1]
  have hbo : orderOf b = orderOf (B : PSL2MatrixGroup K) := Subgroup.orderOf_mk _ _
  have hcomm_false : (a * b = b * a) → False := by
    intro hab
    have hP' : (A : PSL2MatrixGroup K) * (B : PSL2MatrixGroup K) =
        (B : PSL2MatrixGroup K) * (A : PSL2MatrixGroup K) := congrArg Subtype.val hab
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_commute hP hAP hμ4 hP'
    exact hno x hx0 hxA hxB
  have hb3 : 2 < orderOf b := by rw [hbo]; exact hB3
  rcases dickson_psl2_subgroup_list hK H with
    ⟨_, _, _, hel⟩ | ⟨_, _, _, hcyc⟩ | ⟨_, _, _, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, _, _, _, _, _, E, _, hEn, hEel, hEcard, _, _, _, _, _, _, _, ⟨_⟩⟩ | ⟨m, hmf, ⟨e⟩⟩ |
      ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    have := hel
    have h1 : (A : PSL2MatrixGroup K) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := H) _ hA
    have h2 : orderOf (A : PSL2MatrixGroup K) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3 := Nat.dvd_gcd h2 hdvd1
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  ·
    exfalso
    exact hcomm_false (hcyc.commGroup.mul_comm a b)
  ·
    exfalso
    exact hcomm_false (commute_of_equiv_dihedral e (x := a) (y := b) (by omega) hb3)
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_alternating_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_perm_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_alternating_five e a with h | h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    have := hEn
    have := hEel
    have hE1 : E ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hEcard
      have : p ^ m = p ^ 0 := by rw [← hEcard, pow_zero]
      have := Nat.pow_right_injective hp'.two_le this
      omega
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_normal_pGroup hE1 hA hB
    exact hno x hx0 hxA hxB
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmf
      omega
    have hFm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases hfm : f ≤ m
    · have h1 := card_psl2_ge (GaloisField p m)
      rw [hFm] at h1
      have h2 : Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_congr e.toEquiv
      rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ ≤ _ := h1
    · exfalso
      push Not at hfm
      have h1 := psl2_orderOf_le (GaloisField p m) (e a)
      rw [MulEquiv.orderOf_eq, hFm, hao] at h1
      have h3m : 3 * m ≤ 2 * f := by
        obtain ⟨c, hc⟩ := hmf
        rcases c with _ | _ | _ | c
        · omega
        · omega
        · omega
        · nlinarith
      have hx : (p ^ m) ^ 3 ≤ (p ^ f) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
        exact Nat.pow_le_pow_right hp'.pos (by omega)
      exact false_of_cube_le_sq hq hx h1 hN3
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hmf
      omega
    have hFm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hmf' : m ∣ f := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hmf
    by_cases hfm : f ≤ m
    · have h2 : Nat.card H = p ^ m * (p ^ (2 * m) - 1) := by
        rw [Nat.card_congr e.toEquiv, MaxUp.card_pgl2_galoisField hm0]
      rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      have : (p ^ m) ^ 2 = p ^ (2 * m) := by rw [← pow_mul, mul_comm]
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ = p ^ m * (p ^ (2 * m) - 1) := by rw [this]
        _ ≤ 2 * (p ^ m * (p ^ (2 * m) - 1)) := Nat.le_mul_of_pos_left _ (by norm_num)
    · exfalso
      push Not at hfm
      have h1 := pgl2_orderOf_le (GaloisField p m) (e a)
      rw [MulEquiv.orderOf_eq, hFm, hao] at h1
      have h2m : 2 * m ≤ f :=
        MaxUp.two_mul_le_of_dvd_of_ne hmf' (Nat.ne_of_lt hfm) (by omega)
      have hx : (p ^ m) ^ 2 ≤ p ^ f := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right hp'.pos (by omega)
      exact false_of_sq_le hq hx h1 hN3

theorem card_ge_of_pgl_pair_of_order {p f : ℕ} [Fact p.Prime]
    [CharP K p] [Finite K] (hK : Nat.card K = p ^ (2 * f)) (hq : 64 ≤ p ^ f)
    (J : Subgroup PGL(Fin 2, K))
    (hJ : J ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    {A B : SpecialLinearGroup (Fin 2) K}
    (hA : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) ∈ J)
    (hB : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B) ∈ J)
    {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    {N : ℕ} (hμ : orderOf (μ ^ 2) = N) (hN : N ∣ p ^ f + 1) (hN3 : p ^ f + 1 ≤ 3 * N)
    (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card J := by
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hι
  set H : Subgroup (PSL2MatrixGroup K) := J.comap ι with hH
  have hmap : H.map ι = J := Subgroup.map_comap_eq_self hJ
  have hcard : Nat.card H = Nat.card J := by
    rw [← hmap]
    exact Nat.card_congr
      (H.equivMapOfInjective ι ProjectiveSpecialLinearGroup.toPGL_injective).toEquiv
  have hAH : (A : PSL2MatrixGroup K) ∈ H := by
    show ι (A : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hA
  have hBH : (B : PSL2MatrixGroup K) ∈ H := by
    show ι (B : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hB
  rw [← hcard]
  exact card_ge_of_pair_of_order hK hq H hAH hBH hP hAP hμ hN hN3 hB3 hno

end Dickson

section Homology

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem norm_eq_one_of_orderOf_dvd (h : UnitaryFieldData ℓ f K) {N : ℕ} (hN : N ∣ ℓ ^ f + 1)
    {σ : K} (hσ : orderOf σ = N) : h.bar σ * σ = 1 := by
  rw [bar_mul_self_eq_pow]
  exact orderOf_dvd_iff_pow_eq_one.1 (hσ ▸ hN)

theorem su2_le_of_two_homologies_of_order (h : UnitaryFieldData ℓ f K)
    (hq : 64 ≤ ℓ ^ f) {N : ℕ} (hN : N ∣ ℓ ^ f + 1) (hN3 : ℓ ^ f + 1 ≤ 3 * N)
    (X : Subgroup (GL (Fin 2) K)) {w u : Fin 2 → K} {σ ρ : K}
    (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0)
    (hu : h.bar (u 0) * u 0 + h.bar (u 1) * u 1 ≠ 0)
    (hwu : h.bar (w 0) * u 0 + h.bar (w 1) * u 1 ≠ 0) (hind : w 0 * u 1 - w 1 * u 0 ≠ 0)
    (hσ : orderOf σ = N) (hρ : orderOf ρ = N)
    (hX1 : ∃ g ∈ X, (g : Matrix (Fin 2) (Fin 2) K) = unitaryHomology h w σ)
    (hX2 : ∃ g ∈ X, (g : Matrix (Fin 2) (Fin 2) K) = unitaryHomology h u ρ) :
    unitarySU ℓ f K 2 ≤ X := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hσn := norm_eq_one_of_orderOf_dvd h hN hσ
  have hρn := norm_eq_one_of_orderOf_dvd h hN hρ
  have hN22 : 22 ≤ N := by omega
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hρ
    omega
  obtain ⟨g₁, hg₁X, hg₁⟩ := hX1
  obtain ⟨g₂, hg₂X, hg₂⟩ := hX2
  have hg₁u : g₁ ∈ gu2 h := ug82_homology_mem_gu2 h hw hσn hg₁
  have hg₂u : g₂ ∈ gu2 h := ug82_homology_mem_gu2 h hu hρn hg₂
  obtain ⟨s, μ, A, P, hs0, hAs, hμ2, hP, hAP, hevA⟩ := ug82_homology_data h hw hσn hσ1
  obtain ⟨t, ν, B, Q, ht0, hBt, hν2, hQ, hBQ, hevB⟩ := ug82_homology_data h hu hρn hρ1
  set Y : Subgroup (gu2 h) := X.subgroupOf (gu2 h) with hY
  let ψ : gu2 h →* PGL(Fin 2, K) := ProjGenLinGroup.mk.comp (gu2 h).subtype
  have hker : ψ.ker = (gu2Proj h).ker := by
    ext g
    rw [mem_ker_gu2Proj, MonoidHom.mem_ker]
    exact ProjGenLinGroup.mk_eq_one
  have hψrange : ψ.range ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    rintro _ ⟨g, rfl⟩
    exact mk_mem_range_toPGL _ (isSquare_of_norm_one h (norm_det_of_mem_gu2 h g.2))
  have hmk : ∀ (g : gu2 h) (v : K) (hv : v ≠ 0) (T : SpecialLinearGroup (Fin 2) K),
      ((T : Matrix (Fin 2) (Fin 2) K) = v • ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) →
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL T) = ψ g := by
    intro g v hv T hT
    show _ = ProjGenLinGroup.mk (g : GL (Fin 2) K)
    symm
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 v hv, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hT]
    ext i j
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hAJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) ∈ Y.map ψ := by
    rw [hmk ⟨g₁, hg₁u⟩ s hs0 A (by rw [hAs, hg₁])]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg₁X)
  have hBJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B) ∈ Y.map ψ := by
    rw [hmk ⟨g₂, hg₂u⟩ t ht0 B (by rw [hBt, hg₂])]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg₂X)
  have hμ : orderOf (μ ^ 2) = N := by rw [hμ2, hσ]
  have hB3 : 2 < orderOf (B : PSL2MatrixGroup K) := by
    have hν : orderOf (ν ^ 2) = N := by rw [hν2, hρ]
    rw [orderOf_mk_eq hQ hBQ, hν]
    omega
  have hbar0 : ∀ z : K, h.bar z = 0 → z = 0 := fun z hz => (map_eq_zero h.bar).1 hz
  have hno : ∀ x : Fin 2 → K, x ≠ 0 →
      (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False := by
    intro x hx0 hxA hxB
    rcases hevA x hx0 hxA with ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩ <;>
      rcases hevB x hx0 hxB with ⟨b, hb, hxb⟩ | ⟨b, hb, hxb⟩
    · exact hind (ug82_cross_eq_zero ha (hxa.symm.trans hxb))
    · have hc := ug82_cross_eq_zero ha (hxa.symm.trans hxb)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      apply hwu
      apply hbar0
      rw [map_add, map_mul, map_mul, h.bar_bar, h.bar_bar]
      linear_combination hc
    · have hc := ug82_cross_eq_zero ha (hxa.symm.trans hxb)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      apply hwu
      linear_combination -hc
    · have hc := ug82_cross_eq_zero ha (hxa.symm.trans hxb)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      apply hind
      apply hbar0
      rw [map_sub, map_mul, map_mul]
      linear_combination hc
  have hcard := card_ge_of_pgl_pair_of_order h.card hq (Y.map ψ)
    ((Y.map_le_range ψ).trans hψrange) hAJ hBJ hP hAP hμ hN hN3 hB3 hno
  rw [ug82_card_map_eq_of_ker_eq ψ (gu2Proj h) hker Y] at hcard
  have hSU := su2_le_of_card_ge h (by omega) Y hcard
  have hSUle : unitarySU ℓ f K 2 ≤ gu2 h := fun g hg =>
    (mem_gu2 h).2 ((mem_unitarySU_iff h).1 hg).2
  intro g hg
  exact hSU ⟨g, hSUle hg⟩ hg

end Homology

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
