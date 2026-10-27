module

public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem thm5IH_commute_of_glConjSL_fix {D : GL (Fin 2) F} {X : SL2 F} (hX : glConjSL D X = X) :
    (D : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) =
      (X : Matrix (Fin 2) (Fin 2) F) * D := by
  have h := congrArg Subtype.val hX
  rw [glConjSL_coe] at h
  calc (D : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F)
      = (D : Matrix (Fin 2) (Fin 2) F) * X *
        (((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * D) := by
        rw [gl_inv_mul, Matrix.mul_one]
    _ = ((D : Matrix (Fin 2) (Fin 2) F) * X *
        ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * D := by
        simp only [Matrix.mul_assoc]
    _ = (X : Matrix (Fin 2) (Fin 2) F) * D := by rw [h]

theorem thm5IH_scalar_of_glConjSL [Finite F] (hodd : Odd (Nat.card F)) {D : GL (Fin 2) F}
    (h : ∀ A, glConjSL D A = A) : ∃ μ : F, (D : Matrix (Fin 2) (Fin 2) F) = μ • 1 := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one hodd
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  exact scalar_of_commute_quat hab h2 (thm5IH_commute_of_glConjSL_fix (h quatI))
    (thm5IH_commute_of_glConjSL_fix (h (quatJ hab)))

end SL2

section Diagonal

variable {F : Type} [Field F]

theorem thm5IH_exists_HSL {χ : Fˣ} {A : SL2 F}
    (h : ∃ μ : F, ((diagGL χ * Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = μ • 1) : ∃ s : Fˣ, A = HSL s := by
  obtain ⟨μ, hμ⟩ := h
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have h01' : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h := congrFun (congrFun hμ 0) 1
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  have h10' : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h := congrFun (congrFun hμ 1) 0
    simpa [diagGL, Matrix.mul_apply, Fin.sum_univ_two] using h
  rw [h01', h10'] at hdet
  have hne : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  refine ⟨Units.mk0 _ hne, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact h01'
  · exact h10'
  · have : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = ((A : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right (by linear_combination hdet)
    simpa [HSL] using this

end Diagonal

section OddNormal

theorem thm5IH_sl2_zmod3_odd_normal_eq_bot {M : Subgroup (SL2 (ZMod 3))} (hn : M.Normal)
    (hM : Odd (Nat.card M)) : M = ⊥ := by
  have hcard : Nat.card (SL2 (ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hdvd : Nat.card M ∣ 24 := hcard ▸ Subgroup.card_subgroup_dvd_card M
  have h3 : Nat.card M ∣ 3 := by
    have h24 : Nat.card M ∈ Nat.divisors 24 := by simpa using hdvd
    have hodd := Nat.odd_iff.mp hM
    have hdiv : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
    rw [hdiv] at h24
    simp only [Finset.mem_insert, Finset.mem_singleton] at h24
    rcases h24 with h | h | h | h | h | h | h | h <;> rw [h] at hodd ⊢ <;> simp at hodd ⊢
  have hcube : ∀ m ∈ M, m ^ 3 = 1 := fun m hm =>
    orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard M hm).trans h3)
  have key : ∀ m : SL2 (ZMod 3), m ≠ 1 → m ^ 3 = 1 →
      ∃ g : SL2 (ZMod 3), (m * g * m⁻¹ * g⁻¹) ^ 3 ≠ 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  by_contra hm1
  obtain ⟨g, hg⟩ := key m hm1 (hcube m hm)
  apply hg
  have hmem : m * g * m⁻¹ * g⁻¹ ∈ M := by
    have e : m * g * m⁻¹ * g⁻¹ = m * (g * m⁻¹ * g⁻¹) := by group
    rw [e]
    exact M.mul_mem hm (hn.conj_mem _ (M.inv_mem hm) g)
  exact hcube _ hmem

theorem thm5IH_sl2_odd_normal_eq_bot {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {M₁ : Subgroup (SL2 F)} (hn : M₁.Normal) (hM : Odd (Nat.card M₁)) : M₁ = ⊥ := by
  classical
  by_cases h4 : 4 ≤ Nat.card F
  · have hno : ∀ A : SL2 F, A ∈ M₁ → A * A = 1 → A = 1 := by
      intro A hA hA2
      have hd2 : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hA2)
      have hdc : orderOf A ∣ Nat.card M₁ := Subgroup.orderOf_dvd_natCard M₁ hA
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        rw [h] at hdc
        obtain ⟨k, hk⟩ := hdc
        have := Nat.odd_iff.mp hM
        omega
    have hneg : (-1 : SL2 F) * (-1) = 1 := by simp
    have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
    have hne : (-1 : SL2 F) ≠ 1 := by
      intro h
      have h1 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      apply h2
      simp at h1
      linear_combination -h1
    rcases sl2_normal_le_center_or_eq_top h4 hn with hc | htop
    · rw [eq_bot_iff]
      intro A hA
      rw [Subgroup.mem_bot]
      rcases CFSG.LieType.Chevalley.sl2_eq_one_or_neg_one_of_mem_center (hc hA) with h1 | h1
      · exact h1
      · exact absurd (hno A hA (by rw [h1]; exact hneg)) (by rw [h1]; exact hne)
    · exact absurd (hno (-1) (by rw [htop]; exact Subgroup.mem_top _) hneg) hne
  · have hone : 1 < Nat.card F := Finite.one_lt_card
    have h3 : Nat.card F = 3 := by
      have := Nat.odd_iff.mp hodd
      omega
    have : Fintype F := Fintype.ofFinite F
    let e : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
      (by rw [← Nat.card_eq_fintype_card]; exact h3)
    let φ : SL2 (ZMod 3) →* SL2 F := Matrix.SpecialLinearGroup.map e.toRingHom
    let ψ : SL2 F →* SL2 (ZMod 3) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
    have hφψ : ∀ g, φ (ψ g) = g := fun g => by
      ext i j
      simp [φ, ψ]
    have hφinj : Function.Injective φ := fun a b hab => by
      ext i j
      have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) i j) hab
      simpa [φ] using this
    set M' : Subgroup (SL2 (ZMod 3)) := M₁.comap φ with hM'
    have hM'n : M'.Normal := hn.comap φ
    have hM'odd : Odd (Nat.card M') := by
      have h1 : Nat.card (M'.map φ) = Nat.card M' := Subgroup.card_map_of_injective hφinj
      have h2 : M'.map φ ≤ M₁ := Subgroup.map_comap_le φ M₁
      rw [← h1]
      exact hM.of_dvd_nat (Subgroup.card_dvd_of_le h2)
    have hM'bot := thm5IH_sl2_zmod3_odd_normal_eq_bot hM'n hM'odd
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hψg : ψ g ∈ M' := by
      show φ (ψ g) ∈ M₁
      rw [hφψ]
      exact hg
    rw [hM'bot, Subgroup.mem_bot] at hψg
    rw [← hφψ g, hψg, map_one]

end OddNormal

section Chart

variable {F : Type} [Field F] [Finite F] {M : Type*} [Group M]

theorem thm5IH_odd_normal_centralizes_chart (hodd : Odd (Nat.card F))
    {Φ : SL2 F →* M} (hΦ : Function.Injective Φ) {X : Subgroup M} (hQX : Φ.range ≤ X)
    (hXQ : X ≤ Subgroup.normalizer (Φ.range : Set M)) {N : Subgroup M} (hNX : N ≤ X)
    (hNconj : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hNodd : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ A : SL2 F, n * Φ A = Φ A * n := by
  classical
  set M₁ : Subgroup (SL2 F) := N.comap Φ with hM₁
  have hM₁n : M₁.Normal := ⟨fun A hA B => by
    show Φ (B * A * B⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNconj _ (hQX ⟨B, rfl⟩) _ hA⟩
  have hM₁odd : Odd (Nat.card M₁) := by
    have h1 : Nat.card (M₁.map Φ) = Nat.card M₁ := Subgroup.card_map_of_injective hΦ
    have h2 : M₁.map Φ ≤ N := Subgroup.map_comap_le Φ N
    rw [← h1]
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le h2)
  have hM₁bot : M₁ = ⊥ := thm5IH_sl2_odd_normal_eq_bot hodd hM₁n hM₁odd
  intro n hn A
  have hnX : n ∈ X := hNX hn
  have h1 : n * Φ A * n⁻¹ ∈ Φ.range :=
    (Subgroup.mem_normalizer_iff.mp (hXQ hnX) (Φ A)).mp ⟨A, rfl⟩
  have h2 : n * Φ A * n⁻¹ * (Φ A)⁻¹ ∈ Φ.range :=
    Φ.range.mul_mem h1 (Φ.range.inv_mem ⟨A, rfl⟩)
  obtain ⟨A', hA'⟩ := h2
  have h3 : n * Φ A * n⁻¹ * (Φ A)⁻¹ ∈ N := by
    have e : n * Φ A * n⁻¹ * (Φ A)⁻¹ = n * (Φ A * n⁻¹ * (Φ A)⁻¹) := by group
    rw [e]
    exact N.mul_mem hn (hNconj _ (hQX ⟨A, rfl⟩) _ (N.inv_mem hn))
  have h4' : A' ∈ M₁ := by
    show Φ A' ∈ N
    rw [hA']
    exact h3
  rw [hM₁bot, Subgroup.mem_bot] at h4'
  rw [h4', map_one] at hA'
  have h5 : n * Φ A * n⁻¹ = Φ A := mul_inv_eq_one.mp hA'.symm
  exact mul_inv_eq_iff_eq_mul.mp h5

end Chart

section Diag

variable {F : Type} [Field F] [Finite F]

theorem thm5IH_diagGL_eq_one (hodd : Odd (Nat.card F)) {s : Fˣ}
    (h : ∀ M, glConjSL (diagGL s) M = M) : s = 1 := by
  obtain ⟨μ, hμ⟩ := thm5IH_scalar_of_glConjSL hodd h
  have h00 := congrFun (congrFun hμ 0) 0
  have h11 := congrFun (congrFun hμ 1) 1
  simp [diagGL] at h00 h11
  exact Units.ext (by rw [h00, ← h11]; rfl)

omit [Finite F] in
theorem thm5IH_odd_card_of_two_ne_zero [Finite F] (h : (2 : F) ≠ 0) : Odd (Nat.card F) := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  apply FiniteField.odd_card_of_char_ne_two
  intro h2
  apply h
  have : CharP F 2 := ringChar.of_eq h2
  exact_mod_cast CharP.cast_eq_zero F 2

end Diag

theorem thm5IH_le_normalizer_of_conj_mem {G : Type*} [Group G] {X Q : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q) : X ≤ Subgroup.normalizer (Q : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem thm5IH_sl2_neg_one_comm {F : Type} [Field F] (A : SL2 F) : A * (-1) = (-1) * A := by
  apply Subtype.ext
  simp


end CFSG.ClassicalInvolution.Asc77
