module

public import CFSG.ClassicalInvolution.Q3.Q3T6FaField
public import CFSG.ClassicalInvolution.Q3.Q3NTUnitary
public import CFSG.ClassicalInvolution.AschTight.S19KUniIn

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

section Uni

theorem Fa.fixed_unitaryInvolution_three {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p]
    (hq : p ^ f = 3) (c : K) (hc : unitaryInvolution K p f c = c) :
    c = 0 ∨ c = 1 ∨ c = -1 := by
  rw [unitaryInvolution_apply, hq] at hc
  have h2 : c * ((c - 1) * (c + 1)) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem uni_lift_data_three (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : p ^ f = 3)
    {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = p ^ f) {E : Type} [Group E]
    (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) (φ : MulAut E)
    (hφ : ∃ (ι : ↥((S19K.rootU K p f).map θ) ≃* SL(2, F')) (g : GL (Fin 2) F'),
      ∀ x : ↥((S19K.rootU K p f).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((S19K.rootU K p f).map θ)) : E) = φ x) :
    ∃ (α : Phan.Su K p f 3 →* Phan.Su K p f 3) (G : GL (Fin 3) K) (τ : K ≃+* K),
      (∀ x, θ (α x) = φ (θ x)) ∧
      (∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (G : Matrix (Fin 3) (Fin 3) K) *
          τ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ∧
      ((G : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K p f)).transpose *
        (G : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      S19K.IsBlockDiag (G : Matrix (Fin 3) (Fin 3) K) ∧
      (τ = RingEquiv.refl K ∨ τ = unitaryInvolution K p f) := by
  obtain ⟨ι, g, hι⟩ := hφ
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨α, G, τ, hα, hform, hiso, -⟩ :=
    Q3.Q3NT.unitaryAutClassification_isometry_of_odd hK hp hf (le_refl 3) E θ hθ hker φ
  have hcl2 := Models.isClassicalSL2_rootSU2 (K := K) (p := p) (f := f) hK hp (n := 3)
    (by norm_num)
  have h3 : ¬ 3 ∣ p ^ f + 1 := by rw [hq]; decide
  have hinj : Function.Injective θ :=
    Fa.injective_of_center_eq_bot θ (Q3.Q3NT.center_su3_eq_bot hK hp hf h3) hker
  have hφL : ∀ x ∈ (S19K.rootU K p f).map θ, φ x ∈ (S19K.rootU K p f).map θ := fun x hx => by
    rw [← hι ⟨x, hx⟩]
    exact (ι.symm _).2
  have hαR := Fa.mem_of_lift_of_injective θ hinj hφL hα
  have hτ : ∀ c : K, unitaryInvolution K p f c = c → τ c = c := by
    intro c hc
    rcases Fa.fixed_unitaryInvolution_three hq c hc with rfl | rfl | rfl <;> simp
  refine ⟨α, G, τ, hα, hform, hiso, ?_, S19K.ringEquiv_eq_of_fixes hK τ hτ⟩
  set z₀ := Models.rootInvSU K p f (n := 3) (by norm_num)
  have hz₀R : z₀ ∈ S19K.rootU K p f := Models.rootInvSU_mem_rootSU2 _
  have hz₀2 : z₀ ^ 2 = 1 := by rw [← hcl2.orderOf_eq_two]; exact pow_orderOf_eq_one z₀
  have hαz : α z₀ = z₀ := by
    refine hcl2.eq_of_orderOf_eq_two (Models.odd_natCard_fixedSubfield hK hp) (hαR _ hz₀R)
      (orderOf_eq_prime ?_ ?_)
    · rw [← map_pow, hz₀2, map_one]
    · intro h1
      have h3 : θ z₀ = 1 := by
        apply φ.injective
        rw [← hα, h1, map_one, map_one]
      have h4 : z₀ = 1 := hinj (by rw [h3, map_one])
      have h5 := hcl2.orderOf_eq_two
      rw [h4, orderOf_one] at h5
      exact absurd h5 (by norm_num)
  have h2 : (2 : K) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  have h1 := hform z₀
  rw [hαz, S19K.coe_rootInvSU_three] at h1
  have hτz : τ.mapMatrix !![(-1 : K), 0, 0; 0, -1, 0; 0, 0, 1] =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [RingEquiv.mapMatrix_apply]
  rw [hτz] at h1
  refine S19K.isBlockDiag_of_commute_negBlock h2 _ ?_
  calc (G : Matrix (Fin 3) (Fin 3) K) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      (G : Matrix (Fin 3) (Fin 3) K) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
        (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K)) := by
        rw [Units.inv_mul, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, ← h1]

theorem uni_centralizer_three (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : p ^ f = 3)
    {E : Type} [Group E] (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) {φ : MulAut E}
    {α : Phan.Su K p f 3 →* Phan.Su K p f 3} {G : GL (Fin 3) K} {τ : K ≃+* K}
    (hα : ∀ x, θ (α x) = φ (θ x))
    (hform : ∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) *
        τ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hG : S19K.IsBlockDiag (G : Matrix (Fin 3) (Fin 3) K)) :
    (τ = RingEquiv.refl K →
      ∀ c ∈ Subgroup.centralizer (((S19K.rootU K p f).map θ : Subgroup E) : Set E), φ c = c) ∧
    (τ = unitaryInvolution K p f →
      ∀ c ∈ Subgroup.centralizer (((S19K.rootU K p f).map θ : Subgroup E) : Set E),
        φ c = c⁻¹) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have h3 : ¬ 3 ∣ p ^ f + 1 := by rw [hq]; decide
  have hinj : Function.Injective θ :=
    Fa.injective_of_center_eq_bot θ (Q3.Q3NT.center_su3_eq_bot hK hp hf h3) hker
  have key : ∀ c ∈ Subgroup.centralizer (((S19K.rootU K p f).map θ : Subgroup E) : Set E),
      ∃ x, θ x = c ∧ (τ = RingEquiv.refl K → α x = x) ∧
        (τ = unitaryInvolution K p f → α x = x⁻¹) := by
    intro c hc
    obtain ⟨x, rfl⟩ := hθ c
    exact ⟨x, rfl, S19K.uni_lift_apply_of_mem_centralizer hK hp (by omega) hform hG
      (Fa.mem_centralizer_of_map_of_injective θ hinj hc)⟩
  refine ⟨fun hτ c hc => ?_, fun hτ c hc => ?_⟩
  · obtain ⟨x, rfl, h1, -⟩ := key c hc
    rw [← hα, h1 hτ]
  · obtain ⟨x, rfl, -, h2⟩ := key c hc
    rw [← hα, h2 hτ, map_inv]

theorem flUni_three (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : p ^ f = 3)
    {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = p ^ f) {E : Type} [Group E]
    (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) (φ : MulAut E)
    (hφ : ∃ (ι : ↥((S19K.rootU K p f).map θ) ≃* SL(2, F')) (g : GL (Fin 2) F'),
      ∀ x : ↥((S19K.rootU K p f).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((S19K.rootU K p f).map θ)) : E) = φ x) :
    ((∀ c ∈ Subgroup.centralizer (((S19K.rootU K p f).map θ : Subgroup E) : Set E), φ c = c) ∨
      (∀ c ∈ Subgroup.centralizer (((S19K.rootU K p f).map θ : Subgroup E) : Set E),
        φ c = c⁻¹)) ∧
    (φ * φ = 1 → (∃ c ∈ Subgroup.centralizer (((S19K.rootU K p f).map θ : Subgroup E) : Set E),
        φ c = c ∧ c * c ≠ 1) → ∃ y : E, φ = MulAut.conj y) := by
  obtain ⟨α, G, τ, hα, hform, hiso, hG, hτ⟩ := uni_lift_data_three hK hp hq hF' θ hθ hker φ hφ
  obtain ⟨hC1, hC2⟩ := uni_centralizer_three hK hp hq θ hθ hker hα hform hG
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  refine ⟨hτ.imp hC1 hC2, fun hφ2 ⟨c, hc, hφc, hcc⟩ => ?_⟩
  rcases hτ with h | h
  · subst h
    refine S19K.uni_inner hK hp hf θ hθ hker hα (fun x => ?_) hiso hφ2
    rw [hform, RingEquiv.mapMatrix_refl]
    rfl
  · have h1 := hC2 h c hc
    rw [hφc] at h1
    refine absurd ?_ hcc
    calc c * c = c * c⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel c

end Uni

end CFSG.ClassicalInvolution.Q3.Q3T6
