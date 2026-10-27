module

public import CFSG.ClassicalInvolution.Q3.Q3T6FaField
public import CFSG.ClassicalInvolution.AschTight.S19KLinFL

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Lin

theorem lin_lift_data_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    (hcl : RouteD.Gaps.LinearAutClassification F 3) {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) (φ : MulAut E)
    (hφ : ∃ (ι : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ) ≃* SL(2, F))
        (g : GL (Fin 2) F),
      ∀ x : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ)) : E) = φ x) :
    ∃ (α : SL(3, F) →* SL(3, F)) (G : GL (Fin 3) F) (ε : Bool),
      (∀ x, θ (α x) = φ (θ x)) ∧
      (∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        (G : Matrix (Fin 3) (Fin 3) F) * S19K.twist ε x * ((G⁻¹ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)) ∧
      S19K.IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨ι, g, hι⟩ := hφ
  obtain ⟨α, G, σ, ε, hα, hform0⟩ := hcl E θ hθ hker φ
  obtain rfl : σ = RingEquiv.refl F := Fa.ringEquiv_eq_refl hF σ
  have hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * S19K.twist ε x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := fun x => by
    rw [hform0, RingEquiv.mapMatrix_refl]
    rfl
  have h2 : (2 : F) ≠ 0 := Fa.two_ne_zero hF
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hcl2 := Models.isClassicalSL2_rootSL2 (K := F) h2 (n := 3) (by norm_num)
  have hinj : Function.Injective θ :=
    Fa.injective_of_center_eq_bot θ (Fa.center_specialLinear_eq_bot hF) hker
  have hφL : ∀ x ∈ (Models.rootSL2 F (n := 3) (by norm_num)).map θ,
      φ x ∈ (Models.rootSL2 F (n := 3) (by norm_num)).map θ := fun x hx => by
    rw [← hι ⟨x, hx⟩]
    exact (ι.symm _).2
  have hαR := Fa.mem_of_lift_of_injective θ hinj hφL hα
  refine ⟨α, G, ε, hα, hform, ?_⟩
  set z₀ := Models.rootInv F (n := 3) (by norm_num)
  have hz₀R : z₀ ∈ Models.rootSL2 F (n := 3) (by norm_num) := Models.rootInv_mem_rootSL2 _
  have hz₀2 : z₀ ^ 2 = 1 := by rw [← hcl2.orderOf_eq_two]; exact pow_orderOf_eq_one z₀
  have hαz : α z₀ = z₀ := by
    refine hcl2.eq_of_orderOf_eq_two hodd (hαR _ hz₀R) (orderOf_eq_prime ?_ ?_)
    · rw [← map_pow, hz₀2, map_one]
    · intro h1
      have h3 : θ z₀ = 1 := by
        apply φ.injective
        rw [← hα, h1, map_one, map_one]
      have h4 : z₀ = 1 := hinj (by rw [h3, map_one])
      have h5 := hcl2.orderOf_eq_two
      rw [h4, orderOf_one] at h5
      exact absurd h5 (by norm_num)
  have htz : S19K.twist ε z₀ = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    have hinv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz₀2])
    cases ε
    · exact S19K.coe_rootInv_three
    · show (((z₀⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose = _
      rw [hinv, S19K.coe_rootInv_three]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  have h1 := hform z₀
  rw [hαz, htz, S19K.coe_rootInv_three] at h1
  refine S19K.isBlockDiag_of_commute_negBlock h2 _ ?_
  calc (G : Matrix (Fin 3) (Fin 3) F) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      (G : Matrix (Fin 3) (Fin 3) F) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
        (((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (G : Matrix (Fin 3) (Fin 3) F)) := by
        rw [Units.inv_mul, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, ← h1]

theorem lin_centralizer_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {E : Type}
    [Group E] (θ : SL(3, F) →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {φ : MulAut E} {α : SL(3, F) →* SL(3, F)}
    {G : GL (Fin 3) F} {ε : Bool} (hα : ∀ x, θ (α x) = φ (θ x))
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * S19K.twist ε x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F))
    (hG : S19K.IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F)) :
    ∀ c ∈ Subgroup.centralizer
      (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
      φ c = if ε then c⁻¹ else c := by
  intro c hc
  have hinj : Function.Injective θ :=
    Fa.injective_of_center_eq_bot θ (Fa.center_specialLinear_eq_bot hF) hker
  obtain ⟨x, rfl⟩ := hθ c
  have hx := Fa.mem_centralizer_of_map_of_injective θ hinj hc
  rw [← hα, S19K.lift_apply_of_mem_centralizer hform hG hx]
  cases ε <;> simp

theorem flLin_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    (hcl : RouteD.Gaps.LinearAutClassification F 3) {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) (φ : MulAut E)
    (hφ : ∃ (ι : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ) ≃* SL(2, F))
        (g : GL (Fin 2) F),
      ∀ x : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ)) : E) = φ x) :
    ((∀ c ∈ Subgroup.centralizer
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E), φ c = c) ∨
      (∀ c ∈ Subgroup.centralizer
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
          φ c = c⁻¹)) ∧
    (φ * φ = 1 → (∃ c ∈ Subgroup.centralizer
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
          φ c = c ∧ c * c ≠ 1) → ∃ y : E, φ = MulAut.conj y) := by
  obtain ⟨α, G, ε, hα, hform, hG⟩ := lin_lift_data_three hF hcl θ hθ hker φ hφ
  have hC := lin_centralizer_three hF θ hθ hker hα hform hG
  refine ⟨?_, fun hφ2 ⟨c, hc, hφc, hcc⟩ => ?_⟩
  · cases ε
    · exact Or.inl fun c hc => by simpa using hC c hc
    · exact Or.inr fun c hc => by simpa using hC c hc
  · cases ε
    · exact S19K.lin_inner θ hθ hker hα hform hφ2
    · have h1 : φ c = c⁻¹ := by simpa using hC c hc
      rw [hφc] at h1
      refine absurd ?_ hcc
      calc c * c = c * c⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel c

end Lin

end CFSG.ClassicalInvolution.Q3.Q3T6
