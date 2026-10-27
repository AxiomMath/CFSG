module

public import CFSG.ClassicalInvolution.AschTight.S19KGen
public import CFSG.ClassicalInvolution.AschTight.S19KLinStd

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem trace_mapMatrix (σ : F ≃+* F) (M : Matrix (Fin 3) (Fin 3) F) :
    (σ.mapMatrix M).trace = σ M.trace := by
  simp [RingEquiv.mapMatrix_apply, Matrix.trace]

@[expose] def twist (ε : Bool) (x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F :=
  if ε then (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose
  else (x : Matrix (Fin 3) (Fin 3) F)

variable [Finite F]

theorem lin_lift_data (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
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
        (G : Matrix (Fin 3) (Fin 3) F) * twist ε x * ((G⁻¹ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)) ∧
      IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨ι, g, hι⟩ := hφ
  obtain ⟨α, G, σ, ε, hα, hform0⟩ := hcl E θ hθ hker φ
  have hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * σ.mapMatrix (twist ε x) *
        ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := hform0
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_odd_natCard hodd
  have hcl2 := Models.isClassicalSL2_rootSL2 (K := F) h2 (n := 3) (by norm_num)
  have : Group.IsPerfect (Models.rootSL2 F (n := 3) (by norm_num)) := hcl2.isPerfect (by omega)
  have hR : ∀ r ∈ Models.rootSL2 F (n := 3) (by norm_num), r ∈ Subgroup.center SL(3, F) →
      r = 1 := fun r hr hc => eq_one_of_mem_center_rootSL2 hr hc
  have hφL : ∀ x ∈ (Models.rootSL2 F (n := 3) (by norm_num)).map θ,
      φ x ∈ (Models.rootSL2 F (n := 3) (by norm_num)).map θ := fun x hx => by
    rw [← hι ⟨x, hx⟩]
    exact (ι.symm _).2
  have hαR := mem_of_lift θ hker hR hφL hα
  have htr := trace_eq_of_conj hodd h5 stdEquiv ((restrictEquiv θ hker hR).trans ι)
    (liftRestrict α hαR) g (semilin_restrict θ hker hR hα hαR ι g hι)
  have htw : ∀ x ∈ Models.rootSL2 F (n := 3) (by norm_num), (twist ε x).trace =
      ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace := fun x hx => by
    cases ε
    · rfl
    · exact trace_inv_transpose hx
  have hσ : ∀ c : F, σ c = c := by
    intro c
    set r : Models.rootSL2 F (n := 3) (by norm_num) :=
      ⟨WeakCT.blockSL F 3 2 0 (by norm_num) (traceSL c), ⟨_, rfl⟩⟩
    have e1 := trace_eq_stdEquiv (liftRestrict α hαR r)
    rw [coe_liftRestrict, htr, ← trace_eq_stdEquiv, hform, Matrix.trace_units_conj,
      trace_mapMatrix, htw _ r.2] at e1
    have e2 : ((r : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).trace = c + 1 := by
      rw [trace_blockSL3, trace_traceSL]
    rw [e2, map_add, map_one] at e1
    exact add_right_cancel e1
  obtain rfl : σ = RingEquiv.refl F := RingEquiv.ext hσ
  have hform' : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * twist ε x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := fun x => by
    rw [hform, RingEquiv.mapMatrix_refl]
    rfl
  refine ⟨α, G, ε, hα, hform', ?_⟩
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
      have h4 := hR z₀ hz₀R (hker h3)
      have h5 := hcl2.orderOf_eq_two
      rw [h4, orderOf_one] at h5
      exact absurd h5 (by norm_num)
  have htz : twist ε z₀ = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    have hinv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz₀2])
    cases ε
    · exact coe_rootInv_three
    · show (((z₀⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose = _
      rw [hinv, coe_rootInv_three]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  have h1 := hform' z₀
  rw [hαz, htz, coe_rootInv_three] at h1
  refine isBlockDiag_of_commute_negBlock h2 _ ?_
  calc (G : Matrix (Fin 3) (Fin 3) F) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      (G : Matrix (Fin 3) (Fin 3) F) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
        (((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (G : Matrix (Fin 3) (Fin 3) F)) := by
        rw [Units.inv_mul, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, ← h1]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
