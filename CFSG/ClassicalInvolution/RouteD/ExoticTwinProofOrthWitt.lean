module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthGeom
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam hypComb hypComb_injective map_hypComb)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Hyp

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem isHypFam_of_table (u w : Fin 4 → V) (hu : ∀ i, Q (u i) = 0) (hw : ∀ i, Q (w i) = 0)
    (huu : ∀ i j, polar Q (u i) (u j) = 0) (hww : ∀ i j, polar Q (w i) (w j) = 0)
    (huw : ∀ i j, polar Q (u i) (w j) = if i = j then 1 else 0) :
    IsHypFam Q (fun (i : Fin 4) (s : Bool) => if s then u i else w i) := by
  refine ⟨fun i s => ?_, fun i j hij s t => ?_, fun i s => ?_⟩
  · cases s
    · exact hw i
    · exact hu i
  · cases s <;> cases t
    · exact hww i j
    · simpa [polar_comm Q (w i) (u j), hij.symm] using huw j i
    · simpa [hij] using huw i j
    · exact huu i j
  · cases s
    · simpa using (polar_comm Q (w i) (u i)).trans (by simpa using huw i i)
    · simpa using huw i i

theorem isHypFam_of_orth (F₀ F₁ : OFrame Q) (h : F₁.span ≤ F₀.perp) :
    IsHypFam Q (fun (i : Fin 4) (s : Bool) =>
      if s then ![F₀.e₁, F₀.e₂, F₁.e₁, F₁.e₂] i else ![F₀.f₁, F₀.f₂, F₁.f₁, F₁.f₂] i) := by
  obtain ⟨a11, a12, a13, a14⟩ := (mem_perp_iff_four F₀).mp (h F₁.e₁_mem_span)
  obtain ⟨a21, a22, a23, a24⟩ := (mem_perp_iff_four F₀).mp (h F₁.f₁_mem_span)
  obtain ⟨a31, a32, a33, a34⟩ := (mem_perp_iff_four F₀).mp (h F₁.e₂_mem_span)
  obtain ⟨a41, a42, a43, a44⟩ := (mem_perp_iff_four F₀).mp (h F₁.f₂_mem_span)
  have c11 : polar Q F₀.e₁ F₁.e₁ = 0 := by rw [polar_comm]; exact a11
  have c12 : polar Q F₀.f₁ F₁.e₁ = 0 := by rw [polar_comm]; exact a12
  have c13 : polar Q F₀.e₂ F₁.e₁ = 0 := by rw [polar_comm]; exact a13
  have c14 : polar Q F₀.f₂ F₁.e₁ = 0 := by rw [polar_comm]; exact a14
  have c21 : polar Q F₀.e₁ F₁.f₁ = 0 := by rw [polar_comm]; exact a21
  have c22 : polar Q F₀.f₁ F₁.f₁ = 0 := by rw [polar_comm]; exact a22
  have c23 : polar Q F₀.e₂ F₁.f₁ = 0 := by rw [polar_comm]; exact a23
  have c24 : polar Q F₀.f₂ F₁.f₁ = 0 := by rw [polar_comm]; exact a24
  have c31 : polar Q F₀.e₁ F₁.e₂ = 0 := by rw [polar_comm]; exact a31
  have c32 : polar Q F₀.f₁ F₁.e₂ = 0 := by rw [polar_comm]; exact a32
  have c33 : polar Q F₀.e₂ F₁.e₂ = 0 := by rw [polar_comm]; exact a33
  have c34 : polar Q F₀.f₂ F₁.e₂ = 0 := by rw [polar_comm]; exact a34
  have c41 : polar Q F₀.e₁ F₁.f₂ = 0 := by rw [polar_comm]; exact a41
  have c42 : polar Q F₀.f₁ F₁.f₂ = 0 := by rw [polar_comm]; exact a42
  have c43 : polar Q F₀.e₂ F₁.f₂ = 0 := by rw [polar_comm]; exact a43
  have c44 : polar Q F₀.f₂ F₁.f₂ = 0 := by rw [polar_comm]; exact a44
  refine isHypFam_of_table _ _ (fun i => ?_) (fun i => ?_) (fun i j => ?_) (fun i j => ?_)
    (fun i j => ?_)
  · fin_cases i <;> simp [F₀.Q_e₁, F₀.Q_e₂, F₁.Q_e₁, F₁.Q_e₂]
  · fin_cases i <;> simp [F₀.Q_f₁, F₀.Q_f₂, F₁.Q_f₁, F₁.Q_f₂]
  · fin_cases i <;> fin_cases j <;> simp [F₀.polar_e₁_e₁, F₀.polar_e₁_e₂, F₀.polar_e₂_e₁,
      F₀.polar_e₂_e₂, F₁.polar_e₁_e₁, F₁.polar_e₁_e₂, F₁.polar_e₂_e₁, F₁.polar_e₂_e₂, a11, a13,
      a31, a33, c11, c13, c31, c33]
  · fin_cases i <;> fin_cases j <;> simp [F₀.polar_f₁_f₁, F₀.polar_f₁_f₂, F₀.polar_f₂_f₁,
      F₀.polar_f₂_f₂, F₁.polar_f₁_f₁, F₁.polar_f₁_f₂, F₁.polar_f₂_f₁, F₁.polar_f₂_f₂, a22, a24,
      a42, a44, c22, c24, c42, c44]
  · fin_cases i <;> fin_cases j <;> simp [F₀.polar_e₁_f₁, F₀.polar_e₁_f₂, F₀.polar_e₂_f₁,
      F₀.polar_e₂_f₂, F₁.polar_e₁_f₁, F₁.polar_e₁_f₂, F₁.polar_e₂_f₁, F₁.polar_e₂_f₂, a12, a14,
      a32, a34, c21, c23, c41, c43]

end Hyp

section Count

variable {F : Type} [Field F] [Finite F]

theorem false_of_orth_quadMinus_four (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 4 ≤ Nat.card F)
    (F₀ F₁ : OFrame (quadMinus 4 F b c)) (h : F₁.span ≤ F₀.perp) : False := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hv := isHypFam_of_orth F₀ F₁ h
  set v : Fin 4 → Bool → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := fun (i : Fin 4) (s : Bool) =>
      if s then ![F₀.e₁, F₀.e₂, F₁.e₁, F₁.e₂] i else ![F₀.f₁, F₀.f₂, F₁.f₁, F₁.f₂] i with hvdef
  let e' : Fin 4 × Bool ≃ Fin 4 ⊕ Fin 4 :=
    (Equiv.prodComm (Fin 4) Bool).trans (Equiv.boolProdEquivSum (Fin 4))
  let ψ₀ : (Fin 4 ⊕ Fin 4 → F) →ₗ[F] (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) :=
    (hypComb v).comp (LinearMap.funLeft F F e')
  have hψQ : ∀ w, quadMinus 4 F b c (ψ₀ w) = quadPlus 4 F w := by
    intro w
    show quadMinus 4 F b c (hypComb v (w ∘ e')) = _
    rw [map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w (e' (i, true)) * w (e' (i, false)) = _
    simp [e', Equiv.boolProdEquivSum, mul_comm]
  have hinj : Function.Injective ψ₀ :=
    (hypComb_injective hv).comp (LinearMap.funLeft_injective_of_surjective F F e' e'.surjective)
  have hdim : Module.finrank F (Fin 4 ⊕ Fin 4 → F) =
      Module.finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  have hsurj : Function.Surjective ψ₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hcard : Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} =
      Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) // quadMinus 4 F b c x = 0} :=
    Nat.card_congr ((Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩).subtypeEquiv fun w => by
      rw [show (Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩) w = ψ₀ w from rfl, hψQ w])
  have e1 : (Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) :=
    CFSG.ClassicalInvolution.card_singular_quadPlus 3
  have e2 : (Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) // quadMinus 4 F b c x = 0} :
      ℤ) = 1 + ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) :=
    CFSG.ClassicalInvolution.card_singular_quadMinus_of_two_ne_zero h2 hirr 3
  rw [hcard] at e1
  have hq : (4 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast h4
  have key : ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) -
      ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) =
      2 * ((Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1)) := by ring
  have hpos : 0 < (Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1) :=
    mul_pos (pow_pos (by linarith) 3) (by linarith)
  linarith

end Count

end CFSG.ClassicalInvolution.RouteD.Exotic
