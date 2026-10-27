module

public import CFSG.GH74.GLS.SP.Local.SPLSL2ThreeField
public import CFSG.GH74.GLS.LU.Local.SL2Aut2
public import CFSG.GH74.GLS.IVK.L2.TorusMatrices
public import CFSG.GH74.GLS.LU.Local.SL2Aux

public section

namespace CFSG.GH74.GLS.SP.Local.SL2Three

open Matrix CFSG.Semidihedral.OddFieldSL2 CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.LU.Local
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL slConjugation_matrix)
open scoped MatrixGroups

section Anticomm

variable {F : Type} [Field F]

theorem matrix_rel_of_anticomm (α β : SL(2, F))
    (hα : α * α = minusIdentity F) (hβ : β * β = minusIdentity F)
    (hβα : β * α = α * β * minusIdentity F) :
    (α : Matrix (Fin 2) (Fin 2) F) * α = -1 ∧ (β : Matrix (Fin 2) (Fin 2) F) * β = -1 ∧
      (β : Matrix (Fin 2) (Fin 2) F) * α = -((α : Matrix (Fin 2) (Fin 2) F) * β) := by
  have hneg : ((minusIdentity F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [minusIdentity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hα
    simpa [hneg] using this
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hβ
    simpa [hneg] using this
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hβα
    simpa [hneg] using this

theorem exists_smul_one_of_comm (h2 : (2 : F) ≠ 0) (α β : SL(2, F))
    (hα : α * α = minusIdentity F) (hβ : β * β = minusIdentity F)
    (hβα : β * α = α * β * minusIdentity F) (X : Matrix (Fin 2) (Fin 2) F)
    (hXα : X * α = α * X) (hXβ : X * β = β * X) :
    ∃ c : F, X = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨hA, hB, hBA⟩ := matrix_rel_of_anticomm α β hα hβ hβα
  obtain ⟨h01, h10, h00⟩ := SL2.scalar_of_comm_anticomm h2 _ _ _ α.2 β.2 hA hB hBA hXα hXβ
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]

theorem mul_comm_of_slConjugation_eq (G : GL (Fin 2) F) (x : SL(2, F))
    (h : slConjugation F G x = x) :
    (G : Matrix (Fin 2) (Fin 2) F) * x = x * G := by
  have h2 := congrArg SpecialLinearGroup.toGL h
  rw [slConjugation_toGL] at h2
  have h3 : G * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * G := by
    calc G * SpecialLinearGroup.toGL x = (G * SpecialLinearGroup.toGL x * G⁻¹) * G := by group
      _ = SpecialLinearGroup.toGL x * G := by rw [h2]
  have h4 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
  simpa using h4

end Anticomm

section Cyclic

variable {F : Type} [Field F] [Finite F]

theorem eq_one_of_right_eq_one (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (α β : SL(2, F))
    (hα : α * α = minusIdentity F) (hβ : β * β = minusIdentity F)
    (hβα : β * α = α * β * minusIdentity F) (φ : MulAut SL(2, F)) (hφα : φ α = α) (hφβ : φ β = β)
    (h1 : (gammaOf hodd h3 φ).right = 1) : φ = 1 := by
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 φ h1
  have h2 := two_ne_zero_of_odd_card F hodd
  have hGα : (G : Matrix (Fin 2) (Fin 2) F) * α = α * G :=
    mul_comm_of_slConjugation_eq G α (by rw [← hG]; exact hφα)
  have hGβ : (G : Matrix (Fin 2) (Fin 2) F) * β = β * G :=
    mul_comm_of_slConjugation_eq G β (by rw [← hG]; exact hφβ)
  obtain ⟨c, hc⟩ := exists_smul_one_of_comm h2 α β hα hβ hβα _ hGα hGβ
  rw [hG]
  exact slConjugation_eq_one_of_scalar G c hc

theorem isCyclic_of_fix (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (α β : SL(2, F))
    (hα : α * α = minusIdentity F) (hβ : β * β = minusIdentity F)
    (hβα : β * α = α * β * minusIdentity F) (Φ : Subgroup (MulAut SL(2, F)))
    (hfix : ∀ φ ∈ Φ, φ α = α ∧ φ β = β) : IsCyclic Φ := by
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  let f : Φ →* (F ≃+* F) :=
    (SemidirectProduct.rightHom : CFSG.GorensteinWalter.PGammaL2 F →* (F ≃+* F)).comp
      ((gammaOf hodd h3).comp Φ.subtype)
  refine isCyclic_of_injective f ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  refine Subtype.ext (eq_one_of_right_eq_one hodd h3 α β hα hβ hβα x (hfix x x.2).1 (hfix x x.2).2 hx)

end Cyclic

section Rep

variable {F : Type} [Field F] [Finite F]

theorem exists_rep_matrix (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (φ : MulAut SL(2, F)) :
    ∃ G : GL (Fin 2) F, ∀ b : SL(2, F),
      ((φ b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
        (G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map (gammaOf hodd h3 φ).right := by
  obtain ⟨G, hG⟩ := exists_rep hodd h3 φ
  refine ⟨G, fun b => ?_⟩
  have h1 : SpecialLinearGroup.toGL (φ b) * G =
      G * GeneralLinearGroup.map ((gammaOf hodd h3 φ).right : F →+* F) (SpecialLinearGroup.toGL b) := by
    rw [hG b]
    group
  have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1
  simpa using h2

end Rep

section Descent

variable {F : Type} [Field F] [Finite F]

theorem pow_fix {M : Type*} [Group M] (φ : MulAut M) (x : M) (h : φ x = x) (k : ℕ) :
    (φ ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, h]

theorem exists_descent (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (hmod : Nat.card F % 4 = 3)
    (α β : SL(2, F)) (hα : α * α = minusIdentity F) (hβ : β * β = minusIdentity F)
    (hβα : β * α = α * β * minusIdentity F)
    (φ : MulAut SL(2, F)) (hφα : φ α = α) (hφβ : φ β = β) (hφodd : Odd (orderOf φ)) :
    ∃ (P : GL (Fin 2) F) (σ : F ≃+* F),
      (∀ X : SL(2, F), φ (slConjugation F P X) =
        slConjugation F P (SpecialLinearGroup.map (σ : F →+* F) X)) ∧
      α = slConjugation F P (CFSG.GH74.GLS.IVK.L2Torus.w0 F) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card F hodd
  obtain ⟨G, hG⟩ := exists_rep_matrix hodd h3 φ
  set σ : F ≃+* F := (gammaOf hodd h3 φ).right with hσ
  have hsodd : Odd (orderOf σ) :=
    Odd.of_dvd_nat hφodd (orderOf_map_dvd (SemidirectProduct.rightHom.comp (gammaOf hodd h3)) φ)
  have hs0 : 0 < orderOf σ := hsodd.pos
  set s := orderOf σ with hs
  set Gm : Matrix (Fin 2) (Fin 2) F := (G : Matrix (Fin 2) (Fin 2) F) with hGm
  have hσs : σ ^ s = 1 := pow_orderOf_eq_one σ
  obtain ⟨hA, hB, hBA⟩ := matrix_rel_of_anticomm α β hα hβ hβα
  have hcomm : ∀ x : SL(2, F), φ x = x → (x : Matrix (Fin 2) (Fin 2) F) * Mseq σ Gm s =
      Mseq σ Gm s * x := by
    intro x hx
    have := Mseq_conj σ Gm φ hG s x
    rwa [pow_fix φ x hx, hσs, map_one_aut] at this
  obtain ⟨l, hl⟩ := exists_smul_one_of_comm h2 α β hα hβ hβα (Mseq σ Gm s)
    (hcomm α hφα).symm (hcomm β hφβ).symm
  have hD0 : Gm.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero G
  have hdet : ∏ i ∈ Finset.range s, (σ ^ i) Gm.det = l ^ 2 := by
    rw [← det_Mseq, hl, Matrix.det_smul, Matrix.det_one]
    simp
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have : ∏ i ∈ Finset.range s, (σ ^ i) Gm.det ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero (σ ^ i)).2 hD0
    exact this (by simpa using hdet)
  have hσl : σ l = l := by
    have e1 : Mseq σ Gm (s + 1) = Mseq σ Gm s * Gm.map (σ ^ s) := Mseq_succ' σ Gm s
    have e2 : Mseq σ Gm (s + 1) = Gm * (Mseq σ Gm s).map σ := rfl
    rw [e2, hl, hσs, map_one_aut] at e1
    have e3 : (l • (1 : Matrix (Fin 2) (Fin 2) F)).map σ = σ l • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.map_apply]
    rw [e3] at e1
    obtain ⟨i, j, hij⟩ : ∃ i j, Gm i j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hD0
      have : Gm = 0 := by
        ext i j
        exact hcon i j
      rw [this]
      simp
    have e4 := congrFun (congrFun e1 i) j
    simp at e4
    exact e4.resolve_right hij
  obtain ⟨c, hc0, hc⟩ := exists_norm_mul_eq_one σ hsodd Gm.det l hl0 hσl hdet
  set H : Matrix (Fin 2) (Fin 2) F := c • Gm with hH
  have hHrel : ∀ b : SL(2, F), (φ b : Matrix (Fin 2) (Fin 2) F) * H =
      H * (b : Matrix (Fin 2) (Fin 2) F).map σ := by
    intro b
    rw [hH, Matrix.mul_smul, Matrix.smul_mul, hG b]
  have hMH : Mseq σ H s = 1 := by
    rw [hH, Mseq_smul, hl, smul_smul, hc, one_smul]
  have hΦs : (⇑(twistHom σ H))^[s] = id := by
    funext v
    rw [iterate_twist, hMH, hσs]
    simp
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector σ hs0 (twistHom σ H) (twistHom_smul σ H) hΦs
    (fun _ => 1) (by intro h; have := congrFun h 0; simp at this)
  have hαH : (α : Matrix (Fin 2) (Fin 2) F) * H = H * (α : Matrix (Fin 2) (Fin 2) F).map σ := by
    have := hHrel α
    rwa [hφα] at this
  have hu : twistHom σ H ((α : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      (α : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
    rw [twistHom_mulVec σ H _ hαH, hv]
  have hneg : ¬ IsSquare (-1 : F) := by
    have := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨Pm, hdetP, hR1, hR3⟩ := exists_basis_matrix σ H _ v hA hv0 hv hu hneg
  let P : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Pm hdetP
  have hPval : (P : Matrix (Fin 2) (Fin 2) F) = Pm := rfl
  have hPPi : (P : Matrix (Fin 2) (Fin 2) F) * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Units.mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Units.inv_mul P
  refine ⟨P, σ, ?_, ?_⟩
  · intro X
    apply Subtype.ext
    set Y : SL(2, F) := slConjugation F P X with hY
    have hYm : (Y : Matrix (Fin 2) (Fin 2) F) * Pm = Pm * (X : Matrix (Fin 2) (Fin 2) F) := by
      rw [hY, slConjugation_matrix, ← hPval, mul_assoc, mul_assoc, hPiP, mul_one]
    have hmain : ((φ Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Pm =
        Pm * (X : Matrix (Fin 2) (Fin 2) F).map σ := by
      calc ((φ Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Pm
          = ((φ Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (H * Pm.map σ) := by rw [hR1]
        _ = (((φ Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * H) * Pm.map σ := by rw [mul_assoc]
        _ = (H * (Y : Matrix (Fin 2) (Fin 2) F).map σ) * Pm.map σ := by rw [hHrel Y]
        _ = H * ((Y : Matrix (Fin 2) (Fin 2) F) * Pm).map σ := by rw [mul_assoc, map_mul_aut]
        _ = H * (Pm * (X : Matrix (Fin 2) (Fin 2) F)).map σ := by rw [hYm]
        _ = (H * Pm.map σ) * (X : Matrix (Fin 2) (Fin 2) F).map σ := by
          rw [map_mul_aut, ← mul_assoc]
        _ = Pm * (X : Matrix (Fin 2) (Fin 2) F).map σ := by rw [hR1]
    have e1 : ((φ Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (((φ Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Pm) *
          ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← hPval, mul_assoc, hPPi, mul_one]
    rw [e1, hmain, slConjugation_matrix, hPval]
    rfl
  · apply Subtype.ext
    have e1 : (α : Matrix (Fin 2) (Fin 2) F) =
        ((α : Matrix (Fin 2) (Fin 2) F) * Pm) * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← hPval, mul_assoc, hPPi, mul_one]
    have hw0 : ((CFSG.GH74.GLS.IVK.L2Torus.w0 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        !![0, 1; -1, 0] := by
      simp [CFSG.GH74.GLS.IVK.L2Torus.w0]
    rw [e1, hR3, slConjugation_matrix, hPval, hw0]

end Descent

end CFSG.GH74.GLS.SP.Local.SL2Three
